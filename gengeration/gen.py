import re
from typing import List, Dict, Callable, Optional, Tuple

def dynamic_position_generator(state):
    """根据已填充的实体动态生成位置搜索空间（新增选项前置）"""
    template = state['partial_template']
    entities = re.findall(r'(\w+)\s*=\s*(Car|Pedestrian)', template)

    # 基础位置选项（保持原样，放在最后）
    base_options = ["on road", "on intersection"]

    # 关系类型选项容器（ahead/left/right/behind）
    relation_options = []

    # 偏移选项容器（at...）
    offset_options = []

    # 检查每个实体是否已填充位置
    for entity_name, entity_type in entities:
        # 构造位置占位符key
        if entity_name == "ego":
            pos_key = "position1"
        elif entity_name.startswith("otherCar"):
            car_num = int(entity_name[8:])
            pos_key = f"position{car_num + 1}"
        elif entity_name.startswith("human"):
            human_num = int(entity_name[5:])
            pos_key = f"position{len([e for e, _ in entities if e.startswith('otherCar')]) + human_num + 1}"

        # 如果该实体的位置已填充
        if pos_key in state['filled_values']:
            # 在relation_options最前面添加关系类型选项（使用insert保持顺序）
            relation_options[0:0] = [
                f"ahead of {entity_name} by Range(?,?)",
                f"left of {entity_name} by Range(?,?)",
                f"right of {entity_name} by Range(?,?)",
                f"behind {entity_name} by Range(?,?)"
            ]

            # 在offset_options最前面添加偏移选项
            offset_options.insert(0, f"at {entity_name} offset by(Range(?,?),Range(?,?))")

    # 按指定顺序组合结果
    return relation_options + offset_options + base_options

def dynamic_heading_generator(state):
    """根据已填充的实体动态生成朝向搜索空间（新增选项前置）"""
    # 解析模板获取已定义的实体
    template = state['partial_template']
    entities = re.findall(r'(\w+)\s*=\s*(Car|Pedestrian)', template)

    # 基础朝向选项（保持在最后）
    base_headings = ["Range(?,?) relative to roadDirection"]

    # 相对朝向选项容器（新增选项将放在这里的最前面）
    relative_headings = []

    # 检查每个实体是否已填充朝向
    for entity_name, entity_type in entities:
        # 构造朝向占位符key
        if entity_name == "ego":
            heading_key = "heading1"
        elif entity_name.startswith("otherCar"):
            car_num = int(entity_name[8:])
            heading_key = f"heading{car_num + 1}"
        elif entity_name.startswith("human"):
            human_num = int(entity_name[5:])
            heading_key = f"heading{len([e for e, _ in entities if e.startswith('otherCar')]) + human_num + 1}"

        # 如果该实体的朝向已填充
        if heading_key in state['filled_values']:
            # 在列表最前面插入新的相对朝向选项
            relative_headings.insert(0, f"Range(?,?) deg relative to {entity_name}.heading")

    # 组合结果：相对朝向（后来居上） + 基础朝向
    return relative_headings + base_headings

def simple_validator(filled_values, partial_template):
    """简单的验证函数，总是返回True"""
    return True


class SceneSketchFiller:
    def __init__(self, num_other_cars: int = 0, num_pedestrians: int = 0):
        """
        初始化场景填充器

        参数:
            num_other_cars: 其他汽车数量 (默认0)
            num_pedestrians: 行人数量 (默认0)
        """
        self.num_other_cars = num_other_cars
        self.num_pedestrians = num_pedestrians
        self.template = self.generate_sketch()
        self.placeholder_map = self.parse_placeholders()
        self.filled_values = {}
        self.filled_history = []

        # 默认验证函数 - 总是返回成功
        self.validation_func = lambda filled, partial: True

        # 搜索空间生成器
        self.position_space_generator = None
        self.heading_space_generator = None
        self.current_position_space = []
        self.current_heading_space = []

    def set_validation_func(self, func: Callable):
        """设置自定义验证函数"""
        self.validation_func = func

    def set_space_generators(self,
                             position_gen: Callable[[Dict], List[str]],
                             heading_gen: Callable[[Dict], List[str]]):
        """
        设置动态生成搜索空间的函数

        参数:
            position_gen: 接收当前状态，返回可用位置列表的函数
            heading_gen: 接收当前状态，返回可用朝向列表的函数
        """
        self.position_space_generator = position_gen
        self.heading_space_generator = heading_gen

    def generate_sketch(self) -> str:
        """生成带有占位符的场景草图"""
        sketch_lines = [f"ego = Car <?_position1>, facing <?_heading1>"]

        # 添加其他汽车
        for i in range(1, self.num_other_cars + 1):
            sketch_lines.append(f"otherCar{i} = Car <?_position{i + 1}>, facing <?_heading{i + 1}>")

        # 添加行人
        for i in range(1, self.num_pedestrians + 1):
            sketch_lines.append(
                f"human{i} = Pedestrian <?_position{self.num_other_cars + i + 1}>, facing <?_heading{self.num_other_cars + i + 1}>")

        return "\n".join(sketch_lines)

    def parse_placeholders(self) -> Dict[str, dict]:
        """解析所有占位符及其类型"""
        placeholders = re.findall(r'<\?_([a-zA-Z]+)(\d+)>', self.template)
        mapping = {}

        for placeholder in set(placeholders):
            ptype, pindex = placeholder
            key = f"{ptype}{pindex}"
            mapping[key] = {
                "full_tag": f"<?_{ptype}{pindex}>",
                "type": ptype,
                "index": int(pindex),
                "value": None,
                "filled": False
            }
        return mapping

    def get_placeholder_order(self) -> List[str]:
        """获取按对象顺序的占位符填充顺序 (positionX → headingX → positionY → headingY)"""
        # 首先获取所有占位符键
        all_keys = list(self.placeholder_map.keys())

        # 按索引排序
        all_keys.sort(key=lambda x: self.placeholder_map[x]["index"])

        # 创建新的顺序：每个对象的position和heading连续
        ordered_list = []
        for key in all_keys:
            # 如果是position占位符，则添加它和对应的heading
            if key.startswith("position"):
                obj_index = key[8:]  # 提取索引部分
                ordered_list.append(f"position{obj_index}")
                ordered_list.append(f"heading{obj_index}")

        return ordered_list

    def get_current_state(self) -> Dict:
        """获取当前填充状态"""
        return {
            "filled_values": self.filled_values.copy(),
            "next_placeholder": self.get_next_placeholder(),
            "partial_template": self.get_partial_template(),
            "filled_history": self.filled_history.copy()
        }

    def get_next_placeholder(self) -> Optional[str]:
        """获取下一个待填充的占位符"""
        order = self.get_placeholder_order()
        for placeholder_key in order:
            if not self.placeholder_map[placeholder_key]["filled"]:
                return placeholder_key
        return None

    def get_partial_template(self) -> str:
        """获取当前部分填充的模板"""
        current_template = self.template
        for ph_key, ph_info in self.placeholder_map.items():
            if ph_info["filled"] and ph_info["value"] is not None:
                current_template = current_template.replace(ph_info["full_tag"], ph_info["value"])
        return current_template

    def update_search_spaces(self):
        """根据当前状态更新搜索空间"""
        current_state = self.get_current_state()

        if self.position_space_generator:
            self.current_position_space = self.position_space_generator(current_state)

        if self.heading_space_generator:
            self.current_heading_space = self.heading_space_generator(current_state)

    def fill_placeholder(self, placeholder_key: str, value: str) -> bool:
        """填充指定占位符并验证结果"""
        if placeholder_key not in self.placeholder_map:
            raise ValueError(f"无效占位符: {placeholder_key}")

        ph_info = self.placeholder_map[placeholder_key]

        # 创建部分填充状态的副本用于验证
        partial_state = self.get_current_state()
        partial_state["filled_values"][placeholder_key] = value

        # 验证
        if not self.validation_func(partial_state["filled_values"], partial_state["partial_template"]):
            return False

        # 验证通过，执行填充
        ph_info["value"] = value
        ph_info["filled"] = True
        self.filled_values[placeholder_key] = value
        self.filled_history.append({
            "placeholder": placeholder_key,
            "value": value,
            "partial_template": partial_state["partial_template"]
        })

        # 填充成功后更新搜索空间
        self.update_search_spaces()

        return True

    def backtrack(self) -> bool:
        """回溯到上一个占位符并尝试下一个值"""
        """
        if not self.filled_history:
            return False  # 没有历史记录，无法回溯

        # 获取最近填充的占位符
        last_fill = self.filled_history.pop()
        placeholder_key = last_fill["placeholder"]
        last_value = last_fill["value"]

        # 重置当前占位符状态
        self.placeholder_map[placeholder_key]["value"] = None
        self.placeholder_map[placeholder_key]["filled"] = False
        if placeholder_key in self.filled_values:
            del self.filled_values[placeholder_key]

        # 更新搜索空间（回溯后状态已改变）
        self.update_search_spaces()

        # 获取正确的搜索空间
        ph_type = "position" if placeholder_key.startswith("position") else "heading"
        space = self.current_position_space if ph_type == "position" else self.current_heading_space

        # 尝试填充新值
        if last_value in space:
            current_index = space.index(last_value) + 1
        else:
            current_index = 0

        if current_index < len(space):
            new_value = space[current_index]
            return self.fill_placeholder(placeholder_key, new_value)

        # 当前占位符的值已尝试完，继续回溯
        """
        return self.backtrack()

    def step_by_step_fill(self) -> bool:
        """按对象顺序逐个填充占位符并验证中间结果"""
        # 初始更新搜索空间
        self.update_search_spaces()

        # 获取正确的填充顺序
        placeholder_order = self.get_placeholder_order()

        current_index = 0
        while current_index < len(placeholder_order):
            ph_key = placeholder_order[current_index]
            ph_type = "position" if ph_key.startswith("position") else "heading"
            space = self.current_position_space if ph_type == "position" else self.current_heading_space

            if not space:
                print(f"警告: {ph_key} 的搜索空间为空，无法继续填充")
                return False

            filled = False

            # 尝试填充当前占位符
            for value in space:
                # 尝试填充当前值
                success = self.fill_placeholder(ph_key, value)

                if success:
                    # 验证通过，继续下一个占位符
                    filled = True
                    print(f"填充 {ph_key} 成功! 值: {value}")
                    print("当前场景状态:")
                    print(self.get_partial_template())
                    print("-" * 40)
                    current_index += 1  # 移动到下一个占位符
                    break
                else:
                    # 验证失败，尝试下一个值
                    print(f"尝试值 {value} 未能通过验证，尝试下一个...")
            """
            if not filled:
                # 回溯尝试
                print(f"所有值尝试失败，开始回溯...")
                if self.backtrack():
                    print("回溯成功，继续填充当前占位符")
                    # 回溯后重新获取当前填充位置
                    current_index = self.get_current_index_in_order()
                else:
                    print("回溯失败，没有可行解")
                    return False
            """
        return True

    def get_current_index_in_order(self) -> int:
        """获取当前填充进度在顺序中的位置"""
        order = self.get_placeholder_order()
        for i, ph_key in enumerate(order):
            if not self.placeholder_map[ph_key]["filled"]:
                return i
        return len(order)


# 示例使用
if __name__ == "__main__":
    # 1. 创建场景草图
    filler = SceneSketchFiller(num_other_cars=1, num_pedestrians=1)
    print("初始场景sketch:")
    print(filler.template)

    # 2. 设置动态搜索空间生成器和验证函数
    filler.set_space_generators(dynamic_position_generator, dynamic_heading_generator)
    filler.set_validation_func(simple_validator)

    # 3. 执行按顺序填充
    print("\n开始按对象顺序填充并验证中间结果...")
    if filler.step_by_step_fill():
        print("\n所有填充完成! 最终结果:")
        print(filler.get_partial_template(), "\n")
        print("heading:", filler.current_heading_space)
        print("position:", filler.current_position_space)
    else:
        print("填充失败，无法找到有效组合")