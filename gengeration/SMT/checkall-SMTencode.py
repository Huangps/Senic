import math
import subprocess
import os
from typing import List, Dict, Tuple, Optional


class SpatialRelationAnalyzer:
    """
    空间关系分析器，用于判断点与点之间的相对位置关系
    """

    def __init__(self, temp_dir: str = "./temp_smt"):
        """
        初始化分析器

        Args:
            temp_dir: 临时文件目录
        """
        self.temp_dir = temp_dir
        os.makedirs(temp_dir, exist_ok=True)

    def _generate_smt_code(self, relation_type: str, A_x: float, A_y: float, A_heading: float,
                           B_x: float, B_y: float) -> str:
        """
        生成SMT约束代码

        Args:
            relation_type: 关系类型 ('left', 'right', 'ahead', 'behind')
            A_x, A_y: 参考点A的坐标
            A_heading: 参考点A的朝向角度（度数）
            B_x, B_y: 目标点B的坐标


        Returns:
            SMT代码字符串
        """

        # 根据关系类型设置角度范围
        angle_ranges = {
            'left': (80, 100),
            'right': (260, 280),
            'ahead': (-10, 10),
            'behind': (170, 190)
        }

        min_angle, max_angle = angle_ranges[relation_type]

        smt_code = f"""; SMT约束：检查B是否在A的{relation_type}侧且距离在[range_x, range_x+5]范围内


(set-logic QF_NRA) 
; 定义变量
(declare-const A_x Real)
(declare-const A_y Real)
(declare-const A_heading Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const range_x Real)

; 设置已知值
(assert (= A_x {A_x}))
(assert (= A_y {A_y}))
(assert (= A_heading {A_heading}))
(assert (= B_x {B_x}))
(assert (= B_y {B_y}))


; 计算相对坐标，B相对A
(define-fun delta_x () Real (- B_x A_x))
(define-fun delta_y () Real (- B_y A_y))

; 计算距离
(define-fun distance () Real (sqrt (+ (* delta_x delta_x) (* delta_y delta_y))))

; 计算B相对正X轴的弧度（取值范围为[-pi,pi]）
(define-fun angle_rad_x () Real (atan2 delta_y delta_x))

; 规范化到 [0, 2π) 范围
(define-fun angle_rad_nom () Real
    (let ((raw_angle angle_rad_x))
        (ite (< raw_angle 0.0)
             (+ raw_angle (* 2.0 {math.pi}))
             raw_angle)))

; 计算B相对正y轴的弧度
(define-fun angle_rad_y () Real (- angle_rad_nom (/ {math.pi} 2.0)))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y (/ (* A_heading {math.pi}) 180.0)))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 规范化角度到[0, 360)
 
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta)) 

(define-fun normalized_angle_deg () Real (normalize_angle angle_deg))

; {relation_type}角度范围
(define-fun theta_min () Real (normalize_angle (+ A_heading {min_angle}.0)))
(define-fun theta_max () Real (normalize_angle (+ A_heading {max_angle}.0)))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_min theta_max)
        (and (>= normalized_angle_deg theta_min) (<= normalized_angle_deg theta_max))
        (or (>= normalized_angle_deg theta_min) (<= normalized_angle_deg theta_max))))

; 距离约束
(define-fun range_y () Real (+ range_x 5.0))
(define-fun distance_constraint () Bool
    (and (>= distance range_x) (<= distance range_y)))

; 总约束
(assert (and angle_constraint distance_constraint))

; 检查可满足性
(check-sat)
(get-model)
"""
        return smt_code

    def _write_smt_file(self, smt_code: str, filename: str) -> str:
        """
        写入SMT文件

        Args:
            smt_code: SMT代码
            filename: 文件名

        Returns:
            文件完整路径
        """
        file_path = os.path.join(self.temp_dir, filename)
        with open(file_path, "w") as f:
            f.write(smt_code)
        return file_path

    def _run_smt_solver(self, file_path: str) -> tuple[bool, str]:
        """
        运行SMT求解器

        Args:
            file_path: SMT文件路径

        Returns:
            tuple[bool, str]: (是否成功执行, 结果描述)
            - (True, "sat") 表示约束满足
            - (True, "unsat") 表示约束不满足
            - (False, "error") 表示求解器执行出错
            - (False, "timeout") 表示超时
            - (False, "not_found") 表示求解器未找到
        """
        """
           运行MathSAT求解器
           """
        try:
            result = subprocess.run(
                ["mathsat.exe", file_path],
                capture_output=True,
                text=True,
                timeout=30
            )

            output = result.stdout.strip()
            error_output = result.stderr.strip()

            if error_output or "error" in output.lower():
                print(f"MathSAT Error: {error_output}")
                return (False, "error")

            # MathSAT输出示例：
            # sat
            # (model ...)
            # 或
            # unsat

            if output:
                first_line = output.split('\n')[0].strip().lower()
                if first_line == "sat":
                    return (True, "sat")
                elif first_line == "unsat":
                    return (True, "unsat")

            return (False, "error")

        except subprocess.TimeoutExpired:
            return (False, "timeout")
        except FileNotFoundError:
            return (False, "not_found")
        except Exception as e:
            print(f"Error: {e}")
            return (False, "error")

    def check_spatial_relation(self, relation_type: str, A_point: Dict, B_point: Dict) -> bool:
        """
        检查两点之间的空间关系（range_x需要在SMT文件中设置）

        Args:
            relation_type: 关系类型 ('left', 'right', 'ahead', 'behind')
            A_point: 参考点 {'x': float, 'y': float, 'heading': float, 'id': str}
            B_point: 目标点 {'x': float, 'y': float, 'heading': float, 'id': str}

        Returns:
            是否满足指定关系
        """
        smt_code = self._generate_smt_code(
            relation_type,
            A_point['x'], A_point['y'], A_point['heading'],
            B_point['x'], B_point['y']
        )

        filename = f"{A_point['id']}_to_{B_point['id']}_{relation_type}.smt2"
        file_path = self._write_smt_file(smt_code, filename)

        success, result = self._run_smt_solver(file_path)

        # 只有成功执行且结果为sat时才返回True
        if success and result == "sat":
            return True
        elif not success:
            # 记录错误日志
            print(f"Warning: SMT solver failed for {filename}: {result}")

        return False
    def get_all_relations(self, A_point: Dict, B_point: Dict) -> List[str]:
        """
        获取两点之间的所有可能关系

        Args:
            A_point: 参考点
            B_point: 目标点

        Returns:
            满足的关系列表
        """
        relations = []
        relation_types = ['left', 'right', 'ahead', 'behind']

        for rel_type in relation_types:
            if self.check_spatial_relation(rel_type, A_point, B_point):
                relations.append(rel_type)

        return relations


class PointSequenceAnalyzer:
    """
    点序列分析器，按顺序分析点之间的关系
    """

    def __init__(self, temp_dir: str = "./temp_smt"):
        """
        初始化分析器

        Args:
            temp_dir: 临时文件目录
        """
        self.spatial_analyzer = SpatialRelationAnalyzer(temp_dir)
        self.results = []

    def find_closest_reference(self, current_point: Dict, reference_points: List[Dict]) -> Dict:
        """
        找到最近的参考点

        Args:
            current_point: 当前点
            reference_points: 参考点列表

        Returns:
            最近的参考点
        """
        if len(reference_points) == 1:
            return reference_points[0]

        closest_point = min(reference_points,
                            key=lambda p: math.sqrt((p["x"] - current_point["x"]) ** 2 +
                                                    (p["y"] - current_point["y"]) ** 2))
        return closest_point

    def analyze_point_relations(self, current_point: Dict, reference_points: List[Dict],
                                use_closest_only: bool = True) -> Optional[str]:
        """
        分析当前点与参考点的关系
        """
        if use_closest_only:
            # 先检查最近的参考点
            ref_point = self.find_closest_reference(current_point, reference_points)
            relations = self.spatial_analyzer.get_all_relations(
                ref_point, current_point
            )

            if relations:
                relation_str = "/".join(relations).upper()
                return f"{current_point['id']} is {relation_str} of {ref_point['id']}"
            else:
                # ❌ 修正：如果最近点没有关系，检查其他参考点
                other_references = [p for p in reference_points if p['id'] != ref_point['id']]
                if other_references:
                    for other_ref in other_references:
                        relations = self.spatial_analyzer.get_all_relations(
                            other_ref, current_point
                        )
                        if relations:
                            relation_str = "/".join(relations).upper()
                            return f"{current_point['id']} is {relation_str} of {other_ref['id']}"
        else:
            # 分析所有参考点
            for ref_point in reference_points:
                relations = self.spatial_analyzer.get_all_relations(
                    ref_point, current_point
                )

                if relations:
                    relation_str = "/".join(relations).upper()
                    return f"{current_point['id']} is {relation_str} of {ref_point['id']}"

        return f"{current_point['id']} has no defined spatial relation with reference points"

    def analyze_sequence(self, points: List[Dict],
                         use_closest_only: bool = True) -> List[str]:
        """
        分析点序列

        Args:
            points: 点列表，第一个点应该是ego
            use_closest_only: 是否只使用最近的参考点

        Returns:
            分析结果列表
        """
        if len(points) < 2:
            return ["Need at least ego and one point to analyze"]

        results = []

        # 从第二个点开始分析（第一个是ego）
        for i in range(1, len(points)):
            current_point = points[i]
            # 参考点包括ego和前面的所有点
            reference_points = points[:i]

            relation = self.analyze_point_relations(
                current_point, reference_points, use_closest_only
            )

            if relation:
                results.append(relation)

        return results

    def print_results(self, results: List[str]):
        """
        打印分析结果

        Args:
            results: 结果列表
        """
        print("=== Spatial Relation Analysis Results ===")
        for i, result in enumerate(results, 1):
            print(f"{i}. {result}")


# 使用示例
def main():
    """
    主函数示例
    """
    # 定义点数据
    points = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 90.0},
        {"id": "P1", "x": 5.0, "y": 0.0, "heading": 90.0},
        {"id": "P2", "x": 10.0, "y": -2.0, "heading": 90.0},
        {"id": "P3", "x": 8.0, "y": 3.0, "heading": 90.0},
        {"id": "P4", "x": 15.0, "y": 0.0, "heading": 90.0}
    ]

    # 创建分析器
    analyzer = PointSequenceAnalyzer(temp_dir="./temp_smt")

    # 分析序列
    results = analyzer.analyze_sequence(points, use_closest_only=True)

    # 打印结果
    analyzer.print_results(results)

    # 清理临时文件（可选）
    # import shutil
    # shutil.rmtree("./temp_smt")


if __name__ == "__main__":
    main()
