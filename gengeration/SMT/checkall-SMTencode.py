import math
import subprocess
import os
from typing import List, Dict, Tuple, Optional


class OrientationRelationAnalyzer:
    """
    基于SMT的朝向关系分析器
    """

    def __init__(self, temp_dir: str = "./temp_smt"):
        self.temp_dir = temp_dir
        os.makedirs(temp_dir, exist_ok=True)
        self.dreal_path = "/opt/dreal/4.21.06.2/bin/dreal"  # 根据你的实际路径调整

    def _generate_toward_smt(self, A_x: float, A_y: float, B_x: float, B_y: float, B_heading: float) -> str:
        """
        生成B朝向A的SMT约束
        """
        smt_code = f"""; SMT约束：检查B是否朝向A（角度容差±10度）
(set-logic QF_NRA)

; 定义变量
(declare-const A_x Real)
(declare-const A_y Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const B_heading Real)  ; B的朝向角度

; 设置已知值
(assert (= A_x {A_x}))
(assert (= A_y {A_y}))
(assert (= B_x {B_x}))
(assert (= B_y {B_y}))
(assert (= B_heading {B_heading}))

; 计算从B到A的方位角（相对于正Y轴，逆时针为正）
(define-fun delta_x () Real (- A_x B_x))
(define-fun delta_y () Real (- A_y B_y))

; 计算相对于正X轴的角度
(define-fun angle_rad_x () Real (atan2 delta_y delta_x))

; 转换为相对于正Y轴的角度（正Y轴=0度，逆时针增加）
(define-fun bearing_angle_rad () Real (- angle_rad_x (/ {math.pi} 2.0) ))
(define-fun bearing_angle_deg () Real (* bearing_angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun normalized_bearing () Real (normalize_angle bearing_angle_deg))

; 计算角度差
(define-fun angle_diff_raw () Real (- normalized_bearing B_heading))
(define-fun angle_diff () Real (normalize_angle angle_diff_raw))

; 处理跨越0度的情况，取最小角度差
(define-fun min_angle_diff () Real
    (ite (> angle_diff 180.0)
         (- 360.0 angle_diff)
         angle_diff))

; 朝向约束（±10度容差）
(define-fun toward_constraint () Bool (<= min_angle_diff 10.0))

; 总约束
(assert toward_constraint)

; 检查可满足性
(check-sat)
(get-model)
"""
        return smt_code

    def _generate_away_smt(self, A_x: float, A_y: float, B_x: float, B_y: float, B_heading: float) -> str:
        """
        生成B背向A的SMT约束
        """
        smt_code = f"""; SMT约束：检查B是否背向A（角度容差±10度）
(set-logic QF_NRA)

; 定义变量
(declare-const A_x Real)
(declare-const A_y Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const B_heading Real)

; 设置已知值
(assert (= A_x {A_x}))
(assert (= A_y {A_y}))
(assert (= B_x {B_x}))
(assert (= B_y {B_y}))
(assert (= B_heading {B_heading}))

; 计算从A到B的方位角（B背向A的方向）
(define-fun delta_x () Real (- B_x A_x))
(define-fun delta_y () Real (- B_y A_y))

; 计算相对于正X轴的角度
(define-fun angle_rad_x () Real (atan2 delta_y delta_x))

; 转换为相对于正Y轴的角度
(define-fun bearing_angle_rad () Real (- angle_rad_x (/ {math.pi} 2.0) ))
(define-fun bearing_angle_deg () Real (* bearing_angle_rad (/ 180.0 {math.pi})))

; 角度规范化
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun normalized_bearing () Real (normalize_angle bearing_angle_deg))

; 计算角度差
(define-fun angle_diff_raw () Real (- normalized_bearing B_heading))
(define-fun angle_diff () Real (normalize_angle angle_diff_raw))

; 取最小角度差
(define-fun min_angle_diff () Real
    (ite (> angle_diff 180.0)
         (- 360.0 angle_diff)
         angle_diff))

; 背向约束（±10度容差）
(define-fun away_constraint () Bool (<= min_angle_diff 10.0))

; 总约束
(assert away_constraint)

; 检查可满足性
(check-sat)
(get-model)
"""
        return smt_code

    def _generate_relative_heading_smt(self, A_heading: float, B_heading: float,
                                    tolerance: float = 10.0) -> str:
        """
        生成SMT约束：求解一个y，使得B相对A的朝向落在[y, y+tolerance]区间内（y是变量）
        """
        smt_code = f"""; SMT约束：求解y，使得相对朝向 ∈ [y, y+{tolerance}]
(set-logic QF_NRA)

; 定义变量
(declare-const A_heading Real)
(declare-const B_heading Real)
(declare-const y Real) 

; 设置已知值
(assert (= A_heading {A_heading}))
(assert (= B_heading {B_heading}))

; 计算相对朝向
(define-fun relative_heading () Real (- B_heading A_heading))

        
; 角度规范化到[0, 360)
(define-fun normalize_0_360 ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))
        
        

(define-fun normalized_relative () Real (normalize_0_360  relative_heading))

; 约束：normalized_relative ∈ [y, y + {tolerance}]
(assert (>= normalized_relative y))
(assert (<= normalized_relative (+ y {tolerance})))

; 约束 y ∈ [0, 360)
(assert (>= y 0.0))
(assert (< y 360.0))

; 求解y
(check-sat)
(get-value (y))

; 检查可满足性
(check-sat)
(get-model)
"""
        return smt_code


    def check_toward_relation(self, A_point: Dict, B_point: Dict) -> bool:
        """
        检查B是否朝向A
        """
        smt_code = self._generate_toward_smt(
            A_point['x'], A_point['y'],
            B_point['x'], B_point['y'],
            B_point['heading']
        )

        filename = f"{B_point['id']}_toward_{A_point['id']}.smt2"
        file_path = self._write_smt_file(smt_code, filename)

        success, result = self._run_smt_solver(file_path)
        return success and result == "sat"

    def check_away_relation(self, A_point: Dict, B_point: Dict) -> bool:
        """
        检查B是否背向A
        """
        smt_code = self._generate_away_smt(
            A_point['x'], A_point['y'],
            B_point['x'], B_point['y'],
            B_point['heading']
        )

        filename = f"{B_point['id']}_away_{A_point['id']}.smt2"
        file_path = self._write_smt_file(smt_code, filename)

        success, result = self._run_smt_solver(file_path)
        return success and result == "sat"

    def get_relative_heading_relation(self, A_point: Dict, B_point: Dict,
                                         tolerance: float = 10.0) -> bool:
        """
        生成SMT约束：求解一个y，使得B相对A的朝向落在[y, y+tolerance]区间内（y是变量）
        """
        smt_code = self._generate_relative_heading_smt(
            A_point['heading'], B_point['heading'],tolerance
        )

        filename = f"{B_point['id']}_facing_relative_to_{A_point['id']}.smt2"
        file_path = self._write_smt_file(smt_code, filename)

        success, result = self._run_smt_solver(file_path)
        if not success or "unsat" in result:
            return None

        # 解析 (get-value (y)) 的输出，例如: ((y 37.5))
        try:
            if "(y" in result:
                start = result.find("(y") + len("(y")
                end = result.find(")", start)
                value_str = result[start:end].strip()
                y_value = float(value_str)
                # 确保 y ∈ [0, 360)
                y_value = y_value % 360.0
                if y_value < 0:
                    y_value += 360.0
                return y_value
        except Exception as e:
            print(f"解析SMT结果失败: {e}")
            return None

        return None

    def get_orientation_relation(self, A_point: Dict, B_point: Dict) -> str:
        """
        获取两点间的朝向关系
        """
        # 优先检查toward关系
        if self.check_toward_relation(A_point, B_point):
            return "toward"

        # 检查away关系
        elif self.check_away_relation(A_point, B_point):
            return "away from"

        # 检查相对朝向关系
        else:
            y_value = self.get_relative_heading_relation(A_point, B_point, tolerance=10.0)
            if y_value is not None:
                return f"relative_heading_{y_value:.6g}"

        return "none"

    def _write_smt_file(self, smt_code: str, filename: str) -> str:
        file_path = os.path.join(self.temp_dir, filename)
        with open(file_path, "w") as f:
            f.write(smt_code)
        return file_path

    def _run_smt_solver(self, file_path: str) -> tuple[bool, str]:
        try:
            result = subprocess.run(
                [self.dreal_path, file_path],
                capture_output=True,
                text=True
            )

            output = result.stdout.strip()

            # 解析输出
            if output:
                lines = output.split('\n')
                for line in lines:
                    line = line.strip().lower()
                    if line in ["sat", "unsat"] or line.startswith("delta-sat"):
                        if line == "unsat":
                            return (True, "unsat")
                        else:
                            return (True, "sat")

            # 错误处理
            error_output = result.stderr.strip()
            if error_output and "error" in error_output.lower() and "model is not available" not in error_output.lower():
                print(f"dReal Error: {error_output}")
                return (False, "error")

            return (False, "unknown")

        except Exception as e:
            print(f"Solver Error: {e}")
            return (False, "error")



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

    def _generate_relation_smt_code(self, A_x: float, A_y: float, A_heading: float,
                                    B_x: float, B_y: float) -> str:
        """
        生成SMT约束：求解x, y，使得B落在A的局部坐标系下 [x, x+5] × [y, y+5] 区域内
        - x: 横向（左负右正，基于A朝向）
        - y: 纵向（前正后负，基于A朝向）
        """
        smt_code = f"""; SMT约束：求解x, y，使得B在A的局部坐标系下落在 [x, x+5] × [y, y+5] 区域内
    (set-logic QF_NRA)

    ; 定义变量
    (declare-const A_x Real)
    (declare-const A_y Real)
    (declare-const A_heading Real)
    (declare-const B_x Real)
    (declare-const B_y Real)
    (declare-const x Int)   ; ← 横向偏移（左负右正）
    (declare-const y Int)   ; ← 纵向偏移（前正后负）

    ; 设置已知值
    (assert (= A_x {A_x}))
    (assert (= A_y {A_y}))
    (assert (= A_heading {A_heading}))
    (assert (= B_x {B_x}))
    (assert (= B_y {B_y}))

    ; 计算全局坐标系下B相对A的偏移
    (define-fun delta_x_global () Real (- B_x A_x))
    (define-fun delta_y_global () Real (- B_y A_y))

    ; 将A的朝向转换为弧度
    (define-fun heading_rad () Real (* A_heading (/ {math.pi} 180.0)))

    ;旋转矩阵：将全局偏移旋转到A的局部坐标系（A朝向为局部Y轴正方向）

    (define-fun local_x () Real
        (+ (* (- (sin heading_rad)) delta_y_global)
           (* (cos heading_rad) delta_x_global)))
    
    (define-fun local_y () Real
        (+ (* (sin heading_rad) delta_x_global)
           (* (cos heading_rad) delta_y_global)))

    ; 约束：B在局部坐标系下落在 [x, x+5] × [y, y+5]
    (assert (>= local_x x))
    (assert (<= local_x (+ x 5.0)))
    (assert (>= local_y y))
    (assert (<= local_y (+ y 5.0)))


    ; 求解x, y
    (check-sat)
    (get-value (x y))
    """
        return smt_code

    def _generate_NSWE_relation_smt_code(self, relation_type: str, A_x: float, A_y: float, A_heading: float,
                           B_x: float, B_y: float) -> str:
        """
        生成B相对A的前后左右相对关系SMT约束代码

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
(declare-const range_x Int)

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

; 计算B相对正Y轴的角度（弧度
; 坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ {math.pi} 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle_deg ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun normalized_angle () Real (normalize_angle_deg angle_deg_raw))

; {relation_type}角度范围
(define-fun theta_min () Real (normalize_angle_deg (+ A_heading {min_angle}.0)))
(define-fun theta_max () Real (normalize_angle_deg (+ A_heading {max_angle}.0)))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_min theta_max)
        (and (>= normalized_angle theta_min) (<= normalized_angle theta_max))
        (or (>= normalized_angle theta_min) (<= normalized_angle theta_max))))

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

    def _run_smt_solver_NSWE_x(self, file_path: str) -> tuple[bool, str, str]:
        """
        运行dreal求解器, 获取前后左右相对位置 以及 x（距离区间[x,x+5]）
        """
        try:
            result = subprocess.run(
                ["/opt/dreal/4.21.06.2/bin/dreal", file_path],
                capture_output=True,
                text=True
            )

            output = result.stdout.strip().lower()

            # 按行解析，确保精确匹配
            lines = output.split('\n')
            for line in lines:
                line = line.strip().lower()
                # 精确匹配
                if line in ["sat", "unsat"] or line.startswith("delta-sat"):
                    if line == "unsat":
                        return (True, "unsat" ,"unsat" )
                    else:
                        return (True, "sat" ,output)

            # 错误处理
            error_output = result.stderr.strip()
            if error_output:
                if "error" in error_output.lower() and "model is not available" not in error_output.lower():
                    print(f"dReal Error: {error_output}")
                    return (False, "error", "error")

            return (False, "unknown", "unknown")

        except Exception as e:
            print(f"Unexpected Error: {e}")
            return (False, "error", "error")
    def _run_smt_solver_numerical_xy(self, file_path: str) -> tuple[bool, str, str]:
        """
        运行dreal求解器, 获取相对位置关系数值
        """
        try:
            result = subprocess.run(
                ["/opt/dreal/4.21.06.2/bin/dreal", file_path],
                capture_output=True,
                text=True
            )

            output = result.stdout.strip().lower()

            # 按行解析，确保精确匹配
            lines = output.split('\n')
            for line in lines:
                line = line.strip().lower()
                # 精确匹配
                if line in ["sat", "unsat"] or line.startswith("delta-sat"):
                    if line == "unsat":
                        return (True, "unsat","unsat")
                    else:
                        return (True, "sat", output)

            # 错误处理
            error_output = result.stderr.strip()
            if error_output:
                if "error" in error_output.lower() and "model is not available" not in error_output.lower():
                    print(f"dReal Error: {error_output}")
                    return (False, "error","error")

            return (False, "unknown", "unknown")

        except Exception as e:
            print(f"Unexpected Error: {e}")
            return (False, "error", "error")

    def check_NSWE_relation(self, relation_type: str, A_point: Dict, B_point: Dict) -> tuple[bool, str]:
        """
        检查两点之间的空间关系

        Args:
            relation_type: 关系类型 ('left', 'right', 'ahead', 'behind')
            A_point: 参考点 {'x': float, 'y': float, 'heading': float, 'id': str}
            B_point: 目标点 {'x': float, 'y': float, 'heading': float, 'id': str}

        Returns:
            是否满足指定关系
        """
        smt_code = self._generate_NSWE_relation_smt_code(
            relation_type,
            A_point['x'], A_point['y'], A_point['heading'],
            B_point['x'], B_point['y']
        )

        filename = f"{B_point['id']}__NSWE_relative_to_{A_point['id']}_{relation_type}.smt2"
        file_path = self._write_smt_file(smt_code, filename)

        success, result ,output = self._run_smt_solver_NSWE_x(file_path)

        x_str =''
        if "range_x () int " in output:
            start_x = output.find("range_x () int ") + len("range_x () int ")
            end_x = output.find(")", start_x)
            x_str = output[start_x:end_x].strip()



        print(f"DEBUG: {filename} -> success={success}, result={result}")  # 调试信息

        # 只有成功执行且结果为sat时才返回True
        if success and result == "sat":
            return (True,x_str)
        elif not success:
            # 记录错误日志
            print(f"Warning: SMT solver failed for {filename}: {result}")

        return (False,x_str)
    def get_NSWE_relations(self, A_point: Dict, B_point: Dict) -> tuple[List[str], str] :
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
            bool_,range_x = self.check_NSWE_relation(rel_type, A_point, B_point)
            if bool_:
                relations.append(rel_type)
                return (relations,range_x)  #立即返回

        return (relations,range_x)

    def get_numerical_relationship(self, A_point: Dict, B_point: Dict) -> Optional[Tuple[str, str]]:
        smt_code = self._generate_relation_smt_code(
            A_point['x'], A_point['y'], A_point['heading'],
            B_point['x'], B_point['y']
        )
        filename = f"{B_point['id']}_local_xy_{A_point['id']}.smt2"
        file_path = self._write_smt_file(smt_code, filename)
        success, result, output = self._run_smt_solver_numerical_xy(file_path)

        if not success or "unsat" in result:
            return None

        try:
            # 解析 ((x ...) (y ...))
            if "(x" in output and "(y" in output:
                try:
                    # 提取 x
                    start_x = output.find("(x") + len("(x")
                    end_x = output.find(")", start_x)
                    x_str = output[start_x:end_x].strip()

                    # 处理 Lisp 风格负数: "(- 10" → 去掉 '('，保留 "- 10" → float 能处理
                    if x_str.startswith('('):
                        x_str = x_str[1:].strip()  # 去掉开头的 '('
                    x_val = x_str

                    # 提取 y
                    start_y = output.find("(y") + len("(y")
                    end_y = output.find(")", start_y)
                    y_str = output[start_y:end_y].strip()

                    if y_str.startswith('('):
                        y_str = y_str[1:].strip()
                    y_val = y_str

                    return x_val, y_val

                except Exception as e:
                    print(f"解析 x/y 失败: {e}")
                    return None

                return x_val, y_val
        except Exception as e:
            print(f"解析失败: {e}")
            return None

        return None


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
        self.orientation_analyzer = OrientationRelationAnalyzer(temp_dir)
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
        分析当前点与参考点的关系：
        1. 优先检查最近参考点是否有 NSWE 关系 → 有则返回；
        2. 若无，检查其他参考点是否有 NSWE 关系 → 有则返回；
        3. 若全无，计算最近参考点的数值相对位置关系；
        4. 若仍无，返回无关系语句。
        """
        if not reference_points:
            return f"{current_point['id']} has no reference point"

        # 1. 找最近点
        closest_ref = self.find_closest_reference(current_point, reference_points)

        # 2. 检查最近点是否有 NSWE 关系
        relations, range_x = self.spatial_analyzer.get_NSWE_relations(closest_ref, current_point)
        if relations:
            relation_str = "/".join(relations).upper()
            if relation_str == "behind":
                return f"{current_point['id']} is {relation_str}  {closest_ref['id']} by Range[{range_x},{range_x}+5]"
            return f"{current_point['id']} is {relation_str} of {closest_ref['id']} by Range[{range_x},{range_x}+5]"

        # 3. 检查其他点是否有 NSWE 关系
        other_refs = [p for p in reference_points if p['id'] != closest_ref['id']]
        for ref in other_refs:
            relations, range_x = self.spatial_analyzer.get_NSWE_relations(ref, current_point)
            if relations:
                relation_str = "/".join(relations).upper()
                return f"{current_point['id']} is {relation_str} of {closest_ref['id']} by Range[{range_x},{range_x}+5]"

        # 4. 所有NSWE关系都无 → 用最近点计算数值关系
        xy = self.spatial_analyzer.get_numerical_relationship(closest_ref, current_point)
        if xy is not None:
            x, y = xy
            return f"{current_point['id']} is at range x[{x}, {x + ' +2'}] y[{y:}, {y + ' +2'}] of {closest_ref['id']}"

        # 5. 彻底无关系
        return f"{current_point['id']} has no defined spatial relation with reference points"

        # if use_closest_only:
        #     # 先检查最近的参考点
        #     ref_point = self.find_closest_reference(current_point, reference_points)
        #     relations = self.spatial_analyzer.get_NSWE_relations(
        #         ref_point, current_point
        #     )
        #
        #     if relations:
        #         relation_str = "/".join(relations).upper()
        #         return f"{current_point['id']} is {relation_str} of {ref_point['id']}"
        #     else:
        #         # ❌ 修正：如果最近点没有关系，检查其他参考点
        #         other_references = [p for p in reference_points if p['id'] != ref_point['id']]
        #         if other_references:
        #             for other_ref in other_references:
        #                 relations = self.spatial_analyzer.get_NSWE_relations(
        #                     other_ref, current_point
        #                 )
        #                 if relations:
        #                     relation_str = "/".join(relations).upper()
        #                     return f"{current_point['id']} is {relation_str} of {other_ref['id']}"
        #
        # else:
        #     # 分析所有参考点
        #     for ref_point in reference_points:
        #         relations = self.spatial_analyzer.get_NSWE_relations(
        #             ref_point, current_point
        #         )
        #
        #         if relations:
        #             relation_str = "/".join(relations).upper()
        #             return f"{current_point['id']} is {relation_str} of {ref_point['id']}"
        #
        # return f"{current_point['id']} has no defined spatial relation with reference points"

    def analyze_orientation_relations(self, current_point: Dict, reference_points: List[Dict],
                                use_closest_only: bool = True) -> List[str]:
        """
        分析点序列的朝向关系（支持优先最近点策略）
        """
        results = []


        if use_closest_only:
            # 1. 先找最近的参考点
            ref_point = self.find_closest_reference(current_point, reference_points)
            relation = self.orientation_analyzer.get_orientation_relation(ref_point, current_point)

            if relation != "none":
                self._format_orientation_result(relation, current_point, ref_point, results)
                found = True
            else:
                # 2. 最近点无关系 → 检查其他点
                other_refs = [p for p in reference_points if p['id'] != ref_point['id']]
                for other_ref in other_refs:
                    relation = self.orientation_analyzer.get_orientation_relation(other_ref, current_point)
                    if relation != "none":
                        self._format_orientation_result(relation, current_point, other_ref, results)
                        found = True
                        break
        else:
            # 3. 分析所有参考点，找到第一个有效关系就记录（或你想记录所有？这里按“首个有效”处理）
            for ref_point in reference_points:
                relation = self.orientation_analyzer.get_orientation_relation(ref_point, current_point)
                if relation != "none":
                    self._format_orientation_result(relation, current_point, ref_point, results)
                    found = True
                    break  # 如需记录所有关系，移除 break

        # 可选：记录无关系的情况（按你上一个函数风格）
            if not found:
                results.append(f"{current_point['id']} has no defined orientation relation with reference points")

        return results

    def _format_orientation_result(self, relation: str, current_point: Dict, ref_point: Dict, results: List[str]):
        """辅助方法：格式化朝向关系字符串"""
        if relation.startswith("relative_heading_"):
            angle = relation.split("_")[-1]
            results.append(f"{current_point['id']} has relative heading {angle}° to {ref_point['id']}")
        else:
            results.append(f"{current_point['id']} is facing {relation} {ref_point['id']}")

    def analyze_sequence(self, points: List[Dict],
                         use_closest_only: bool = True) -> List[str]:
        """
        分析点序列（空间关系 + 朝向关系）

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

            # 1. 分析空间关系
            spatial_relation = self.analyze_point_relations(
                current_point, reference_points, use_closest_only
            )
            if spatial_relation:
                results.append(spatial_relation)

            # 2. 分析朝向关系（返回列表，需展开）
            orientation_relations = self.analyze_orientation_relations(
                current_point, reference_points, use_closest_only
            )
            results.extend(orientation_relations)  # ← 关键：用 extend 展开列表

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
    points1 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 90.0},
        {"id": "P1", "x": 5.0, "y": 0.0, "heading": 90.0},
        {"id": "P2", "x": 10.0, "y": -2.0, "heading": 90.0},
        {"id": "P3", "x": 8.0, "y": 3.0, "heading": 90.0},
        {"id": "P4", "x": 15.0, "y": 0.0, "heading": 90.0}
    ]
    points2 = [
        {"id": "ego", "x": 0.0, "y": 0.0, "heading": 90.0},
        {"id": "P1", "x": 5.0, "y": 5.0, "heading": 135.0},
        {"id": "P2", "x": 5.0, "y": 0.0, "heading": 0.0},
        {"id": "P3", "x": 0.0, "y": 8.0, "heading": 90.0},
        {"id": "P4", "x": -10, "y": 0.0, "heading": 90.0},
        {"id": "P5", "x": -10, "y": 5, "heading": 90.0}
    ]

    # 创建分析器
    analyzer = PointSequenceAnalyzer(temp_dir="./temp_smt")


    spatial_results = analyzer.analyze_sequence(points2)
    for i, result in enumerate(spatial_results, 1):
        print(f"{i}. {result}")




    # 清理临时文件（可选）
    # import shutil
    # shutil.rmtree("./temp_smt")


if __name__ == "__main__":
    main()
