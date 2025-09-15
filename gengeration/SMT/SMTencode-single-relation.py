import math
import os
import subprocess
from typing import List, Dict, Tuple, Optional

temp_dir: str = "./temp_smt"
dreal_path = "/opt/dreal/4.21.06.2/bin/dreal"

def _run_smt_solver(file_path: str) -> tuple[bool, str]:
    try:
        result = subprocess.run(
            [dreal_path, file_path],
            capture_output=True,
            text=True,
            timeout=30
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
def _write_smt_file(smt_code: str, filename: str) -> str:
    file_path = os.path.join(temp_dir, filename)
    with open(file_path, "w") as f:
        f.write(smt_code)
    return file_path

def generate_relation_smt_code( A_x: float, A_y: float, A_heading: float,
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


def find_local_xy(A_point: Dict, B_point: Dict) -> Optional[Tuple[float, float]]:
    smt_code = generate_relation_smt_code(
        A_point['x'], A_point['y'], A_point['heading'],
        B_point['x'], B_point['y']
    )
    filename = f"{B_point['id']}_local_xy_{A_point['id']}.smt2"
    file_path = _write_smt_file(smt_code, filename)
    success, result = _run_smt_solver(file_path)

    if not success or "unsat" in result:
        return None

    try:
        # 解析 ((x ...) (y ...))
        if "(x" in result and "(y" in result:
            # 提取 x
            start_x = result.find("(x") + len("(x")
            end_x = result.find(")", start_x)
            x_val = float(result[start_x:end_x].strip())

            # 提取 y
            start_y = result.find("(y") + len("(y")
            end_y = result.find(")", start_y)
            y_val = float(result[start_y:end_y].strip())

            return x_val, y_val
    except Exception as e:
        print(f"解析失败: {e}")
        return None

    return None

A={"id": "ego","x": 0.0, "y": 0.0, "heading": 90.0}
B={"id": "p","x": 5.0, "y": 0.0}
result = find_local_xy(A, B)
if result is not None:
    x, y = result
    print(f"x={x:.2f}, y={y:.2f}")
else:
    print("SMT求解失败或无解")







def Left_of_by_range(A_x, A_y, A_heading, B_x, B_y, output_file="constraints.smt2"):
    """
    生成SMT约束文件，检查B是否在A的left且距离在[range_x, range_x+5]范围内。

    坐标系：正Y轴=0度，角度逆时针增加
    正Y轴=0°, 负X轴=90°, 负Y轴=180°, 正X轴=270°
    """
    smt_code = f"""; SMT约束：检查B是否在A的left且距离在[range_x, range_x+5]范围内
; 坐标系：正Y轴=0度，角度逆时针增加
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

; 计算B相对正Y轴的角度（弧度）
; 坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ {math.pi} 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun angle_deg_absolute () Real (normalize_angle angle_deg_raw))

; 计算B相对于A朝向的相对角度
(define-fun angle_deg_relative () Real (- angle_deg_absolute A_heading))
(define-fun angle_deg () Real (normalize_angle angle_deg_relative))

; left角度范围：80-100度（相对于A的朝向）
(define-fun theta_min () Real 80.0)
(define-fun theta_max () Real 100.0)

; 角度约束
(define-fun angle_constraint () Bool
    (and (>= angle_deg theta_min) (<= angle_deg theta_max)))

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

    # 写入SMT文件
    with open(output_file, "w") as f:
        f.write(smt_code)

    print(f"SMT约束文件已生成: {output_file}")


def Right_of_by_range(A_x, A_y, A_heading, B_x, B_y, output_file="constraints.smt2"):
    """
    生成SMT约束文件，检查B是否在A的Right且距离在[range_x, range_x+5]范围内。

    坐标系：正Y轴=0度，角度逆时针增加
    正Y轴=0°, 负X轴=90°, 负Y轴=180°, 正X轴=270°
    """
    smt_code = f"""; SMT约束：检查B是否在A的Right且距离在[range_x, range_x+5]范围内
; 坐标系：正Y轴=0度，角度逆时针增加

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

; 计算B相对正Y轴的角度（弧度
; 坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ {math.pi} 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun angle_deg_absolute () Real (normalize_angle angle_deg_raw))

; 计算B相对于A朝向的相对角度
(define-fun angle_deg_relative () Real (- angle_deg_absolute A_heading))
(define-fun angle_deg () Real (normalize_angle angle_deg_relative))

; Right角度范围：260-280度（相对于A的朝向）
(define-fun theta_min () Real 260.0)
(define-fun theta_max () Real 280.0)

; 角度约束
(define-fun angle_constraint () Bool
    (and (>= angle_deg theta_min) (<= angle_deg theta_max)))

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

    # 写入SMT文件
    with open(output_file, "w") as f:
        f.write(smt_code)

    print(f"SMT约束文件已生成: {output_file}")

def Ahead_of_by_range(A_x, A_y, A_heading, B_x, B_y, output_file="constraints.smt2"):
    """
    生成SMT约束文件，检查B是否在A的Ahead且距离在[range_x, range_x+5]范围内。

    坐标系：正Y轴=0度，角度逆时针增加
    正Y轴=0°, 负X轴=90°, 负Y轴=180°, 正X轴=270°
    """
    smt_code = f"""; SMT约束：检查B是否在A的Ahead且距离在[range_x, range_x+5]范围内
; 坐标系：正Y轴=0度，角度逆时针增加

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

; 计算B相对正Y轴的角度（弧度）- 正确的方法
; 坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ {math.pi} 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun angle_deg_absolute () Real (normalize_angle angle_deg_raw))

; 计算B相对于A朝向的相对角度
(define-fun angle_deg_relative () Real (- angle_deg_absolute A_heading))
(define-fun angle_deg () Real (normalize_angle angle_deg_relative))

; Ahead角度范围：-10 - 10度（相对于A的朝向）
(define-fun theta_min () Real - 10.0)
(define-fun theta_max () Real 10.0)

; 角度约束
(define-fun angle_constraint () Bool
    (and (>= angle_deg theta_min) (<= angle_deg theta_max)))

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

    # 写入SMT文件
    with open(output_file, "w") as f:
        f.write(smt_code)

    print(f"SMT约束文件已生成: {output_file}")


def Behind_by_range(A_x, A_y, A_heading, B_x, B_y, output_file="constraints.smt2"):
    """
    生成SMT约束文件，检查B是否在A的后方且距离在[range_x, range_x+5]范围内。

    坐标系：正Y轴=0度，角度逆时针增加
    正Y轴=0°, 负X轴=90°, 负Y轴=180°, 正X轴=270°
    """
    smt_code = f"""; SMT约束：检查B是否在A的后方且距离在[range_x, range_x+5]范围内
; 坐标系：正Y轴=0度，角度逆时针增加

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

; 计算B相对正Y轴的角度（弧度）- 正确的方法
; 坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ {math.pi} 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 {math.pi})))

; 角度规范化到[0, 360)
(define-fun normalize_angle ((angle Real)) Real
    (ite (>= angle 360.0) (- angle 360.0)
         (ite (< angle 0.0) (+ angle 360.0)
              angle)))

(define-fun angle_deg_absolute () Real (normalize_angle angle_deg_raw))

; 计算B相对于A朝向的相对角度
(define-fun angle_deg_relative () Real (- angle_deg_absolute A_heading))
(define-fun angle_deg () Real (normalize_angle angle_deg_relative))

; 后方角度范围：170-190度（相对于A的朝向）
(define-fun theta_min () Real 170.0)
(define-fun theta_max () Real 190.0)

; 角度约束
(define-fun angle_constraint () Bool
    (and (>= angle_deg theta_min) (<= angle_deg theta_max)))

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

    # 写入SMT文件
    with open(output_file, "w") as f:
        f.write(smt_code)

    print(f"SMT约束文件已生成: {output_file}")


#Behind_by_range(0, 0, 90, 5, 0, output_file="constraints.smt2")