import math


def Left_of_by_range(A_x, A_y, A_heading, B_x, B_y, output_file="constraints.smt2"):
    """
    生成SMT约束文件，检查B是否在A的左侧且距离在[range_x, range_y]范围内。

    参数:
        A_x, A_y: A的坐标。
        A_heading: A的朝向角度（度数）。
        B_x, B_y: B的坐标。
        range_x, range_y: 距离范围。
        output_file: 输出的SMT文件路径（默认: "constraints.smt2"）。
    """
    smt_code = f"""; SMT约束：检查B是否在A的左侧且距离在[range_x, range_x + 5]范围内


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
             (+ raw_angle (* 2.0 3.141592653589793))
             raw_angle)))

; 计算B相对正y轴的弧度
(define-fun angle_rad_y () Real (-  angle_rad_nom  (/ {math.pi} 2) ))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y A_heading))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 左边角度范围（A_heading + 80度到A_heading + 100度）
(define-fun theta_left_min () Real (+ A_heading 80.0))
(define-fun theta_left_max () Real (+ A_heading 100.0))

; 规范化角度到[0, 360)
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta))

(define-fun theta_left_min_norm () Real (normalize_angle theta_left_min))
(define-fun theta_left_max_norm () Real (normalize_angle theta_left_max))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_left_min_norm theta_left_max_norm)
        (and (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))
        (or (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))))

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
    生成SMT约束文件，检查B是否在A的左侧且距离在[range_x, range_y]范围内。

    参数:
        A_x, A_y: A的坐标。
        A_heading: A的朝向角度（度数）。
        B_x, B_y: B的坐标。
        range_x, range_y: 距离范围。
        output_file: 输出的SMT文件路径（默认: "constraints.smt2"）。
    """
    smt_code = f"""; SMT约束：检查B是否在A的左侧且距离在[range_x, range_x+5]范围内


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
             (+ raw_angle (* 2.0 3.141592653589793))
             raw_angle)))

; 计算B相对正y轴的弧度
(define-fun angle_rad_y () Real (-  angle_rad_nom  (/ {math.pi} 2) ))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y A_heading))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 右边角度范围（A_heading + 260度到A_heading + 280度）
(define-fun theta_left_min () Real (+ A_heading 80.0))
(define-fun theta_left_max () Real (+ A_heading 100.0))

; 规范化角度到[0, 360)
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta))

(define-fun theta_left_min_norm () Real (normalize_angle theta_left_min))
(define-fun theta_left_max_norm () Real (normalize_angle theta_left_max))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_left_min_norm theta_left_max_norm)
        (and (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))
        (or (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))))

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
    生成SMT约束文件，检查B是否在A的左侧且距离在[range_x, range_y]范围内。

    参数:
        A_x, A_y: A的坐标。
        A_heading: A的朝向角度（度数）。
        B_x, B_y: B的坐标。
        range_x, range_y: 距离范围。
        output_file: 输出的SMT文件路径（默认: "constraints.smt2"）。
    """
    smt_code = f"""; SMT约束：检查B是否在A的左侧且距离在[range_x, range_x+5]范围内


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
             (+ raw_angle (* 2.0 3.141592653589793))
             raw_angle)))

; 计算B相对正y轴的弧度
(define-fun angle_rad_y () Real (-  angle_rad_nom  (/ {math.pi} 2) ))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y A_heading))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 前方角度范围（A_heading - 10度到A_heading + 10度）
(define-fun theta_left_min () Real (- A_heading 10.0))
(define-fun theta_left_max () Real (+ A_heading 10.0))

; 规范化角度到[0, 360)
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta))

(define-fun theta_left_min_norm () Real (normalize_angle theta_left_min))
(define-fun theta_left_max_norm () Real (normalize_angle theta_left_max))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_left_min_norm theta_left_max_norm)
        (and (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))
        (or (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))))

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
    生成SMT约束文件，检查B是否在A的左侧且距离在[range_x, range_y]范围内。

    参数:
        A_x, A_y: A的坐标。
        A_heading: A的朝向角度（度数）。
        B_x, B_y: B的坐标。
        range_x, range_y: 距离范围。
        output_file: 输出的SMT文件路径（默认: "constraints.smt2"）。
    """
    smt_code = f"""; SMT约束：检查B是否在A的左侧且距离在[range_x, range_x+5]范围内


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
             (+ raw_angle (* 2.0 3.141592653589793))
             raw_angle)))

; 计算B相对正y轴的弧度
(define-fun angle_rad_y () Real (-  angle_rad_nom  (/ {math.pi} 2) ))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y A_heading))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 {math.pi})))

; 前方角度范围（A_heading + 170度到A_heading + 180度）
(define-fun theta_left_min () Real (+ A_heading 170.0))
(define-fun theta_left_max () Real (+ A_heading 180.0))

; 规范化角度到[0, 360)
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta))

(define-fun theta_left_min_norm () Real (normalize_angle theta_left_min))
(define-fun theta_left_max_norm () Real (normalize_angle theta_left_max))

; 角度约束（处理跨越0度的情况）
(define-fun angle_constraint () Bool
    (ite (<= theta_left_min_norm theta_left_max_norm)
        (and (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))
        (or (>= angle_deg theta_left_min_norm) (<= angle_deg theta_left_max_norm))))

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

