; SMT约束：检查B是否在A的后方且距离在[range_x, range_x+5]范围内
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
(assert (= A_x 0))
(assert (= A_y 0))
(assert (= A_heading 90))
(assert (= B_x 5))
(assert (= B_y 0))

; 计算相对坐标，B相对A
(define-fun delta_x () Real (- B_x A_x))
(define-fun delta_y () Real (- B_y A_y))

; 计算距离
(define-fun distance () Real (sqrt (+ (* delta_x delta_x) (* delta_y delta_y))))

; 计算B相对正Y轴的角度（弧度）- 正确的方法
; 在你的坐标系中，正Y轴=0度，所以需要调整atan2的使用
(define-fun angle_rad () Real 
    (let ((raw_angle (- (atan2 delta_y delta_x) (/ 3.141592653589793 2.0))))
        raw_angle))

; 转换为度数
(define-fun angle_deg_raw () Real (* angle_rad (/ 180.0 3.141592653589793)))

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
