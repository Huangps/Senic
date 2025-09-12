; SMT约束：检查B是否在A的behind侧且距离在[range_x, range_x+5]范围内


(set-logic ALL) 
; 定义变量
(declare-const A_x Real)
(declare-const A_y Real)
(declare-const A_heading Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const range_x Real)

; 设置已知值
(assert (= A_x 10.0))
(assert (= A_y -2.0))
(assert (= A_heading 90.0))
(assert (= B_x 8.0))
(assert (= B_y 3.0))


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
(define-fun angle_rad_y () Real (- angle_rad_nom (/ 3.141592653589793 2.0)))

; 计算B相对A的弧度
(define-fun angle_rad () Real (- angle_rad_y (/ (* A_heading 3.141592653589793) 180.0)))

; 转换为度数
(define-fun angle_deg () Real (* angle_rad (/ 180.0 3.141592653589793)))

; 规范化角度到[0, 360)
 
(define-fun normalize_angle ((theta Real)) Real
    (ite (>= theta 360.0) (- theta 360.0) theta)) 

(define-fun normalized_angle_deg () Real (normalize_angle angle_deg))

; behind角度范围
(define-fun theta_min () Real (normalize_angle (+ A_heading 170.0)))
(define-fun theta_max () Real (normalize_angle (+ A_heading 190.0)))

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
