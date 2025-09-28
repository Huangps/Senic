(set-logic QF_NRA)

; ==================== 辅助函数定义 ====================
; 规范化到0～360
(define-fun normalize_angle ((angle Real)) Real
    (ite (> angle 360.0) (- angle 360.0)
    (ite (< angle 0.0) (+ angle 360.0)
    angle)))


;使用函数计算向量AB的角度（相对正Y轴的角度。 正y轴为0度，角度逆时针增加）
;先计算dy和dx
;atan2计算出和正X轴的夹角（弧度）
;减去pi/2 得到和正Y轴的夹角，再转换为角度制
;最后规范化到0～360
(define-fun relative_bearing ((Ax Real) (Ay Real) (Bx Real) (By Real)) Real
    (let ((dx (- Bx Ax))
          (dy (- By Ay)))
        (let ((angle_rad (atan2 dy dx)))
            (let ((angle_deg_normal (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
                (normalize_angle angle_deg_normal)))))

; ==================== 测试用例 ====================
; 测试: ego (0,0) ,P1(0,5)
(declare-const ego_x1 Real) (declare-const ego_y1 Real)
(declare-const P1_x1 Real) (declare-const P1_y1 Real)
(assert (= ego_x1 0.0)) (assert (= ego_y1 0.0))
(assert (= P1_x1 0.0)) (assert (= P1_y1 5.0))






; bearing2 为使用函数计算的结果，预期结果为0,实际为225
(define-fun bearing2 () Real (relative_bearing ego_x1 ego_y1 P1_x1 P1_y1))

; ==================== 求解 ====================
(check-sat)
(get-value (
     bearing2
))

