(set-logic QF_NRA)



; 定义 angle_offset

(define-fun normalize_angle ((angle Real)) Real
    (ite (> angle 360.0) (- angle 360.0)
    (ite (< angle 0.0) (+ angle 360.0)
    angle)))



(define-fun E () Real
    (let ((angle_rad (atan2 5.0 0.0 )))
        (let ((angle_deg_normal (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
            (normalize_angle angle_deg_normal))))


(define-fun F ((Ax Real) (Ay Real) (Bx Real) (By Real)) Real
    (let ((dx (- Bx Ax))
          (dy (- By Ay)))
        (let ((angle_rad (atan2 dy dx )))
            (let ((angle_deg_normal (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
                (normalize_angle angle_deg_normal)))))

(define-fun G () Real (F 0.0 0.0 0.0 5.0))



; 检查可满足性
(check-sat)

; 输出 angle_offset
(get-value ( E  G))
