(set-logic QF_NRA)

; 声明 dx, dy
(declare-const dx Real)
(declare-const dy Real)

; 给 dx, dy 赋值
(assert (= dx 0.0))
(assert (= dy 5.0))

; 定义 angle_offset

(define-fun normalize_angle ((angle Real)) Real
    (ite (> angle 360.0) (- angle 360.0)
    (ite (< angle 0.0) (+ angle 360.0)
    angle)))



(define-fun A () Real  (atan2 dy dx)  )
(define-fun B () Real (- (atan2 dy dx) (/ 3.141592653589793 2.0) ))
(define-fun C () Real (*(- (atan2 dy dx) (/ 3.141592653589793 2.0) )  (/ 180.0 3.141592653589793)   ))

(define-fun D () Real (normalize_angle C))


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

; 声明 dx, dy
(declare-const dx1 Real)
(declare-const dy1 Real)
(declare-const ax1 Real)
(declare-const ay1 Real)
(declare-const bx1 Real)
(declare-const by1 Real)

(declare-const A Real)

(assert (= ax1 0.0 ))
(assert (= bx1 0.0 ))
(assert (= ay1 0.0 ))
(assert (= by1 5.0 ))


(assert (= dx1 (- bx1 ax1)))
(assert (= dy1 (- by1 ay1)))

(assert (= A (-( atan2 dy1 dx1)  (/ 3.141592653589793 2.0) )))


(define-fun G () Real (F 0.0 0.0 0.0 5.0))

(define-fun H () Real
        (let ((angle_rad (atan2 5.0 0)))
            (let ((angle_deg_normal (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
                (normalize_angle angle_deg_normal))))

(define-fun K ((Ax Real) (Ay Real) (Bx Real) (By Real)) Real
    (let ((dx (- Bx Ax))
          (dy (- By Ay)))
        (let ((angle_rad (atan2 5.0 0.0 )))
            (let ((angle_deg_normal (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
                (normalize_angle angle_deg_normal)))))

(define-fun I () Real (K 0.0 0.0 0.0 5.0))



; 检查可满足性
(check-sat)

; 输出 angle_offset
(get-value (dx1 dy1 A G H I))
