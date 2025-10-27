(set-logic QF_NRA)

; auto-generated test: TC2_two_boundary
; params: A=(0.0,0.0), B=(0.0,1.0), A_h=90.0, min=-10.0, max=10.0

(declare-const A_x Real)
(declare-const A_y Real)
(declare-const B_x Real)
(declare-const B_y Real)
(declare-const A_h Real)
(declare-const min_angle Real)
(declare-const max_angle Real)

(assert (= A_x 0.0))
(assert (= A_y 0.0))
(assert (= B_x 0.0))
(assert (= B_y 1.0))
(assert (= A_h 90.0))
(assert (= min_angle -10.0))
(assert (= max_angle 10.0))

; assert the angle expression holds
(assert (let ((angle_deg (* (- (atan2 (- B_y A_y) (- B_x A_x)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ A_h min_angle))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ A_h max_angle))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))))

(check-sat)
(get-model)
