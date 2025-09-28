(set-logic QF_NRA)

; ego
(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 0.0))

; other point
(declare-const x1 Real) (assert (= x1 0.0))
(declare-const y1 Real) (assert (= y1 1.41))

; "ahead" angle constraint: ego heading is reference
(assert
  (let ((angle_deg (* (- (atan2 (- y1 y0) (- x1 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
    (let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0)
                          (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))
      (let ((theta_min (+ h0 -10)))
        (let ((theta_max (+ h0 10)))
          (ite (<= theta_min theta_max)
               (and (>= norm_angle theta_min) (<= norm_angle theta_max))
               (or (>= norm_angle theta_min) (<= norm_angle theta_max))))))))


(check-sat)
(get-model)
