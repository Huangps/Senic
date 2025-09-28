(set-logic QF_NRA)

; --- 声明 ego 和一个测试点 ---
; ego
(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 0.0))

; other point
(declare-const x1 Real) (assert (= x1 0.0))
(declare-const y1 Real) (assert (= y1 -5.0))
(declare-const h1 Real) (assert (= h1 0.0))

; --- toward_expr ---
(assert
  (let ((delta_x (- x0 x1)))
    (let ((delta_y (- y0 y1)))
      (let ((angle_rad (atan2 delta_y delta_x)))
        (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))
          (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0)
                                  (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))
            (let ((angle_diff (- norm_bearing h1)))
              (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))
                (<= min_angle_diff 10.0)))))))))


(check-sat)
(get-model)
