(set-logic QF_NRA)

; ego
(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 45.0))

; other point
(declare-const x1 Real) (assert (= x1 -10.0))
(declare-const y1 Real) (assert (= y1 -10.0))
(declare-const h1 Real) (assert (= h1 45.0))

; relative angle variable
(declare-const relative_angle_v0_ego Real)

; relative_expr
(assert
  (let ((rel_heading (- h1 h0)))
    (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0)
                        (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))
      (and (>= norm_rel (- relative_angle_v0_ego 5))
           (<= norm_rel (+ relative_angle_v0_ego 5))
           (>= relative_angle_v0_ego 0)
           (< relative_angle_v0_ego 360)))))


(check-sat)
(get-model)
