(set-logic QF_NRA)

(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 216.0))

(declare-const x1 Real) (assert (= x1 5.0))
(declare-const y1 Real) (assert (= y1 -5.0))
(declare-const h1 Real) (assert (= h1 0.0))

; ==== 布尔矩阵排列 ====
(declare-const b_0_0 Bool)

(assert (or b_0_0))



(assert (or b_0_0))

(define-fun vx0 () Real (ite b_0_0 x1 x1))
(define-fun vy0 () Real (ite b_0_0 y1 y1))
(define-fun vh0 () Real (ite b_0_0 h1 h1))



; ==== 朝向关系约束 ====
(declare-const head_choice_0 Int)
(assert (and (>= head_choice_0 0) (<= head_choice_0 0)))
(declare-const head_relation_v0_ego Int)
(assert (and (>= head_relation_v0_ego 1) (<= head_relation_v0_ego 3)))
(declare-const relative_angle_v0_ego Real)
(assert (and (>= relative_angle_v0_ego 0.0) (<= relative_angle_v0_ego 360.0)))
(assert (=> (= head_relation_v0_ego 1) (let ((delta_x (- x0 vx0)))  (let ((delta_y (- y0 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v0_ego 2) (let ((delta_x (- vx0 x0)))  (let ((delta_y (- vy0 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v0_ego 3) (let ((rel_heading (- vh0 h0)))  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))    (and (>= norm_rel  relative_angle_v0_ego ) (<= norm_rel (+ relative_angle_v0_ego 10)) (>= relative_angle_v0_ego 0) (< relative_angle_v0_ego 360))))))
(assert (ite (or (let ((delta_x (- x0 vx0)))  (let ((delta_y (- y0 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((delta_x (- vx0 x0)))  (let ((delta_y (- vy0 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))) (or (= head_relation_v0_ego 1) (= head_relation_v0_ego 2)) (= head_relation_v0_ego 3)))
(assert (and
(or (and (= head_choice_0 0) (or (= head_relation_v0_ego 1) (= head_relation_v0_ego 2) (= head_relation_v0_ego 3))))
))

(check-sat)
(get-model)
