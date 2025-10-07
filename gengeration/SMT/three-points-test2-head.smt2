(set-logic QF_NRA)

(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 0.0))

(declare-const x1 Real) (assert (= x1 5.0))
(declare-const y1 Real) (assert (= y1 5.0))
(declare-const h1 Real) (assert (= h1 0.0))

(declare-const x2 Real) (assert (= x2 -5.0))
(declare-const y2 Real) (assert (= y2 5.0))
(declare-const h2 Real) (assert (= h2 0.0))

; ==== 布尔矩阵排列 ====
(declare-const b_0_0 Bool)
(declare-const b_0_1 Bool)
(declare-const b_1_0 Bool)
(declare-const b_1_1 Bool)

(assert (or b_0_0 b_0_1))
(assert (or b_1_0 b_1_1))

(assert (not (and b_0_0 b_0_1)))
(assert (not (and b_1_0 b_1_1)))

(assert (not (and b_0_0 b_1_0)))
(assert (not (and b_0_1 b_1_1)))

(assert (or b_0_0 b_1_0))
(assert (or b_0_1 b_1_1))

(define-fun vx0 () Real (ite b_0_0 x1 (ite b_0_1 x2 x2)))
(define-fun vy0 () Real (ite b_0_0 y1 (ite b_0_1 y2 y2)))
(define-fun vh0 () Real (ite b_0_0 h1 (ite b_0_1 h2 h2)))

(define-fun vx1 () Real (ite b_1_0 x1 (ite b_1_1 x2 x2)))
(define-fun vy1 () Real (ite b_1_0 y1 (ite b_1_1 y2 y2)))
(define-fun vh1 () Real (ite b_1_0 h1 (ite b_1_1 h2 h2)))


; ==== 朝向关系约束 ====
(declare-const head_choice_0 Int)
(assert (and (>= head_choice_0 0) (<= head_choice_0 0)))
(declare-const head_relation_v0_ego Int)
(assert (and (>= head_relation_v0_ego 1) (<= head_relation_v0_ego 3)))
(declare-const relative_angle_v0_ego Real)
(assert (and (>= relative_angle_v0_ego 0.0) (<= relative_angle_v0_ego 360.0)))
(assert (=> (= head_relation_v0_ego 1) (let ((delta_x (- x0 vx0)))  (let ((delta_y (- y0 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v0_ego 2) (let ((delta_x (- vx0 x0)))  (let ((delta_y (- vy0 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v0_ego 3) (let ((rel_heading (- vh0 h0)))  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))    (and (>= norm_rel (- relative_angle_v0_ego 5)) (<= norm_rel (+ relative_angle_v0_ego 5)) (>= relative_angle_v0_ego 0) (< relative_angle_v0_ego 360))))))
(assert (ite (or (let ((delta_x (- x0 vx0)))  (let ((delta_y (- y0 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((delta_x (- vx0 x0)))  (let ((delta_y (- vy0 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))) (or (= head_relation_v0_ego 1) (= head_relation_v0_ego 2)) (= head_relation_v0_ego 3)))
(declare-const head_choice_1 Int)
(assert (and (>= head_choice_1 0) (<= head_choice_1 1)))
(declare-const head_relation_v1_ego Int)
(assert (and (>= head_relation_v1_ego 1) (<= head_relation_v1_ego 3)))
(declare-const relative_angle_v1_ego Real)
(assert (and (>= relative_angle_v1_ego 0.0) (<= relative_angle_v1_ego 360.0)))
(assert (=> (= head_relation_v1_ego 1) (let ((delta_x (- x0 vx1)))  (let ((delta_y (- y0 vy1)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v1_ego 2) (let ((delta_x (- vx1 x0)))  (let ((delta_y (- vy1 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v1_ego 3) (let ((rel_heading (- vh1 h0)))  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))    (and (>= norm_rel (- relative_angle_v1_ego 5)) (<= norm_rel (+ relative_angle_v1_ego 5)) (>= relative_angle_v1_ego 0) (< relative_angle_v1_ego 360))))))
(assert (ite (or (let ((delta_x (- x0 vx1)))  (let ((delta_y (- y0 vy1)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((delta_x (- vx1 x0)))  (let ((delta_y (- vy1 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))) (or (= head_relation_v1_ego 1) (= head_relation_v1_ego 2)) (= head_relation_v1_ego 3)))
(declare-const head_relation_v1_v0 Int)
(assert (and (>= head_relation_v1_v0 1) (<= head_relation_v1_v0 3)))
(declare-const relative_angle_v1_v0 Real)
(assert (and (>= relative_angle_v1_v0 0.0) (<= relative_angle_v1_v0 360.0)))
(assert (=> (= head_relation_v1_v0 1) (let ((delta_x (- vx0 vx1)))  (let ((delta_y (- vy0 vy1)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v1_v0 2) (let ((delta_x (- vx1 vx0)))  (let ((delta_y (- vy1 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))))
(assert (=> (= head_relation_v1_v0 3) (let ((rel_heading (- vh1 vh0)))  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))    (and (>= norm_rel (- relative_angle_v1_v0 5)) (<= norm_rel (+ relative_angle_v1_v0 5)) (>= relative_angle_v1_v0 0) (< relative_angle_v1_v0 360))))))
(assert (ite (or (let ((delta_x (- vx0 vx1)))  (let ((delta_y (- vy0 vy1)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((delta_x (- vx1 vx0)))  (let ((delta_y (- vy1 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh1)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) )))))))) (or (= head_relation_v1_v0 1) (= head_relation_v1_v0 2)) (= head_relation_v1_v0 3)))
(assert (and
(or (and (= head_choice_0 0) (or (= head_relation_v0_ego 1) (= head_relation_v0_ego 2) (= head_relation_v0_ego 3))))
(or (and (= head_choice_1 0) (or (= head_relation_v1_ego 1) (= head_relation_v1_ego 2) (= head_relation_v1_ego 3))) (and (= head_choice_1 1) (or (= head_relation_v1_v0 1) (= head_relation_v1_v0 2) (= head_relation_v1_v0 3))))
))

(check-sat)
(get-model)
