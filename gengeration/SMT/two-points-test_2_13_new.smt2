(set-logic QF_NRA)

(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 0.0))

(declare-const x1 Real) (assert (= x1 15.0))
(declare-const y1 Real) (assert (= y1 15.0))
(declare-const h1 Real) (assert (= h1 0.0))

; ==== 布尔矩阵排列 ====
(declare-const b_0_0 Bool)

(assert (or b_0_0))



(assert (or b_0_0))

(define-fun vx0 () Real (ite b_0_0 x1 x1))
(define-fun vy0 () Real (ite b_0_0 y1 y1))
(define-fun vh0 () Real (ite b_0_0 h1 h1))

; ==== 位置关系约束 ====
(declare-const pos_choice_0 Int)
(assert (and (>= pos_choice_0 0) (<= pos_choice_0 0)))
(declare-const dist_v0_ego Real)
(declare-const dist_low_v0_ego Real)
(declare-const dist_high_v0_ego Real)
(assert (= dist_v0_ego (sqrt (+ (* (- vx0 x0) (- vx0 x0)) (* (- vy0 y0) (- vy0 y0))))))
(assert (= dist_high_v0_ego (+ dist_low_v0_ego 5)))
(declare-const local_x_v0_ego Real)
(assert (and (>= local_x_v0_ego -100.0) (<= local_x_v0_ego 100.0)))
(declare-const local_y_v0_ego Real)
(assert (and (>= local_y_v0_ego -100.0) (<= local_y_v0_ego 100.0)))
(declare-const relation_v0_ego Int)
(assert (= relation_v0_ego (ite (and (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 -10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v0_ego dist_low_v0_ego) (<= dist_v0_ego dist_high_v0_ego)) 1 
(ite (and (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 170))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 190))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v0_ego dist_low_v0_ego) (<= dist_v0_ego dist_high_v0_ego)) 2 
(ite (and (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 80))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 100))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v0_ego dist_low_v0_ego) (<= dist_v0_ego dist_high_v0_ego)) 3 
(ite (and (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 260))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 280))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v0_ego dist_low_v0_ego) (<= dist_v0_ego dist_high_v0_ego)) 4 
5))))))
(assert (=> (= relation_v0_ego 5) (let ((delta_x_global (- vx0 x0))      (delta_y_global (- vy0 y0)))  (let ((heading_rad (* h0 (/ 3.141592653589793 180.0))))    (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global) (* (cos heading_rad) delta_x_global)))          (local_y (+ (* (sin heading_rad) delta_x_global) (* (cos heading_rad) delta_y_global))))      (and (>= local_x local_x_v0_ego) (<= local_x (+ local_x_v0_ego 5))           (>= local_y local_y_v0_ego) (<= local_y (+ local_y_v0_ego 5))))))))
(assert ( and 
(or (and (= pos_choice_0 0) (= relation_v0_ego relation_v0_ego)))
))

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
