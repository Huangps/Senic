(set-logic QF_NRA)

(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 180.0))

(declare-const x1 Real) (assert (= x1 0.0))
(declare-const y1 Real) (assert (= y1 1.4))
(declare-const h1 Real) (assert (= h1 0.0))

; ==== 布尔矩阵排列 ====
(declare-const b_0_0 Bool)

(assert (or b_0_0))


(define-fun vx0 () Real (ite b_0_0 x1 x1))
(define-fun vy0 () Real (ite b_0_0 y1 y1))
(define-fun vh0 () Real (ite b_0_0 h1 h1))

; ==== 位置关系约束 ====
(declare-const local_x_v0_ego Real)
(declare-const local_y_v0_ego Real)
(assert (and
(or (or (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (+ h0 -10)))(let ((theta_max (+ h0 10)))(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (+ h0 170)))(let ((theta_max (+ h0 190)))(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (+ h0 80)))(let ((theta_max (+ h0 100)))(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (let ((angle_deg (* (- (atan2 (- vy0 y0) (- vx0 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (+ h0 260)))(let ((theta_max (+ h0 280)))(ite (<= theta_min theta_max) (and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (let ((delta_x_global (- vx0 x0))      (delta_y_global (- vy0 y0)))  (let ((heading_rad (* h0 (/ 3.141592653589793 180.0))))    (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global) (* (cos heading_rad) delta_x_global)))          (local_y (+ (* (sin heading_rad) delta_x_global) (* (cos heading_rad) delta_y_global))))      (and (>= local_x local_x_v0_ego) (<= local_x (+ local_x_v0_ego 0.1))           (>= local_y local_y_v0_ego) (<= local_y (+ local_y_v0_ego 0.1))))))))
))

; ==== 朝向关系约束 ====
(declare-const relative_angle_v0_ego Real)
(assert (and
(or (or (let ((delta_x (- x0 vx0)))  (let ((delta_y (- y0 vy0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((delta_x (- vx0 x0)))  (let ((delta_y (- vy0 y0)))    (let ((angle_rad (atan2 delta_y delta_x)))      (let ((bearing_deg (* (- angle_rad (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))        (let ((norm_bearing (ite (>= bearing_deg 360.0) (- bearing_deg 360.0) (ite (< bearing_deg 0.0) (+ bearing_deg 360.0) bearing_deg))))          (let ((angle_diff (- norm_bearing vh0)))            (let ((min_angle_diff (ite (> angle_diff 180.0) (- 360.0 angle_diff) angle_diff)))              (<= min_angle_diff 10.0) ))))))) (let ((rel_heading (- vh0 h0)))  (let ((norm_rel (ite (>= rel_heading 360.0) (- rel_heading 360.0) (ite (< rel_heading 0.0) (+ rel_heading 360.0) rel_heading))))    (and (>= norm_rel (- relative_angle_v0_ego 5)) (<= norm_rel (+ relative_angle_v0_ego 5)) (>= relative_angle_v0_ego 0) (< relative_angle_v0_ego 360))))))
))

(check-sat)
(get-model)
