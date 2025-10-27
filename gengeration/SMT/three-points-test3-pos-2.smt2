(set-logic QF_NRA)

(declare-const x0 Real) (assert (= x0 0.0))
(declare-const y0 Real) (assert (= y0 0.0))
(declare-const h0 Real) (assert (= h0 0.0))

(declare-const x1 Real) (assert (= x1 -5.0))
(declare-const y1 Real) (assert (= y1 0.0))
(declare-const h1 Real) (assert (= h1 0.0))

(declare-const x2 Real) (assert (= x2 -10.0))
(declare-const y2 Real) (assert (= y2 0.0))
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
(declare-const pos_choice_1 Int)
(assert (and (>= pos_choice_1 0) (<= pos_choice_1 1)))
(declare-const dist_v1_ego Real)
(declare-const dist_low_v1_ego Real)
(declare-const dist_high_v1_ego Real)
(assert (= dist_v1_ego (sqrt (+ (* (- vx1 x0) (- vx1 x0)) (* (- vy1 y0) (- vy1 y0))))))
(assert (= dist_high_v1_ego (+ dist_low_v1_ego 5)))
(declare-const local_x_v1_ego Real)
(assert (and (>= local_x_v1_ego -100.0) (<= local_x_v1_ego 100.0)))
(declare-const local_y_v1_ego Real)
(assert (and (>= local_y_v1_ego -100.0) (<= local_y_v1_ego 100.0)))
(declare-const relation_v1_ego Int)
(declare-const dist_v1_v0 Real)
(declare-const dist_low_v1_v0 Real)
(declare-const dist_high_v1_v0 Real)
(assert (= dist_v1_v0 (sqrt (+ (* (- vx1 vx0) (- vx1 vx0)) (* (- vy1 vy0) (- vy1 vy0))))))
(assert (= dist_high_v1_v0 (+ dist_low_v1_v0 5)))
(declare-const local_x_v1_v0 Real)
(assert (and (>= local_x_v1_v0 -100.0) (<= local_x_v1_v0 100.0)))
(declare-const local_y_v1_v0 Real)
(assert (and (>= local_y_v1_v0 -100.0) (<= local_y_v1_v0 100.0)))
(declare-const relation_v1_v0 Int)



 (assert ( and

(or (and (= pos_choice_1 0) (= relation_v1_ego (ite (and (let ((angle_deg (* (- (atan2 (- vy1 y0) (- vx1 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 -10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_ego dist_low_v1_ego) (<= dist_v1_ego dist_high_v1_ego)) 1
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 y0) (- vx1 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 170))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 190))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_ego dist_low_v1_ego) (<= dist_v1_ego dist_high_v1_ego)) 2
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 y0) (- vx1 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 80))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 100))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_ego dist_low_v1_ego) (<= dist_v1_ego dist_high_v1_ego)) 3
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 y0) (- vx1 x0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ h0 260))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ h0 280))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_ego dist_low_v1_ego) (<= dist_v1_ego dist_high_v1_ego)) 4  5
 ))))) (=> (= relation_v1_ego 5) (let ((delta_x_global (- vx1 x0))      (delta_y_global (- vy1 y0)))  (let ((heading_rad (* h0 (/ 3.141592653589793 180.0))))    (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global) (* (cos heading_rad) delta_x_global)))          (local_y (+ (* (sin heading_rad) delta_x_global) (* (cos heading_rad) delta_y_global))))      (and (>= local_x local_x_v1_ego) (<= local_x (+ local_x_v1_ego 5))           (>= local_y local_y_v1_ego) (<= local_y (+ local_y_v1_ego 5)))))))
)
  (and (= pos_choice_1 1) (= relation_v1_v0 (ite (and (let ((angle_deg (* (- (atan2 (- vy1 vy0) (- vx1 vx0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ vh0 -10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ vh0 10))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_v0 dist_low_v1_v0) (<= dist_v1_v0 dist_high_v1_v0)) 1
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 vy0) (- vx1 vx0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ vh0 170))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ vh0 190))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_v0 dist_low_v1_v0) (<= dist_v1_v0 dist_high_v1_v0)) 2
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 vy0) (- vx1 vx0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ vh0 80))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ vh0 100))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_v0 dist_low_v1_v0) (<= dist_v1_v0 dist_high_v1_v0)) 3
(ite (and (let ((angle_deg (* (- (atan2 (- vy1 vy0) (- vx1 vx0)) (/ 3.141592653589793 2.0)) (/ 180.0 3.141592653589793))))(let ((norm_angle (ite (>= angle_deg 360.0) (- angle_deg 360.0) (ite (< angle_deg 0.0) (+ angle_deg 360.0) angle_deg))))(let ((theta_min (let ((raw (+ vh0 260))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(let ((theta_max (let ((raw (+ vh0 280))) (ite (>= raw 360.0) (- raw 360.0) (ite (< raw 0.0) (+ raw 360.0) raw)))))(ite (<= theta_min theta_max)(and (>= norm_angle theta_min) (<= norm_angle theta_max))(or (>= norm_angle theta_min) (<= norm_angle theta_max))))))) (>= dist_v1_v0 dist_low_v1_v0) (<= dist_v1_v0 dist_high_v1_v0)) 4  5
 ))))) (=> (= relation_v1_v0 5) (let ((delta_x_global (- vx1 vx0))      (delta_y_global (- vy1 vy0)))  (let ((heading_rad (* vh0 (/ 3.141592653589793 180.0))))    (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global) (* (cos heading_rad) delta_x_global)))          (local_y (+ (* (sin heading_rad) delta_x_global) (* (cos heading_rad) delta_y_global))))      (and (>= local_x local_x_v1_v0) (<= local_x (+ local_x_v1_v0 5))           (>= local_y local_y_v1_v0) (<= local_y (+ local_y_v1_v0 5)))))))
)

 )

))



(check-sat)
(get-model)
