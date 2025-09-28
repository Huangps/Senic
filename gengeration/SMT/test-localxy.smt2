(set-logic QF_NRA)

; ego 点
(declare-const x0 Real)
(declare-const y0 Real)
(declare-const h0 Real)

(assert (= x0 0.0))
(assert (= y0 0.0))
(assert (= h0 45.0))

; B 点
(declare-const vx0 Real)
(declare-const vy0 Real)

(assert (= vx0 0.0))
(assert (= vy0 1.41))

; 局部坐标变量
(declare-const local_x_v0_ego Real)
(declare-const local_y_v0_ego Real)

; 约束：B 点相对 ego 落在 [local_x, local_x+0.1] × [local_y, local_y+0.1]
(assert
  (let ((delta_x_global (- vx0 x0))
        (delta_y_global (- vy0 y0)))
    (let ((heading_rad (* h0 (/ 3.141592653589793 180.0))))
      (let ((local_x (+ (* (- (sin heading_rad)) delta_y_global)
                        (* (cos heading_rad) delta_x_global)))
            (local_y (+ (* (sin heading_rad) delta_x_global)
                        (* (cos heading_rad) delta_y_global))))
        (and (>= local_x local_x_v0_ego) (<= local_x (+ local_x_v0_ego 0.1))
             (>= local_y local_y_v0_ego) (<= local_y (+ local_y_v0_ego 0.1)))))))

(check-sat)
(get-model)
