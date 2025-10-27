

(declare-const angle Real)
(declare-const angle_rad Real)
(declare-const angle1 Real)

(assert (= angle (atan2 -5 5)))


(assert (= angle_rad (+ angle (/ 3.141592653589793 4.0))))


(check-sat)
(get-value ( angle angle_rad))