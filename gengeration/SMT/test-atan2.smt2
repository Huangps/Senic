
(declare-const angle1 Real)
(assert (= angle1 (atan2 0.1 100)))

(declare-const angle2 Real)
(assert (= angle2 (atan2 0.1 -100)))

(declare-const angle3 Real)
(assert (= angle3 (atan2 -100 0.1)))

(declare-const angle4 Real)
(assert (= angle4 (atan2 -0.1 100)))


(check-sat)
(get-value (angle1 angle2 angle3 angle4))