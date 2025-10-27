(set-logic QF_NRA)


(declare-const x0 Real)
(declare-const x1 Real)
(declare-const b Bool)  (assert (= b true))


(assert (and (or (= x0 x0 )  )))
(assert (and (or (= x1 x1 )  )))

(assert (and (or (= x0 x0 ) (= x1 x1 ) )))



(check-sat)
(get-model)
