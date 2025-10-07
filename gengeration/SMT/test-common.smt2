(set-logic QF_NRA)



(define-fun A ((y1 Real) (y2 Real) (x1 Real) (x2 Real)) Real
     (- (+ y1 y2) (+ x1 x2) ) )

(define-fun A_result () Real (A 5.0 0.0 0.0 0.0))


(define-fun B ((y1 Real) (y2 Real) (x1 Real) (x2 Real)) Real
    (let ((B_1 (- (+ y1 y2) (+ x1 x2) ) ))
        (- B_1 0 )))


(define-fun B_result () Real (B 5.0 0.0 0.0 0.0))



(check-sat)
(get-model)
