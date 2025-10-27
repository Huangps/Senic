; ===============================================================
; SMT boundary test case (nonlinear, nested-let version + v1..v10)
; Ten variables + ten conditional (ite) formulas in disjunction
; Each ite's condition uses a value computed via three nested lets
; Each ite also constrains a fresh real variable v1..v10
; All primary x1..x10 set exactly on their boundary values
; No use of define-fun / no mod
; ===============================================================

(set-logic QF_NRA)

; 10 primary variables
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(declare-const x6 Real)
(declare-const x7 Real)
(declare-const x8 Real)
(declare-const x9 Real)
(declare-const x10 Real)

; 10 auxiliary variables to be solved
(declare-const v1 Real)
(declare-const v2 Real)
(declare-const v3 Real)
(declare-const v4 Real)
(declare-const v5 Real)
(declare-const v6 Real)
(declare-const v7 Real)
(declare-const v8 Real)
(declare-const v9 Real)
(declare-const v10 Real)

; Boundary assignments (exact)
(assert (= x1 -10.0))
(assert (= x2 11.0))
(assert (= x3 -21.0))
(assert (= x4 51.0))
(assert (= x5 102.0))
(assert (= x6 100.0))
(assert (= x7 -100.0))
(assert (= x8 360.0))
(assert (= x9 -360.0))
(assert (= x10 0.0))

; Disjunction of 10 ite formulas. Each ite's condition uses value
; computed through three nested lets (a -> b -> c). Each branch also
; constrains a corresponding v_i (then branch sets v_i = c_i, else sets v_i = -1.0).
(assert
  (or
    ; 1) x1 case: c1 = b1^2, with then binding v1 = c1
    (let ((a1 (* x1 1.0)))
      (let ((b1 (+ a1 0.0)))
        (let ((c1 (* b1 b1)))
          (ite (>= c1 0.0)
               (and (= x1 0.0) (= v1 c1))
               (= v1 -1.0)))))

    ; 2) x2 case: c2 = b2 - x2, then v2 = c2
    (let ((a2 (* x2 x2)))
      (let ((b2 (* a2 x2)))
        (let ((c2 (- b2 x2)))
          (ite (<= c2 0.0)
               (and (= x2 1.0) (= v2 c2))
               (= v2 -1.0)))))

    ; 3) x3 case: c3 = x3 * (x3+1) -> then v3 = c3
    (let ((a3 (+ x3 1.0)))
      (let ((b3 (* a3 1.0)))
        (let ((c3 (* x3 b3)))
          (ite (= c3 0.0)
               (and (< x3 0.0) (= v3 c3))
               (= v3 -1.0)))))

    ; 4) x4 case: c4 = x4^2 - 25 -> then v4 = c4
    (let ((a4 (* x4 x4)))
      (let ((b4 (- a4 25.0)))
        (let ((c4 (+ b4 0.0)))
          (ite (>= c4 0.0)
               (and (= (* x4 2) 10.0) (= v4 c4))
               (= v4 -1.0)))))

    ; 5) x5 case: c5 = (x5-10)^2 -> then v5 = c5
    (let ((a5 (- x5 10.0)))
      (let ((b5 (* a5 a5)))
        (let ((c5 (+ b5 0.0)))
          (ite (= c5 0.0)
               (and (= x5 10.0) (= v5 c5))
               (= v5 -1.0)))))

    ; 6) x6 case: c6 = x6^2 - 10000 -> then v6 = c6
    (let ((a6 (* x6 x6)))
      (let ((b6 (- a6 10000.0)))
        (let ((c6 b6))
          (ite (>= c6 0.0)
               (and (= x6 100.0) (= v6 c6))
               (= v6 -1.0)))))

    ; 7) x7 case: c7 = x7^3 + 1000000 -> then v7 = c7
    (let ((a7 (* x7 x7 x7)))
      (let ((b7 (+ a7 1000000.0)))
        (let ((c7 b7))
          (ite (<= c7 0.0)
               (and (= x7 -100.0) (= v7 c7))
               (= v7 -1.0)))))

    ; 8) x8 trig case: c8 = sin(x8 * π/180) -> then v8 = c8
    (let ((a8 (* x8 (/ 3.141592653589793 180.0))))
      (let ((b8 (sin a8)))
        (let ((c8 b8))
          (ite (>= c8 0.0)
               (and (= x8 360.0) (= v8 c8))
               (= v8 -1.0)))))

    ; 9) x9 trig case: c9 = cos(x9 * π/180) - 1 -> then v9 = c9
    (let ((a9 (* x9 (/ 3.141592653589793 180.0))))
      (let ((b9 (cos a9)))
        (let ((c9 (- b9 1.0)))
          (ite (<= c9 0.0)
               (and (= x9 -360.0) (= v9 c9))
               (= v9 -1.0)))))

    ; 10) x10 trig case: c10 = sin(x10) -> then v10 = c10
    (let ((a10 (+ x10 0.0)))
      (let ((b10 (sin a10)))
        (let ((c10 (* b10 1.0)))
          (ite (>= c10 0.0)
               (and (= x10 0.0) (= v10 c10))
               (= v10 -1.0)))))

  )
)

(check-sat)
(get-model)
