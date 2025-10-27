; ===============================================================
; SMT boundary test case (nonlinear, nested-let version)
; Ten variables + ten conditional (ite) formulas in disjunction
; Each ite condition's test expression is computed via three nested lets
; All variables are set exactly on their boundary values
; No use of define-fun / no mod
; ===============================================================

(set-logic QF_NRA)

; 10 variables
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

; Boundary assignments (exact)
(assert (= x1 10.0))
(assert (= x2 12.0))
(assert (= x3 -11.0))
(assert (= x4 52.0))
(assert (= x5 101.0))
(assert (= x6 1002.0))
(assert (= x7 -1001.0))
(assert (= x8 3602.0))
(assert (= x9 -3601.0))
(assert (= x10 10.0))

; Disjunction of 10 ite formulas. Each ite's condition uses a value
; computed through three nested let bindings (a -> b -> c).
(assert
  (and
    ; 1 c = (b = (+ a 0.0), a = (* x1 1.0), c = (* b b))  => c == 0
    (let ((a1 (* x1 1.0)))
      (let ((b1 (+ a1 0.0)))
        (let ((c1 (* b1 b1)))
          (ite (>= c1 0.0) (= x1 0.0) (> c1 0.0)))))
    ; 2 a = x2^2, b = a*x2, c = b - x2  => c == 0 for x2=1
    (let ((a2 (* x2 x2)))
      (let ((b2 (* a2 x2)))
        (let ((c2 (- b2 x2)))
          (ite (<= c2 0.0) (= x2 1.0) (< c2 0.0)))))
    ; 3 a = x3 + 1, b = (* a 1.0), c = (* x3 b) => c == 0 for x3=-1
    (let ((a3 (+ x3 1.0)))
      (let ((b3 (* a3 1.0)))
        (let ((c3 (* x3 b3)))
          (ite (= c3 0.0) (< x3 0.0) (> x3 0.0)))))
    ; 4 a = x4^2, b = a - 25, c = (+ b 0.0) => c == 0 for x4=5
    (let ((a4 (* x4 x4)))
      (let ((b4 (- a4 25.0)))
        (let ((c4 (+ b4 0.0)))
          (ite (>= c4 0.0) (= (* x4 2) 10.0) (< x4 5.0)))))
    ; 5 a = x5 - 10, b = a^2, c = b + 0 => c == 0 for x5=10
    (let ((a5 (- x5 10.0)))
      (let ((b5 (* a5 a5)))
        (let ((c5 (+ b5 0.0)))
          (ite (= c5 0.0) (= x5 10.0) (= x5 9.9)))))
    ; 6 a = x6^2, b = a - 10000, c = b => c == 0 for x6=100
    (let ((a6 (* x6 x6)))
      (let ((b6 (- a6 10000.0)))
        (let ((c6 b6))
          (ite (>= c6 0.0) (= x6 100.0) (< x6 100.0)))))
    ; 7 a = x7^3, b = a + 1000000, c = b => c == 0 for x7=-100
    (let ((a7 (* x7 x7 x7)))
      (let ((b7 (+ a7 1000000.0)))
        (let ((c7 b7))
          (ite (<= c7 0.0) (= x7 -100.0) (> x7 -100.0)))))
    ; 8 a = x8 * (π/180), b = sin(a), c = b => sin(360°)=0
    (let ((a8 (* x8 (/ 3.141592653589793 180.0))))
      (let ((b8 (sin a8)))
        (let ((c8 b8))
          (ite (>= c8 0.0) (= x8 360.0) (= (- x8 360.0) 0.0)))))
    ; 9 a = x9 * (π/180), b = cos(a), c = (- b 1.0) => cos(-360°)=1 -> c==0
    (let ((a9 (* x9 (/ 3.141592653589793 180.0))))
      (let ((b9 (cos a9)))
        (let ((c9 (- b9 1.0)))
          (ite (<= c9 0.0) (= x9 -360.0) (= (+ x9 360.0) 0.0)))))
    ; 10 a = (+ x10 0.0), b = sin(a), c = (* b 1.0) => c == 0 for x10=0
    (let ((a10 (+ x10 0.0)))
      (let ((b10 (sin a10)))
        (let ((c10 (* b10 1.0)))
          (ite (>= c10 0.0) (= x10 0.0) (< x10 0.0)))))

))

(check-sat)
(get-model)
