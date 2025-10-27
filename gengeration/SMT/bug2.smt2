(set-logic QF_NRA)

; ---------------------------
; 候选点
; ---------------------------
(declare-const x1 Real) (assert (= x1 0))
(declare-const x2 Real) (assert (= x2 5))

; ---------------------------
; 布尔矩阵排列选择
; ---------------------------
(declare-const b_0_0 Bool)
(declare-const b_0_1 Bool)
(declare-const b_1_0 Bool)
(declare-const b_1_1 Bool)

; 每行选一个
(assert (or b_0_0 b_0_1))
(assert (or b_1_0 b_1_1))
(assert (not (and b_0_0 b_0_1)))
(assert (not (and b_1_0 b_1_1)))

; 每列最多一个
(assert (not (and b_0_0 b_1_0)))
(assert (not (and b_0_1 b_1_1)))

; ---------------------------
; 定义逻辑变量
; ---------------------------
(define-fun vx0 () Real (ite b_0_0 x1 (ite b_0_1 x2 x2)))
(define-fun vx1 () Real (ite b_1_0 x1 (ite b_1_1 x2 x2)))

; ---------------------------
; A 和 B
; ---------------------------
; 简化版本：A = vx0 == 0, B = vx1 == 5


; ---------------------------
; 测试组合
; ---------------------------
(assert (and (or (= vx0 5)  (= vx1 5))))

(check-sat)
(get-model)
