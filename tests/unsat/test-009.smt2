(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(assert (and (= a b) (or (= b c) (= b d)) (not (= a d)) (not (= a c))))
(check-sat)
; :status unsat
