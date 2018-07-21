(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (and (= a b) (= b c) (not (= a c))))
(check-sat)
; :status unsat
