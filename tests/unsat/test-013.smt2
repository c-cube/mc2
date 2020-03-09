(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun p (U) Bool)
(assert (and (= a b) (not (p a)) (p b)))
(check-sat)
; :status unsat
