(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (and a (=> a b) (not b)))
(check-sat)
; :status unsat
