(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(assert (and (= a b) (not (= (f a) (f b)))))
(check-sat)
; :status unsat
