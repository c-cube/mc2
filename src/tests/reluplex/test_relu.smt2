(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (relu x y))



(check-sat)
(exit)
