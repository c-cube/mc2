(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
(declare-fun z () Real)
(declare-fun x () Real)
(assert (> z 0))
(assert (= x (ite (>= z 0) z 0)))
(assert (>= x 0))






(check-sat)
(exit)
