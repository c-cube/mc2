(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)
;;(declare-fun z () Real)
;;(assert (< z 0))
;;(assert (>= (relu z) 0))

;; Declare the neuron variables
(declare-fun n_0_0 () Real)
(declare-fun n_1_0 () Real)
(declare-fun n_2_0 () Real)

;; Bound input ranges

(assert (>= n_0_0 0))
(assert (<= n_0_0 1))

;; Goal

(assert (< n_2_0 0))

;; Declare the transition rules between neurons

;; Layer 1
(assert (= n_1_0 (relu n_0_0 )))
;; Layer 2
(assert (= n_2_0 (relu (+ n_1_0 1))))

(check-sat)
(exit)
