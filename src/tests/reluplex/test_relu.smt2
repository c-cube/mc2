(set-info :smt-lib-version 2.6)
(set-logic QF_UFLRA)

;; Declare the neuron variables
(declare-fun n_0_0 () Real)
(declare-fun n_1_0 () Real)
(declare-fun n_1_1 () Real)
(declare-fun n_2_0 () Real)
(declare-fun n_2_1 () Real)
(declare-fun n_2_2 () Real)
(declare-fun n_2_3 () Real)
(declare-fun n_3_0 () Real)

;; Bound input ranges


;; Goal


;; Declare the transition rules between neurons

;; Layer 1
(assert (let ((ws (- n_0_0 1))) (relu ws n_1_0)))
(assert (let ((ws (- n_0_0 1))) (relu ws n_1_1)))
;; Layer 2
(assert (let ((ws (+ n_1_0 n_1_1))) (relu ws n_2_0)))
(assert (let ((ws (+ n_1_0 n_1_1))) (relu ws n_2_1)))
(assert (let ((ws (+ n_1_0 n_1_1 (- 1)))) (relu ws n_2_2)))
(assert (let ((ws (+ n_1_0 n_1_1 ))) (relu ws n_2_3)))
;; Layer 3
(assert (let ((ws (+ n_2_0 (* n_2_1 (- 2)) (* n_2_2 (- 1)) n_2_3 2))) (= n_3_0 ws)))


(check-sat)
(exit)