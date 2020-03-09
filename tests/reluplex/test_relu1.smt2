
; expect: unsat

(set-logic QF_LRA)

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
(assert (let ((ws (+ (* n_0_0 (- 1.318621)) (- 0.137526)))) (= n_1_0 (ite (>= ws 0) ws 0))))
;; Layer 2
(assert (let ((ws (+ (* n_1_0 0.743984) 2.197177))) (= n_2_0 ws)))

(check-sat)

