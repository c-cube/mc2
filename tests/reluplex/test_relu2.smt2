
; expect: unsat

(set-logic QF_LRA)

;; Declare the neuron variables
(declare-fun n_0_0 () Real)
(declare-fun n_1_0 () Real)
(declare-fun n_2_0 () Real)

;(define-fun relu ((x Real)) Real (ite (>= x 0) x 0))

;; Bound input ranges

(assert (<= n_0_0 1))

;; Goal

(assert (< n_2_0 0))

;; Declare the transition rules between neurons

;; Layer 1
(assert (= n_1_0 (relu n_0_0)))
;; Layer 2
(assert (= n_2_0 (+ n_1_0 2)))

(check-sat)

