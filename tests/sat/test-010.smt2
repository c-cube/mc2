(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
(assert (and (= a b) (= b c) (or (not (= a c)) (= a d))))
(check-sat)
; :status sat
