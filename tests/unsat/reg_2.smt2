
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f (Bool) U)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert
  (distinct (f a) (f b) (f c)))
(check-sat)
