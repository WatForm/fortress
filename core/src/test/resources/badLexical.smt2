␡
(declare-sort A 0) (declare-sort B 0)
(declare-const x A)
(declare-const y B)
(declare-fun p (A B) Bool)
(assert (p x y))
(check-sat)
(exit)
