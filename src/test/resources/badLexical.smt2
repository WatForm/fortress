␡
(declare-sort A) (declare-sort B)
(declare-const x A)
(declare-const y B)
(declare-fun p (A B) Bool)
(assert (p x y))
(check-sat)
(exit)
