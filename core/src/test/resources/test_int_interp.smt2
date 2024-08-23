(declare-fun notA (Int) Int)
(declare-const a Int)

(assert (forall ((x Int)) (not (= (notA x) a))))
(assert (> a 0))

(check-sat)