(declare-const lower_bound Int)
(declare-const upper_bound Int)
(declare-const soln Int)

(assert (= lower_bound 100))
(assert (= upper_bound 5000))

(assert (<= lower_bound soln upper_bound))
(assert (exists ((x Int)) (= (* x x) soln)))

(check-sat)
(get-model)
(exit)
