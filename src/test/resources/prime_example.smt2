(declare-const lower_bound Int)
(declare-const upper_bound Int)
(declare-const prime Int)

(assert (= lower_bound 2))
(assert (= upper_bound 100))

(assert (<= lower_bound prime upper_bound))
(assert
    (not
         (exists ((x Int) (y Int))
            (and
                (> x 1)
                (> y 1)
                (= (* x y) prime)
            )
        )
    )
)

(check-sat)
(get-model)
(exit)
