(assert (= (+ 1 2 3) 6))
(assert (= (- 10 2 3) 5))
(assert (= (- 3) (- 3)))
(assert (= (* 5 3 4) 60))
(assert (= (div 60 3 2) 10))
(assert (= (mod 10 3) 1))
(assert (<= 1 3 3 4 4 6))
(assert (< 1 2 3 4 5 6))
(assert (>= 6 4 4 3 3 1))
(assert (> 6 5 4 3 2 1))
(check-sat)
(exit)