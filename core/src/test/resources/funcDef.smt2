; test parsing function definition

(define-fun max ((x Int) (y Int)) Int
  (ite (< x y) y x))

(define-fun power2 ((x Int)) Bool
  (or (= x 8) (= x 4) (= x 2) (= x 1)))

