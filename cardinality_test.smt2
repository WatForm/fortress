(set-logic UF)

;; Declare sorts
(declare-sort Car 0)                  ;; The sort representing different car models
(declare-sort CarDealership 0)        ;; The sort representing car dealerships

;; Declare constants for car models
(declare-const sedan Car)
(declare-const suv Car)
(declare-const truck Car)

;; Declare constants for dealerships
(declare-const dealer1 CarDealership)
(declare-const dealer2 CarDealership)

;; Declare a predicate to represent cars available at a dealership
(declare-fun hasCar (CarDealership Car) Bool)

;; Axiom: There are exactly 3 car models in this model
(assert (= (cardinality hasCar) 3))

(check-sat)
