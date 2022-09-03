(set-info :smt-lib-version "2.6")
(set-info :status sat)
(set-info :category "toyExample")
(set-info :source |
This is just a test really.
|)
(set-logic UF)
(declare-sort A 0)
(declare-const x A)
(declare-const y A)
(declare-fun f (A A) Bool)
(assert (reflexive-closure f x y))
(check-sat)
(exit)
