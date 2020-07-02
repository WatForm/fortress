(set-info :smt-lib-version "2.6")
(set-info :status sat)
(set-info :category "toyExample")
(set-info :source |
Testing $ at beginning of constant/function names.
|)
(set-logic UF)
(declare-sort A 0) 
(declare-const $x A)
(declare-fun $p (A A) Bool)
(assert ($p $x $x))
(check-sat)
(exit)
