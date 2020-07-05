(set-info :smt-lib-version 2.6)

(declare-sort A 0)


(declare-fun x () A)
(declare-fun f (A A) Bool)
(declare-fun y () Bool)

(assert 
	(ite (f x x) (f x x) y))

(check-sat)