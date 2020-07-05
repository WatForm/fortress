(set-info :smt-lib-version 2.6)

(declare-sort A 0)


(declare-fun x () A)
(declare-fun f (A A) A)

(assert 
	(= (ite (= (f x x) x) x (f x x)) x))

(check-sat)