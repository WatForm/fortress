(set-info :smt-lib-version 2.6)

(declare-sort A 0)


(declare-fun x () A)
(declare-fun f (A A) A)

; let v_0=x in let v_1 = f(v_0,x) in let v_1=v_0 in f(v_0,v_1)=f(x,x)
; let v_0=x in let v_1 = f(v_0,x) in f(v_0,v_0)=f(x,x)
; let v_0=x in f(v_0,v_0)=f(x,x)
; f(x,x)=f(x,x)

(assert 
	(let ((?v_0 x)) 
		(let ((?v_1 (f ?v_0 x)))
			 (let ((?v_1 ?v_0))
			   (= (f ?v_0 ?v_1) (f x x))))))
(check-sat)