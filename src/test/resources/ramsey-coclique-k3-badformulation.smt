; An incorrect formulation of Ramsey's theorem for k = 3.

(declare-sort V)             ; vertex set
(declare-fun adj (V V) Bool) ; adjacency relation
(assert (forall ((u V) (v V)) (= (adj u v) (adj v u)))) ; G is undirected
(assert (forall ((u V)) (not (adj u u))))               ; G is loopless (not strictly necessary)

(assert (not (exists ((x1 V) (x2 V) (x3 V)) (and 
    (distinct x1 x2 x3)
    (= 
        (adj x1 x2)
        (adj x2 x3))))))

(check-sat)
