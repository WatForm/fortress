; Asserts that two graphs have an isomorphism between them.
; This problem is satisfiable iff V1 and V2 have the same scope.
; It is slightly more interesting than a bijection between general sets since
; it must preserve the adjacency function.

; G1 and G2 are simple undirected graphs

(declare-sort V1 0) ; Vertices of graph G1
(declare-sort V2 0) ; Vertices of graph G2

(declare-fun adj1 (V1 V1) Bool) ; Adjacency relation for G1
(declare-fun adj2 (V2 V2) Bool) ; Adjacency relation for G2 

; G1 is loopless
(assert (forall ((v V1)) (not (adj1 v v))))
; G2 is loopless
(assert (forall ((v V2)) (not (adj2 v v))))

; G1 is undirected
(assert (forall ((u V1) (v V1)) (=> (adj1 u v) (adj1 v u))))
; G2 is undirected
(assert (forall ((u V2) (v V2)) (=> (adj2 u v) (adj2 v u))))

; f is an isomorphism from G1 to G2
(declare-fun f (V1) V2)
(assert (forall ((x V1) (y V1)) (=> (= (f x) (f y)) (= x y))))      ; Injective
(assert (forall ((y V2)) (exists ((x V1)) (= (f x) y))))            ; Surjective
(assert (forall ((u V1) (v V1)) (= (adj1 u v) (adj2 (f u) (f v))))) ; Preserves adjacency

(check-sat)
