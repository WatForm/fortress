(declare-sort vert 0)
(declare-sort colour 0)

(declare-fun edges (vert vert) Bool)
(declare-fun vcolour (vert) colour)

(assert (forall ((x vert) (y vert)) (= (not (= x y)) (edges x y))))
(assert (forall ((x vert) (y vert)) (=> (edges x y) (not (= (vcolour x) (vcolour y))))))

(check-sat)
(get-model)
(exit)
