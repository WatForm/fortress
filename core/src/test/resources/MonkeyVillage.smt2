(declare-sort Tree 0)
(declare-sort Monkey 0)
(declare-sort Banana 0)

(declare-fun own (Monkey Banana) Bool)
(declare-fun b1 (Monkey) Banana)
(declare-fun b2 (Monkey) Banana)
(declare-fun sits (Monkey) Tree)
(declare-fun partner (Monkey) Monkey)

(assert (forall ((m Monkey)) (and (own m (b1 m)) (own m (b2 m)) (not (= (b1 m) (b2 m))))))
(assert (forall ((m1 Monkey) (m2 Monkey) (b Banana)) (=> (and (own m1 b) (own m2 b)) (= m1 m2))))
(assert (forall ((t Tree)) (exists ((m1 Monkey) (m2 Monkey) (m3 Monkey)) (and (= (sits m1) t) (= (sits m2) t) (= (sits m3) t) (distinct m1 m2 m3)))))
(assert (forall ((m1 Monkey) (m2 Monkey) (m3 Monkey) (m4 Monkey) (t Tree)) (=> (and (= (sits m1) t) (= (sits m2) t) (= (sits m3) t) (= (sits m4) t)) (not (distinct m1 m2 m3 m4)))))
(assert (forall ((m Monkey)) (and (not (= (partner m) m)) (= (partner (partner m)) m))))

(check-sat)