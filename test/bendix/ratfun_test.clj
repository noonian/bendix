(ns bendix.ratfun-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.num :as num]
            [bendix.poly :as p]
            [bendix.ratfun :as rf]
            [bendix.ratfun-analysis :as ra]
            [cromulent.check :as check]
            [cromulent.core :as eg]))

(def x (p/variable :x))
(def y (p/variable :y))

(deftest exact-division
  (is (= (p/add x y) (p/divide (p/sub (p/mul x x) (p/mul y y)) (p/sub x y))))
  (is (nil? (p/divide (p/add (p/mul x x) (p/constant 1)) (p/add x (p/constant 1)))))
  (is (= (p/scale y 1/2) (p/divide (p/mul x y) (p/scale x 2))) "by a monomial")
  (is (nil? (p/divide x y)))
  (is (nil? (p/divide x p/zero)))
  (is (= p/zero (p/divide p/zero x)))
  (let [a (p/sum [(p/mul x x) (p/scale y 3) (p/constant 1)]), b (p/sub (p/mul x y) (p/constant 2))]
    (is (= a (p/divide (p/mul a b) b)))
    (is (= b (p/divide (p/mul a b) a)))))

(defn- form [t]
  (let [g (ra/egraph)
        [g id] (eg/add g t)]
    (ra/form (eg/rebuild g) id)))

(deftest normal-forms
  (testing "a sum of fractions over a common denominator"
    (is (= (form [:/ [:+ :x :y] [:* :x :y]]) (form [:+ [:/ 1 :x] [:/ 1 :y]]))))
  (testing "partial fractions: 1/(AB) = 1/(B − A) · (1/A − 1/B)"
    (is (= (form [:/ 1 [:* :x :y]])
           (form [:* [:/ 1 [:- :y :x]] [:- [:/ 1 :x] [:/ 1 :y]]]))))
  (testing "cancellation"
    (is (= (form [:+ :x 1]) (form [:/ [:- [:expt :x 2] 1] [:- :x 1]])))
    (is (= (form 1) (form [:* [:sin :x] [:/ 1 [:sin :x]]])) "an opaque atom cancels too"))
  (testing "a factor's scalar and monomial content are split off"
    (let [f (form [:/ 1 [:- [:* 2 :x :y] [:* 2 :y :y]]])]
      (is (= #{(p/variable :y) (p/sub x y)} (set (keys (:den f)))))
      (is (= (p/constant 1/2) (:num f)))))
  (testing "a product inverted whole keeps its factors (the hint)"
    (let [f (form [:/ 1 [:* [:+ :x :y] [:- :x :y]]])]
      (is (= 2 (count (:den f))))
      (is (= f (form [:- [:/ 1 [:* [:+ :x :y] [:- :x :y]]] 0])))
      (is (= f (form (rf/->term f))))))
  (testing "powers"
    (is (= (form [:/ 1 [:* :x :x]]) (form [:expt :x -2])))
    (is (= (form [:expt [:+ :x 1] 3]) (form [:* [:+ :x 1] [:+ 1 :x] [:+ :x 1]]))))
  (testing "division by zero and a symbolic power are opaque"
    (is (ra/atom? (form [:/ 1 [:- :x :x]])))
    (is (ra/atom? (form [:expt :x :y])))))

(deftest the-index-merges-spellings
  (let [g (ra/egraph)
        [g a] (eg/add g [:/ 1 [:* :x :y]])
        [g b] (eg/add g [:* [:/ 1 [:- :y :x]] [:- [:/ 1 :x] [:/ 1 :y]]])
        [g c] (eg/add g [:/ 2 [:* :x :y]])
        g (eg/rebuild g)]
    (is (empty? (check/violations g)))
    (is (nil? (ra/inconsistency g)))
    (is (= (eg/find g a) (eg/find g b)))
    (is (not= (eg/find g a) (eg/find g c)))))

;; ---------------------------------------------------------------------------
;; properties against exact evaluation

(def gen-term
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/fmap #(into [:+] %) (gen/vector inner 2 3))
                  (gen/fmap #(into [:*] %) (gen/vector inner 2 3))
                  (gen/fmap (fn [[a b]] [:- a b]) (gen/tuple inner inner))
                  (gen/fmap (fn [[a b]] [:/ a b]) (gen/tuple inner inner))
                  (gen/fmap (fn [[a e]] [:expt a e]) (gen/tuple inner (gen/choose -2 2)))]))
   (gen/one-of [(gen/elements [:x :y :z]) (gen/choose -3 3)])
   ))

(defn- value
  "t at env, exactly; nil where a division by zero occurs."
  [t env]
  (cond
    (keyword? t) (env t)
    (number? t) t
    :else
    (let [[op & args] t, vs (map #(value % env) args)]
      (when (every? some? vs)
        (case op
          :+ (reduce num/add vs)
          :* (reduce num/mul vs)
          :- (num/sub (first vs) (second vs))
          :/ (when-not (zero? (second vs)) (num/div (first vs) (second vs)))
          :expt (let [[b e] vs]
                  (cond (not (neg? e)) (num/expt b e)
                        (zero? b) nil
                        :else (num/div 1 (num/expt b (- e))))))))))

(def points [{:x 2 :y 5 :z -3} {:x 7/3 :y -1 :z 11} {:x -4 :y 13/2 :z 3}])

(defn- free?
  "Is f a form over the variables alone, with no opaque class in it
  (x/0 is opaque)?"
  [f]
  (and (rf/ratfun? f) (every? keyword? (rf/atoms f))))

(deftest the-form-is-the-function
  (let [r (tc/quick-check 300
            (prop/for-all [t gen-term]
              (let [f (form t)]
                (or (not (free? f))
                    (every? (fn [env]
                              (let [v (value t env), w (rf/evaluate f env)]
                                ;; t may divide by zero at a point where its
                                ;; normal form does not (x/x at x = 0)
                                (or (nil? v) (= v w))))
                            points)))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

(deftest the-form-is-canonical
  (let [r (tc/quick-check 200
            (prop/for-all [t gen-term, u gen-term]
              (let [f (form t), fu (form u)]
                (or (not (free? f)) (not (free? fu)) (rf/zero? fu)
                    (and (rf/same-function? f (form (rf/->term f)))
                         (rf/same-function? f (form [:/ [:* t u] u]))
                         (rf/same-function? f (form [:- [:+ t u] u])))))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

(defn- form-after
  "The form of t in an e-graph that already holds the terms before."
  [before t]
  (let [g (reduce (fn [g b] (first (eg/add g b))) (ra/egraph) before)
        [g id] (eg/add g t)]
    (ra/form (eg/rebuild g) id)))

(deftest a-form-does-not-depend-on-what-came-first
  (let [t [:/ 1 [:* [:+ :x :y] [:- :x :y]]]
        alone (form t)
        after (form-after [[:- [:* :x :x] [:* :y :y]]] t)]
    (is (= alone after) "the product's factors survive meeting x² − y²")
    (is (= 2 (count (:den after)))))
  (testing "spellings of one function whose factors share a root"
    (is (rf/same-function? (form [:/ 1 [:+ :x :y]]) (form [:/ [:- :x :y] [:- [:* :x :x] [:* :y :y]]])))
    (is (= (form [:/ 1 [:+ :x :y]]) (form [:/ [:- :x :y] [:- [:* :x :x] [:* :y :y]]])) "cancelled by the gcd")
    (let [g (ra/egraph)
          [g a] (eg/add g [:/ 1 [:- [:/ :x :y] [:/ :y :x]]])
          [g b] (eg/add g [:/ [:* :x :y] [:* [:- :x :y] [:+ :x :y]]])
          g (eg/rebuild g)]
      (is (= (eg/find g a) (eg/find g b)) "the index merges them")
      (is (nil? (ra/inconsistency g))))))

(deftest property-equal-keys-are-equal-functions
  (let [r (tc/quick-check 200
            (prop/for-all [t gen-term, u gen-term]
              (let [f (form t), fu (form u)]
                ;; sound: equal keys mean equal values wherever both are defined
                (or (not (free? f)) (not (free? fu))
                    (not (rf/same-function? f fu))
                    (every? (fn [env]
                              (let [v (rf/evaluate f env), w (rf/evaluate fu env)]
                                (or (nil? v) (nil? w) (= v w))))
                            points)))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

(deftest joining-two-splittings
  (let [x (rf/variable :x) y (rf/variable :y)
        a (rf/inverse (rf/sub (rf/mul x x) (rf/mul y y)))
        b (rf/inverse (rf/mul (rf/add x y) (rf/sub x y)))]
    (is (rf/same-function? a b))
    (is (not= a b))
    (is (= (rf/join a b) (rf/join b a) b) "the finer splitting, either way round")
    (is (not= 0 (rf/compare-ratfuns a b)) "the order tells the splittings apart")
    (is (= (rf/smaller a b) (rf/smaller b a)))))

(deftest a-denominator-proved-zero-is-not-too-big
  (let [g (ra/egraph)
        [g id] (eg/add g [:/ 1 [:- :x :y]])
        [g x] (eg/add g :x)
        [g y] (eg/add g :y)
        [g _] (eg/union g x y)
        g (eg/rebuild g)]
    (is (ra/atom? (ra/form g id)) "a division by zero: opaque, and free to take a definition later")))

(deftest a-large-power-gives-up-early
  (let [g (ra/egraph)
        [g id] (eg/add g [:expt [:+ :x :y :z 1] 80])
        t0 (System/currentTimeMillis)
        g (eg/rebuild g)]
    (is (= :too-big (ra/form g id)))
    (is (< (- (System/currentTimeMillis) t0) 10000))))

;; ---------------------------------------------------------------------------
;; division and gcd, against products built to have them

(def gen-poly
  (gen/fmap (fn [terms] (reduce p/add p/zero (map (fn [[m c]] {m c}) terms)))
            (gen/vector (gen/tuple (gen/fmap #(into {} (remove (comp zero? val)) %)
                                             (gen/map (gen/elements [:x :y :z]) (gen/choose 0 2)))
                                   (gen/elements [-3 -2 -1 1 2 3 1/2]))
                        1 3)))

(deftest property-division-undoes-multiplication
  (let [r (tc/quick-check 200
            (prop/for-all [a gen-poly, b gen-poly]
              (or (empty? b)
                  (and (= a (p/divide (p/mul a b) b))
                       (or (p/constant? b) (empty? a)
                           (nil? (p/divide (p/add (p/mul a b) (p/constant 1)) b))
                           (some? (p/divide (p/constant 1) b)))))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

(deftest property-the-gcd-divides-and-is-greatest
  (let [r (tc/quick-check 150
            (prop/for-all [a gen-poly, b gen-poly, c gen-poly]
              (or (empty? c) (empty? a) (empty? b)
                  (let [g (p/gcd (p/mul a c) (p/mul b c))]
                    (and (some? (p/divide (p/mul a c) g))
                         (some? (p/divide (p/mul b c) g))
                         (some? (p/divide g (p/monic c)))
                         (= 1 (p/leading-coefficient g)))))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

(deftest the-leading-term-is-multiplicative
  (let [r (tc/quick-check 200
            (prop/for-all [a gen-poly, b gen-poly]
              (or (empty? a) (empty? b)
                  (= (p/leading-term (p/mul a b))
                     (let [[ma ca] (p/leading-term a), [mb cb] (p/leading-term b)]
                       [(merge-with + ma mb) (num/mul ca cb)])))))]
    (is (:pass? r) (pr-str (:shrunk r)))))

;; ---------------------------------------------------------------------------
;; Laurent expansion

(defn- v-power [v k] (rf/expt (rf/variable v) k))

(defn- truncation-error
  "r minus its first n Laurent terms in v."
  [r v n at]
  (reduce (fn [acc [k c]] (rf/sub acc (rf/mul c (v-power v k)))) r (rf/laurent r v n at)))

(deftest laurent-expansion
  (let [x (rf/variable :x) y (rf/variable :y) d (rf/variable :d)
        c (fn [k] (rf/constant k))]
    (testing "1/(x − d) + 1/(y + d) at d = ∞: −(x + y)/d² + (y² − x²)/d³ + …"
      (let [r (rf/add (rf/inverse (rf/sub x d)) (rf/inverse (rf/add y d)))]
        (is (= [[-2 (rf/neg (rf/add x y))]
                [-3 (rf/sub (rf/mul y y) (rf/mul x x))]]
               (rf/laurent r :d 2)))
        (is (= [-2 (rf/neg (rf/add x y))] (rf/leading r :d)))))
    (testing "1/(1 − d) at d = 0: 1 + d + d² + …"
      (is (= [[0 rf/one] [1 rf/one] [2 rf/one]] (rf/laurent (rf/inverse (rf/sub rf/one d)) :d 3 :zero))))
    (testing "a pole at d = 0: (d² + x)/d is x/d + d"
      (is (= [[-1 x] [0 rf/zero] [1 rf/one]] (rf/laurent (rf/div (rf/add (rf/mul d d) x) d) :d 3 :zero))))
    (testing "a coefficient that is itself a rational function: d/(x·d + 1) → 1/x − 1/(x²d)"
      (is (= [[0 (rf/inverse x)] [-1 (rf/neg (rf/inverse (rf/mul x x)))]]
             (rf/laurent (rf/div d (rf/add (rf/mul x d) rf/one)) :d 2))))
    (testing "a bad n or point is refused, not looped on"
      (is (thrown? clojure.lang.ExceptionInfo (rf/laurent x :x -1)))
      (is (thrown? clojure.lang.ExceptionInfo (rf/laurent x :x 2 :inf))))
    (testing "zero has no terms"
      (is (= [] (rf/laurent rf/zero :d 3)))
      (is (nil? (rf/leading rf/zero :d))))
    (testing "what is left after n terms is of lower order than the last term kept"
      (doseq [r [(rf/div (rf/add (rf/mul d (rf/mul d d)) (rf/mul x y)) (rf/mul (rf/sub d x) (rf/add d (c 2))))
                 (rf/div (rf/sub (rf/mul x d) y) (rf/mul (rf/add (rf/mul d d) x) (rf/sub d y)))
                 (rf/add (rf/inverse (rf/sub x d)) (rf/inverse (rf/add (rf/mul (c 3) d) y)))
                 (rf/div (rf/add x d) (rf/mul (rf/mul d d) (rf/add rf/one (rf/mul y d))))]
              [at n] [[:infinity 4] [:zero 4]]
              :let [terms (rf/laurent r :d n at)
                    last-k (first (peek terms))
                    rest-r (truncation-error r :d n at)]]
        (is (or (rf/zero? rest-r)
                (if (= at :zero)
                  (< last-k (first (rf/leading rest-r :d :zero)))
                  (> last-k (first (rf/leading rest-r :d)))))
            (str at " " r))))))
