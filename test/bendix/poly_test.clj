(ns bendix.poly-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.poly :as p]))

(def x (p/variable :x))
(def y (p/variable :y))
(def one (p/constant 1))

(deftest arithmetic-examples
  (is (= {} (p/add x (p/neg x))))
  (is (= {{:x 1} 2} (p/add x x)))
  (is (= {{:x 2} 1, {:x 1} 2, {} 1} (p/expt (p/add x one) 2)))
  (is (= {{:x 2} 1, {} -1} (p/mul (p/add x one) (p/sub x one))))
  (is (= one (p/expt x 0)))
  (is (= 0 (p/constant-value p/zero)))
  (is (= 3/2 (p/constant-value (p/constant 3/2))))
  (is (nil? (p/constant-value x)))
  (is (= 2 (p/degree (p/mul x y))))
  (is (= -1 (p/degree p/zero)))
  (is (= #{:x :y} (p/atoms (p/mul x y))))
  (is (= 7 (p/evaluate (p/add (p/mul x y) one) {:x 2 :y 3}))))

(deftest atoms-rename-and-combine
  (let [q (p/add (p/mul (p/variable 5) (p/variable 7)) (p/variable 5))]
    (is (= {{3 2} 1, {3 1} 1} (p/map-atoms {5 3, 7 3} q)) "5 and 7 both become 3: x3² + x3")
    (is (= q (p/map-atoms identity q)))))

(deftest term-rendering
  (is (= 0 (p/->term p/zero)))
  (is (= 1 (p/->term one)))
  (is (= :x (p/->term x)))
  (is (= [:* 2 :x] (p/->term (p/scale x 2))))
  (is (= [:+ [:expt :x 2] [:* 2 :x] 1] (p/->term (p/expt (p/add x one) 2))))
  (is (= [:+ [:* :x :y] 1/2] (p/->term (p/add (p/mul x y) (p/constant 1/2)))))
  (is (= [:* 2 [:sin :x]] (p/->term (p/scale (p/variable 9) 2) {9 [:sin :x]}))))

(deftest ordering
  (is (neg? (p/compare-polys x (p/add x one))) "fewer terms first")
  (is (neg? (p/compare-polys x (p/mul x x))) "then lower degree")
  (is (neg? (p/compare-polys x (p/scale x 1/2))) "then smaller coefficients by size: 1 before 1/2")
  (is (neg? (p/compare-polys x (p/scale x 3))) "and 1 before 3")
  (is (neg? (p/compare-polys (p/scale x -1) x)) "equal sizes fall back to value")
  (is (zero? (p/compare-polys x x)))
  (is (= x (p/smaller (p/add x one) x))))

(deftest substitution
  (is (= {{:a 2, :b 1} 1}
         (p/substitute (p/mul x y) {:x (p/variable :a), :y (p/mul (p/variable :a) (p/variable :b))}))
      "x·y with x := a, y := a·b")
  (is (= (p/expt (p/add x one) 2) (p/substitute (p/mul x x) {:x (p/add x one)})) "x² with x := x + 1")
  (is (= x (p/substitute x {:y one})) "an unmapped atom stays")
  (is (= (p/constant 8) (p/substitute (p/expt x 3) {:x (p/constant 2)})))
  (is (nil? (p/substitute (p/expt x 20) {:x (p/add x y)} 5)) "past the limit"))

(deftest linear-equations
  (is (= [:x 0] (p/linear-in-one-atom (p/scale x 1/2))))
  (is (= [:x -1] (p/linear-in-one-atom (p/add x one))))
  (is (= [:x 3/2] (p/linear-in-one-atom (p/sub (p/scale x 2) (p/constant 3)))))
  (is (nil? (p/linear-in-one-atom (p/add x y))) "two atoms")
  (is (nil? (p/linear-in-one-atom (p/mul x x))) "degree two")
  (is (nil? (p/linear-in-one-atom one)) "no atom")
  (is (nil? (p/linear-in-one-atom p/zero))))

;; ---------------------------------------------------------------------------
;; properties

(def atom-gen (gen/elements [:x :y :z]))
(def coeff-gen (gen/such-that (complement zero?)
                              (gen/one-of [gen/small-integer
                                           (gen/fmap #(/ % 3) gen/small-integer)])))
(def monomial-gen (gen/map atom-gen (gen/choose 1 3) {:max-elements 2}))
(def poly-gen (gen/fmap (fn [terms] (p/sum (map (fn [[m c]] {m c}) terms)))
                        (gen/vector (gen/tuple monomial-gen coeff-gen) 0 4)))
(def env-gen (gen/fmap #(merge {:x 0 :y 0 :z 0} %)
                       (gen/map atom-gen (gen/fmap #(/ % 5) gen/small-integer))))

;; Values are exact rationals or, once an exponential is involved,
;; Laurent polynomials in one indeterminate T over ℚ: maps from integer
;; exponent to non-zero rational coefficient, with exp v = T^v. A
;; constant Laurent polynomial is lowered back to the rational, so
;; terms without exponentials evaluate exactly as before.

(defn- lift [v] (cond (map? v) v (zero? v) {} :else {0 v}))

(defn- lower [m]
  (cond (empty? m) 0
        (and (= 1 (count m)) (contains? m 0)) (get m 0)
        :else m))

(defn- add-coefficient [m e c]
  (let [c' (+' (get m e 0) c)]
    (if (zero? c') (dissoc m e) (assoc m e c'))))

(defn- v+ [a b]
  (if (and (number? a) (number? b))
    (+' a b)
    (lower (reduce-kv add-coefficient (lift a) (lift b)))))

(defn- v* [a b]
  (if (and (number? a) (number? b))
    (*' a b)
    (lower (reduce-kv (fn [acc e1 c1]
                        (reduce-kv (fn [acc e2 c2] (add-coefficient acc (+ e1 e2) (*' c1 c2))) acc (lift b)))
                      {}
                      (lift a)))))

(defn- v-
  ([a] (v* -1 a))
  ([a b] (v+ a (v* -1 b))))

(defn- undefined [what data]
  (throw (ex-info what (assoc data :undefined true))))

(defn- v-expt [b e]
  (cond
    (not (integer? e)) (undefined "non-integer exponent" {:exponent e})
    (not (neg? e)) (reduce v* 1 (repeat e b))
    (number? b) (if (zero? b)
                  (undefined "negative power of zero" {})
                  (/ 1 (v-expt b (- e))))
    (= 1 (count b)) (let [[k c] (first b)]
                      (lower {(* k e) (/ 1 (reduce *' 1 (repeat (- e) c)))}))
    :else (undefined "negative power of a sum of exponentials" {:base b})))

(defn- v-exp [v]
  (if (integer? v) (lower {v 1}) (undefined "exp outside the model" {:argument v})))

(defn- v-log [v]
  (cond
    (= 1 v) 0
    (and (map? v) (= 1 (count v)) (= 1 (val (first v)))) (key (first v))
    :else (undefined "log outside the model" {:argument v})))

(defn- rational [v what]
  (if (number? v) v (undefined what {:argument v})))

(defn eval-term
  "Evaluate a term over the ring vocabulary under env, exactly. :sin
  and :cos are evaluated in the unit-circle model: for the argument's
  value v, sin = 2v/(1+v²) and cos = (1−v²)/(1+v²), a rational point
  on the circle, so sin² + cos² = 1 holds exactly and the identity
  rules can be checked by strict equality. :exp and :log are
  evaluated formally: exp v = T^v for an integer v, a Laurent
  polynomial in one indeterminate, and log T^v = v, so
  exp a · exp b = exp (a + b), exp 0 = 1 and log (exp v) = v hold
  exactly and no number ever grows. An exponent must evaluate to an
  integer; a negative power of zero, a non-integer exponent, exp of
  anything but an integer, log of anything but a power of T, and sin,
  cos or division of a value that mentions T throw ex-info with
  :undefined true, which a property treats as a point outside the
  domain."
  [t env]
  (cond
    (number? t) t
    (keyword? t) (get env t)
    :else (let [[op & args] t
                vs (map #(eval-term % env) args)]
            (case op
              :+ (reduce v+ vs)
              :* (reduce v* vs)
              :- (if (= 1 (count vs)) (v- (first vs)) (reduce v- vs))
              :neg (v- (first vs))
              :expt (v-expt (first vs) (second vs))
              :/ (v* (first vs) (/ 1 (rational (second vs) "division by an exponential")))
              :sin (let [v (rational (first vs) "sin of an exponential")] (/ (*' 2 v) (+' 1 (*' v v))))
              :cos (let [v (rational (first vs) "cos of an exponential")] (/ (-' 1 (*' v v)) (+' 1 (*' v v))))
              :exp (v-exp (first vs))
              :log (v-log (first vs))))))

(defn- canonical? [q]
  (and (every? (complement zero?) (vals q))
       (every? (fn [m] (every? pos? (vals m))) (keys q))))

(deftest arithmetic-is-a-ring-homomorphism
  (let [res (tc/quick-check
             200
             (prop/for-all [a poly-gen, b poly-gen, c poly-gen, n (gen/choose 0 3), env env-gen]
               (let [ev #(p/evaluate % env)]
                 (and (= (+' (ev a) (ev b)) (ev (p/add a b)))
                      (= (*' (ev a) (ev b)) (ev (p/mul a b)))
                      (= (-' (ev a)) (ev (p/neg a)))
                      (= (-' (ev a) (ev b)) (ev (p/sub a b)))
                      (= (reduce *' 1 (repeat n (ev a))) (ev (p/expt a n)))
                      (= (p/add a b) (p/add b a))
                      (= (p/mul a b) (p/mul b a))
                      (= (p/add (p/add a b) c) (p/add a (p/add b c)))
                      (= (p/mul (p/mul a b) c) (p/mul a (p/mul b c)))
                      (= (p/mul a (p/add b c)) (p/add (p/mul a b) (p/mul a c)))
                      (= p/zero (p/sub a a))
                      (= a (p/add a p/zero))
                      (= a (p/mul a one))
                      (every? canonical? [(p/add a b) (p/mul a b) (p/sub a b) (p/expt a n)])))))]
    (is (:pass? res) (pr-str res))))

(deftest rendered-terms-evaluate-to-the-polynomial
  (let [res (tc/quick-check
             200
             (prop/for-all [a poly-gen, env env-gen]
               (= (p/evaluate a env) (eval-term (p/->term a) env))))]
    (is (:pass? res) (pr-str res))))

(deftest substitution-is-a-homomorphism
  (let [res (tc/quick-check
             100
             (prop/for-all [a poly-gen, sx poly-gen, sy poly-gen, env env-gen]
               (let [env' (assoc env :x (p/evaluate sx env) :y (p/evaluate sy env))]
                 (= (p/evaluate a env')
                    (p/evaluate (p/substitute a {:x sx :y sy}) env)))))]
    (is (:pass? res) (pr-str res))))

(deftest compare-is-a-total-order
  (let [res (tc/quick-check
             200
             (prop/for-all [a poly-gen, b poly-gen, c poly-gen]
               (let [sgn #(cond (neg? %) -1 (pos? %) 1 :else 0)
                     ab (sgn (p/compare-polys a b)), ba (sgn (p/compare-polys b a))]
                 (and (= ab (- ba))
                      (= (zero? ab) (= a b))
                      (let [ac (sgn (p/compare-polys a c)), bc (sgn (p/compare-polys b c))]
                        (if (and (neg? ab) (neg? bc)) (neg? ac) true))))))]
    (is (:pass? res) (pr-str res))))
