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

(defn eval-term
  "Evaluate a term over the ring vocabulary under env, exactly. :sin
  and :cos are evaluated in the unit-circle model: for the argument's
  value v, sin = 2v/(1+v²) and cos = (1−v²)/(1+v²), a rational point
  on the circle, so sin² + cos² = 1 holds exactly and the identity
  rules can be checked by strict equality. An exponent must evaluate
  to an integer; a negative power of zero, or a non-integer exponent,
  throws ex-info with :undefined true, which a property treats as a
  point outside the domain."
  [t env]
  (cond
    (number? t) t
    (keyword? t) (get env t)
    :else (let [[op & args] t
                vs (map #(eval-term % env) args)]
            (case op
              :+ (reduce +' vs)
              :* (reduce *' vs)
              :- (if (= 1 (count vs)) (-' (first vs)) (reduce -' vs))
              :neg (-' (first vs))
              :expt (let [b (first vs), e (second vs)]
                      (cond
                        (not (integer? e)) (throw (ex-info "non-integer exponent" {:undefined true :exponent e}))
                        (neg? e) (if (zero? b)
                                   (throw (ex-info "negative power of zero" {:undefined true}))
                                   (/ 1 (reduce *' 1 (repeat (- e) b))))
                        :else (reduce *' 1 (repeat e b))))
              :/ (/ (first vs) (second vs))
              :sin (let [v (first vs)] (/ (*' 2 v) (+' 1 (*' v v))))
              :cos (let [v (first vs)] (/ (-' 1 (*' v v)) (+' 1 (*' v v))))))))

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
