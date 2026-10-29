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
                    (and (= f (form (rf/->term f)))
                         (= f (form [:/ [:* t u] u]))
                         (= f (form [:- [:+ t u] u])))))))]
    (is (:pass? r) (pr-str (:shrunk r)))))
