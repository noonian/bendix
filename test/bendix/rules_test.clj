(ns bendix.rules-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.core :as bx :refer [simplify]]
            [bendix.poly :as p]
            [bendix.poly-test :refer [eval-term]]
            [bendix.rules :as rules]
            [cromulent.check :as check]
            [cromulent.core :as eg]))

(defn- simp [t] (:result (simplify t {:rules rules/trig})))

(def s2 [:expt [:sin :x] 2])
(def c2 [:expt [:cos :x] 2])

(deftest reduce-square
  (let [s (p/variable :s), c (p/variable :c)
        one-minus-c2 (p/sub (p/constant 1) (p/mul c c))]
    (is (= (p/constant 1) (p/reduce-square (p/add (p/mul s s) (p/mul c c)) :s one-minus-c2)))
    (is (= (p/mul c c) (p/reduce-square (p/sub (p/constant 1) (p/mul s s)) :s one-minus-c2)))
    (is (= (p/mul s c) (p/reduce-square (p/mul s c) :s one-minus-c2)) "a first power is untouched")
    (is (= (p/mul s one-minus-c2) (p/reduce-square (p/expt s 3) :s one-minus-c2)) "s³ = s·(1 − c²)")
    (is (= (p/expt one-minus-c2 2) (p/reduce-square (p/expt s 4) :s one-minus-c2)))
    (is (= (p/variable :y) (p/reduce-square (p/variable :y) :s one-minus-c2)) "no s at all")
    (is (nil? (p/reduce-square (p/expt s 20) :s one-minus-c2 5)) "past the limit")))

(deftest render
  (is (= [[:+ [:expt '?4 2] '?7 1] {'?4 4 '?7 7}]
         (rules/render (p/add (p/add (p/expt (p/variable 4) 2) (p/variable 7)) (p/constant 1)))))
  (is (= [[:+ [:* -1 [:expt [:cos '?9] 2]] 1] {'?9 9}]
         (rules/render (p/sub (p/constant 1) (p/expt (p/variable [:cos 9]) 2))))
      "a placeholder renders as the node over the argument's class")
  (is (= [[:* '?2 [:expt '?1 [:+ '?3 '?4]]] {'?1 1 '?2 2 '?3 3 '?4 4}]
         (rules/render (p/mul (p/variable 2) (p/variable [:expt 1 [:+ 3 4]]))))
      "a placeholder may have several children, nested"))

(deftest textbook-trig
  (is (= 1 (simp [:+ s2 c2])))
  (is (= 1 (simp [:+ c2 s2])))
  (is (= [:+ :a :b 1] (simp [:+ [:+ [:+ :a s2] c2] :b])) "buried in a sum")
  (is (= [:+ :a :b 1] (simp [:+ [:+ :a c2] [:+ s2 :b]])) "and in another arrangement")
  (is (= :y (simp [:+ [:* :y s2] [:* :y c2]])) "with a cofactor")
  (is (= [:* 5 :x] (simp [:+ [:* [:+ [:* 2 :x] [:* 3 :x]] s2] [:* [:* 5 :x] c2]])) "collected first, then the identity")
  (is (= c2 (simp [:- 1 s2])))
  (is (= s2 (simp [:- 1 c2])) "the cosine of the graph exists; the sine is created by the rule")
  (is (= 1 (simp [:expt [:+ s2 c2] 3])) "the analysis expands the cube, the rule collapses it")
  (is (contains? #{[:+ [:* -2 c2] 1] [:+ [:* 2 s2] -1]}
                 (simp [:- [:expt [:sin :x] 4] [:expt [:cos :x] 4]]))
      "sin⁴ − cos⁴: either of the two canonical forms")
  (is (= 1 (simp [:+ [:expt [:sin [:+ :x :y]] 2] [:expt [:cos [:+ :y :x]] 2]]))
      "arguments are compared as classes: the analysis merged x + y and y + x")
  (is (= [:+ [:expt [:sin :y] 2] [:* 2 :a] 1]
         (simp [:+ [:+ [:+ :a s2] [:expt [:sin :y] 2]] [:+ c2 :a]]))
      "one pair collapses, another argument's lone sine stays")
  (is (= s2 (simp s2)) "a lone sin² stays: 1 − cos² is in the class but larger")
  (is (= [:sin :x] (simp [:sin :x])))
  (is (= [:* [:sin :x] [:cos :x]] (simp [:* [:sin :x] [:cos :x]])) "first powers: nothing to reduce"))

(deftest the-rule-saturates-quickly
  (let [t [:+ [:+ [:+ :a s2] c2] :b]
        {:keys [iterations stop-reason egraph]} (bx/saturate t {:rules rules/trig})]
    (is (= :saturated stop-reason))
    (is (<= iterations 3))
    (is (empty? (check/violations egraph)))
    (is (nil? (rules/trig-inconsistency egraph)))))

(deftest the-oracle-sees-outside-the-identity
  ;; sin²x + cos²x = 1 is inside the ideal; sin x = cos x is not
  (let [g (bx/egraph)
        [g s] (eg/add g [:expt [:sin :x] 2])
        [g c] (eg/add g [:- 1 [:expt [:cos :x] 2]])
        [g _] (eg/union g s c)
        g (eg/rebuild g)]
    (is (nil? (rules/trig-inconsistency g))))
  (let [g (bx/egraph)
        [g s] (eg/add g [:sin :x])
        [g c] (eg/add g [:cos :x])
        [g _] (eg/union g s c)
        g (eg/rebuild g)
        [g a] (eg/add g [:* 2 [:sin :x]])
        [g b] (eg/add g [:+ [:sin :x] [:cos :x]])
        g (eg/rebuild g)]
    (is (= (eg/find g a) (eg/find g b)) "the analysis merged 2·sin x and sin x + cos x")
    (is (nil? (rules/trig-inconsistency g)) "one form per class; nothing to compare"))
  (let [g (bx/egraph)
        [g a] (eg/add g [:* 2 [:sin :x]])
        [g b] (eg/add g [:+ [:sin :x] [:cos :x]])
        [g _] (eg/union g a b)
        g (eg/rebuild g)]
    (is (some? (rules/trig-inconsistency g)) "2·sin x = sin x + cos x is an assumption outside the identity")))

;; ---------------------------------------------------------------------------
;; experiment 4 as a property: O(n) nodes, whatever the arrangement

(def atoms [:a :b :c :d :e :f])

(defn- nested-sum [xs]
  (reduce (fn [acc a] [:+ acc a]) (first xs) (rest xs)))

(deftest buried-pair-in-any-arrangement
  (let [res (tc/quick-check
             100
             (prop/for-all [[n leaves] (gen/bind (gen/choose 1 6)
                                                 (fn [n] (gen/tuple (gen/return n)
                                                                    (gen/shuffle (conj (vec (take n atoms)) s2 c2)))))]
               (let [t (nested-sum leaves)
                     expected (into [:+] (conj (vec (take n atoms)) 1))
                     {:keys [result stop]} (simplify t {:rules rules/trig})
                     {:keys [egraph]} (bx/saturate t {:rules rules/trig})]
                 (and (= :saturated stop)
                      (= expected result)
                      (nil? (rules/trig-inconsistency egraph))
                      ;; the n + 2 leaves, the n + 1 sums written, the two trig atoms and
                      ;; their squares, plus the rendered forms of the classes that hold
                      ;; a square: a small constant per class, never 3^n
                      (<= (eg/node-count egraph) (+ (* 6 (+ n 2)) 12))))))]
    (is (:pass? res) (pr-str res))))

;; ---------------------------------------------------------------------------
;; the numeric oracle, on the unit circle

(def leaf-gen (gen/elements [:x :y 1 2 -1 1/2 [:sin :x] [:cos :x] [:sin :y] [:cos :y] [:sin [:+ :x :y]]]))

(def term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :+) inner inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :-) inner inner)
                  (gen/tuple (gen/return :neg) inner)
                  (gen/tuple (gen/return :expt) inner (gen/choose 0 4))]))
   leaf-gen))

(def env-gen (gen/fmap #(merge {:x 0 :y 0} %)
                       (gen/map (gen/elements [:x :y]) (gen/fmap #(/ % 7) gen/small-integer))))

(defn- size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(deftest simplify-with-trig-preserves-value-and-never-grows
  (let [res (tc/quick-check
             200
             (prop/for-all [t term-gen, env env-gen]
               (let [{:keys [result stop cost]} (simplify t {:rules rules/trig :too-big 50})
                     again (simplify result {:rules rules/trig :too-big 50})]
                 (and (= :saturated stop)
                      (= (eval-term t env) (eval-term result env))
                      (<= (size result) (size t))
                      (= cost (:cost again))))))]
    (is (:pass? res) (pr-str res))))

(deftest the-graph-behind-trig-is-well-formed-and-consistent
  (let [res (tc/quick-check
             100
             (prop/for-all [t term-gen]
               (let [{:keys [egraph]} (bx/saturate t {:rules rules/trig :too-big 50})
                     g (bx/materialize-all egraph)]
                 (and (empty? (check/violations g))
                      (nil? (rules/trig-inconsistency g))))))]
    (is (:pass? res) (pr-str res))))
