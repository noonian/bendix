(ns bendix.smoke
  "Runtime-stable facts about the simplifier, the same on the JVM, on
  Jolt and in ClojureScript: results whose cost is a unique minimum,
  class and node counts, iterations, stop reasons, per-rule counts,
  and bendix.num's exact numbers printed and read back. Never a class
  id and never a tied term (cromulent.smoke says why). `checks` is
  plain data: bendix.smoke-test asserts it under clojure.test, and
  orrery's node build and browser self-test run it."
  (:require [bendix.algebra :as alg]
            [bendix.core :as bx :refer [simplify differentiate]]
            [bendix.exponent :as ex]
            [bendix.num :as num]
            [bendix.rules :as rules]
            [cromulent.core :as eg]
            [cromulent.rewrite :as rw]))

(def s2 [:expt [:sin :x] 2])
(def c2 [:expt [:cos :x] 2])

(defn sum-of
  "A left-nested sum of n distinct atoms, lesson 7's term."
  [n]
  (reduce (fn [acc i] [:+ acc (keyword (str "a" i))]) :a0 (range 1 n)))

(def ac-rules
  [(rw/rule "comm" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "assoc" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])])

(defn- result [t opts] (:result (simplify t opts)))

(defn- check [name expected actual]
  {:name name :expected expected :actual actual :ok? (= expected actual)})

(defn checks
  "One {:name :expected :actual :ok?} per fact."
  []
  (let [half (num/div 1 2)
        fix (let [g (bx/egraph)
                  [g r] (eg/add g (sum-of 5))
                  g (eg/rebuild g)
                  [g2 r2] (eg/add g [:+ :a4 [:+ :a3 [:+ :a2 [:+ :a1 :a0]]]])
                  g2 (eg/rebuild g2)
                  res (rw/embiggen g ac-rules {:scheduler :simple :iter-limit 12 :node-limit 5000})]
              {:sum [(eg/class-count g) (eg/node-count g)]
               :arrangement [(eg/class-count g2) (eg/node-count g2) (= (eg/find g2 r) (eg/find g2 r2))]
               :ac [(:iterations res) (:stop-reason res)
                    (eg/class-count (:egraph res)) (eg/node-count (:egraph res))
                    (mapv :applied (:stats res))]})
        trig (bx/saturate [:+ [:+ [:+ :a s2] c2] :b] {:rules rules/trig})
        d (differentiate [:sin [:* 2 :x]] :x)]
    [(check "like terms collect: 2x + 3x" [:* 5 :x] (result [:+ [:* 2 :x] [:* 3 :x]] {}))
     (check "5x costs 3 under the default cost, saturated"
            [3 :saturated] (let [r (simplify [:+ [:* 2 :x] [:* 3 :x]])] [(:cost r) (:stop r)]))
     (check "(x + 1)(x − 1): the expansion is smaller" [:+ [:expt :x 2] -1] (result [:* [:+ :x 1] [:- :x 1]] {}))
     (check "(x + y)²: the factored form is smaller" [:expt [:+ :x :y] 2] (result [:expt [:+ :x :y] 2] {}))
     (check "sin x + sin x: an opaque atom collects" [:* 2 [:sin :x]] (result [:+ [:sin :x] [:sin :x]] {}))
     (check "y·y pays for the repeated base" [:expt :y 2] (result [:* :y :y] {}))
     (check "x/2 is (1/2)·x, exact" [:* half :x] (result [:/ :x 2] {}))
     (check "1/2 prints as written" "[:* 1/2 :x]" (pr-str (result [:/ :x 2] {})))
     (check "1/2 reads back exact" [:* half :x] (num/read-string "[:* 1/2 :x]"))
     (check "1/2 + 1/3" (num/div 5 6) (num/add half (num/div 1 3)))
     (check "sin²x + cos²x buried in a sum" [:+ :a :b 1] (result [:+ [:+ [:+ :a s2] c2] :b] {:rules rules/trig}))
     (check "1 − cos²x" s2 (result [:- 1 c2] {:rules rules/trig}))
     (check "the pair with a cofactor" :y (result [:+ [:* :y s2] [:* :y c2]] {:rules rules/trig}))
     (check "pythagoras applied per iteration"
            [{"pythagoras" 5} {"pythagoras" 2} {"pythagoras" 0}] (mapv :applied (:stats trig)))
     (check "the trig run: iterations, stop, classes, nodes"
            [3 :saturated 15 22]
            [(:iterations trig) (:stop-reason trig) (eg/class-count (:egraph trig)) (eg/node-count (:egraph trig))])
     (check "exp(x/2)·exp(x/2) under exp-log"
            [:exp :x] (result [:* [:exp [:* half :x]] [:exp [:* half :x]]] {:rules rules/exp-log}))
     (check "the fix: five atoms under the analysis" [9 9] (:sum fix))
     (check "another arrangement lands in the same class" [9 13 true] (:arrangement fix))
     (check "commutativity and associativity merge nothing under the analysis"
            [1 :saturated 12 19 [{"comm" 0 "assoc" 0}]] (:ac fix))
     (check "d/dx sin 2x" [:* 2 [:cos [:* 2 :x]]] (:result d))
     (check "its cost under no-D, as doubles" [0.0 6.015625] (mapv num/->double (:cost d)))
     (check "nothing undifferentiated, saturated" [#{} :saturated] [(:undifferentiated d) (:stop d)])
     (check "the product rule is polynomial calculus"
            [:+ [:* :x [:cos :x]] [:sin :x]] (:result (differentiate [:* :x [:sin :x]] :x)))
     (check "no rule for abs: the derivative stays and says so"
            #{[:D [:abs :x] :x]} (:undifferentiated (differentiate [:* :x [:abs :x]] :x)))
     (check "a rational exponent" [:* half [:expt :x (num/div -1 2)]] (:result (differentiate [:expt :x half] :x)))
     (check "a Boolean atom over GF(2): x·x is x"
            :x (result [:* :x :x] {:algebra (alg/gf2 1) :exponent-laws (constantly ex/idempotent)}))
     (check "x or y in algebraic normal form"
            [:+ [:* :x :y] :x :y]
            (result [:+ [:* [:+ :x 1] [:+ :y 1]] 1] {:algebra (alg/gf2 1) :exponent-laws (constantly ex/idempotent)}))
     (check "an atom ranging over GF(4): x⁴ is x"
            :x (result [:expt :x 4] {:algebra (alg/gf2 2) :exponent-laws (constantly (ex/field-element 4))}))
     (check "a cube root of unity: w⁻² is w"
            :w (result [:expt :w -2] {:algebra (alg/gf2 2) :exponent-laws {:w (ex/root-of-unity 3)}}))]))
