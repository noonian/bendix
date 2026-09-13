(ns bendix.term-test
  (:require [clojure.test :refer [deftest is]]
            [bendix.core :as bx]
            [bendix.term :as bt]
            [cromulent.core :as eg]))

(deftest vocabulary
  (is (bt/variable? :x))
  (is (not (bt/variable? 2)))
  (is (bt/constant? 2))
  (is (bt/constant? 1/2))
  (is (not (bt/constant? :x)))
  (is (not (bt/constant? 0.5)) "floats are not exact")
  (is (bt/class-id? 7))
  (is (not (bt/class-id? :x)))
  (is (bt/placeholder? [:cos 7]))
  (is (not (bt/placeholder? 7))))

(deftest placeholders
  (let [p (bt/placeholder :expt [(bt/class-ref 3) (bt/placeholder :+ [2 (bt/class-ref 4)])])]
    (is (= [:expt {:class 3} [:+ 2 {:class 4}]] p))
    (is (= #{3 4} (bt/class-ids p)) "the constant 2 is not an id")
    (is (= [:expt "3" [:+ 2 "4"]] (bt/map-class-ids str p)))
    (is (= [:sin {:class 9}] (bt/placeholder :sin [(bt/class-ref 9)])))
    (is (bt/placeholder? p))
    (is (bt/class-ref? (bt/class-ref 3)))
    (is (not (bt/class-ref? 3)))))

(deftest reading-classes
  (let [g (bx/egraph)
        [g s] (eg/add g [:sin :x])
        [g x] (eg/add g :x)
        [g c] (eg/add g [:cos :x])
        [g _] (eg/union g s c)
        g (eg/rebuild g)]
    (is (= [:sin x] (bt/node-with g s :sin)))
    (is (= [:cos x] (bt/node-with g s :cos)) "the merged class holds both")
    (is (nil? (bt/node-with g s :exp)))
    (is (= [[:cos x] [:sin x]] (bt/nodes-with g s #{:sin :cos})) "in node order")
    (is (= [] (bt/nodes-with g x #{:sin :cos})) "a variable holds no compound node")))
