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
  (let [p (bt/placeholder :expt [3 [:+ 4 5]])]
    (is (= [:expt 3 [:+ 4 5]] p))
    (is (= #{3 4 5} (bt/class-ids p)))
    (is (= [:expt "3" [:+ "4" "5"]] (bt/map-class-ids str p)))
    (is (= [:sin 9] (bt/placeholder :sin [9])))))

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
