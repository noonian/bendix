(ns bendix.core-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.core :as bx :refer [simplify]]
            [bendix.poly-test :refer [eval-term]]
            [cromulent.check :as check]))

(deftest textbook
  (is (= [:* 5 :x] (:result (simplify [:+ [:* 2 :x] [:* 3 :x]]))))
  (is (= 0 (:result (simplify [:- :x :x]))))
  (is (= 7 (:result (simplify [:+ 1 [:* 2 3]]))))
  (is (= :x (:result (simplify [:* 1 [:+ :x 0]]))))
  (is (= [:+ [:expt :x 2] -1] (:result (simplify [:* [:+ :x 1] [:- :x 1]]))) "the expansion is smaller")
  (is (= [:expt [:+ :x :y] 2] (:result (simplify [:expt [:+ :x :y] 2]))) "the factored form is smaller")
  (is (= [:* 2 [:sin :x]] (:result (simplify [:+ [:sin :x] [:sin :x]]))))
  (is (= [:* 1/2 :x] (:result (simplify [:/ :x 2]))))
  (is (= [:/ :x :y] (:result (simplify [:/ :x :y]))) "division by a non-constant is opaque")
  (let [r (simplify [:+ [:* 2 :x] [:* 3 :x]])]
    (is (= 3 (:cost r)))
    (is (= :saturated (:stop r)))
    (is (= #{} (:assuming r)))))

;; ---------------------------------------------------------------------------
;; the numeric oracle

(def leaf-gen (gen/elements [:x :y 0 1 2 -1 1/2 3]))

(def term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :+) inner inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :-) inner inner)
                  (gen/tuple (gen/return :-) inner)
                  (gen/tuple (gen/return :neg) inner)
                  (gen/tuple (gen/return :expt) inner (gen/choose 0 3))
                  (gen/tuple (gen/return :/) inner (gen/elements [2 3 -4]))]))
   leaf-gen))

(def env-gen (gen/fmap #(merge {:x 0 :y 0} %)
                       (gen/map (gen/elements [:x :y]) (gen/fmap #(/ % 7) gen/small-integer))))

(deftest simplify-preserves-value
  (let [res (tc/quick-check
             200
             (prop/for-all [t term-gen, env env-gen]
               (let [{:keys [result stop]} (simplify t {:too-big 50})]
                 (and (= :saturated stop)
                      (= (eval-term t env) (eval-term result env))))))]
    (is (:pass? res) (pr-str res))))

(defn- size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(deftest simplify-never-grows-and-its-cost-is-a-fixpoint
  (let [res (tc/quick-check
             200
             (prop/for-all [t term-gen]
               (let [{:keys [result cost]} (simplify t {:too-big 50})
                     again (simplify result {:too-big 50})]
                 (and (<= (size result) (size t))
                      (= cost (:cost again))))))]
    (is (:pass? res) (pr-str res))))

(deftest the-graph-behind-simplify-is-well-formed
  (let [res (tc/quick-check
             100
             (prop/for-all [t term-gen]
               (let [{:keys [egraph]} (bx/saturate t {:too-big 50})]
                 (empty? (check/violations (bx/materialize-all egraph))))))]
    (is (:pass? res) (pr-str res))))
