(ns bendix.core-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.core :as bx :refer [simplify]]
            [bendix.poly-test :refer [eval-term]]
            [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.export :as export]
            [cromulent.extract :as ex]))

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
  (is (= [:expt :y 2] (:result (simplify [:* :y :y]))) "a product that repeats a base pays for it")
  (is (= [:* [:expt :y 2] :z] (:result (simplify [:* :y :y :z]))) "even where the power is a node larger")
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

(defn size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(defn simplify-counting-repeats
  "`simplify` under the default cost, with :repeats: how many repeated
  bases t pays for as it is written (`bx/default-cost` less `bx/size`,
  in charges), in the saturated e-graph."
  [t opts]
  (let [{:keys [egraph root stop-reason]} (bx/saturate t opts)
        g (bx/materialize-all egraph)
        cost-fn (bx/default-cost g)
        {:keys [term cost]} (ex/extract g root cost-fn)]
    {:result term :cost cost :stop stop-reason
     :repeats (/ (- (bx/term-cost g cost-fn t) (bx/term-cost g bx/size t)) bx/repeated-base-charge)}))

(defn never-grows?
  "A result is no larger than what was written, but for one node for
  each repeated base it combined (IDEA.md section 6)."
  [t {:keys [result repeats]}]
  (<= (size result) (+ (size t) repeats)))

(deftest term-cost-is-the-cost-of-what-was-written
  (let [t [:* :a :y [:expt :y :n]]
        nested [:* [:* :a :y] [:expt :y :n]]
        g (bx/materialize-all (:egraph (bx/saturate [:+ t nested] {})))]
    (is (= 6 (bx/term-cost g bx/size t)))
    (is (= 8 (bx/term-cost g (bx/default-cost g) t)) "y and yⁿ share a base")
    (is (= 9 (bx/term-cost g (bx/default-cost g) nested)) "the charge sees through nesting")
    (is (= [0 8] (bx/term-cost g (bx/no-D g) t)))))

(deftest simplify-never-grows-and-its-cost-is-a-fixpoint
  (let [res (tc/quick-check
             200
             (prop/for-all [t term-gen]
               (let [{:keys [result cost] :as r} (simplify-counting-repeats t {:too-big 50})
                     again (simplify result {:too-big 50})]
                 (and (never-grows? t r)
                      (= cost (:cost again))))))]
    (is (:pass? res) (pr-str res))))

(deftest the-graph-behind-simplify-is-well-formed
  (let [res (tc/quick-check
             100
             (prop/for-all [t term-gen]
               (let [{:keys [egraph]} (bx/saturate t {:too-big 50})]
                 (empty? (check/violations (bx/materialize-all egraph))))))]
    (is (:pass? res) (pr-str res))))

;; ---------------------------------------------------------------------------
;; the export

(deftest the-export-carries-the-polynomials-as-class-data
  (let [[g id] (eg/add (bx/egraph) [:+ [:* 2 :x] [:* 3 :x]])
        d (bx/serialize g {:roots [id]})
        nodes (get d "nodes")
        data (get d "class_data")]
    (is (= [(str id)] (get d "root_eclasses")))
    (is (= {"type" "polynomial" "poly" "[:* 5 :x]"} (get data (str id))) "the sum's class is worth 5x")
    (is (= {"type" "polynomial" "poly" ":x"} (get data (str (eg/find g (eg/lookup g :x))))))
    (is (= {"type" "polynomial" "poly" "2"} (get data (str (eg/find g (eg/lookup g 2))))))
    (is (every? #(number? (get % "cost")) (vals nodes)) "every node has a cost under the default cost")
    (is (= 1 (get-in nodes [(str (eg/find g (eg/lookup g :x)) ".0") "cost"])))
    (is (= "{" (subs (export/->json d) 0 1)))
    (testing "an opaque class is an atom, and a polynomial over it names it #id"
      (let [[g id] (eg/add (bx/egraph) [:+ [:sin :x] [:sin :x]])
            d (bx/serialize g {:roots [id]})
            s (eg/find g (eg/lookup g [:sin (eg/lookup g :x)]))]
        (is (= {"type" "atom"} (get-in d ["class_data" (str s)])))
        (is (= {"type" "polynomial" "poly" (str "[:* 2 #" s "]")} (get-in d ["class_data" (str id)])))))))
