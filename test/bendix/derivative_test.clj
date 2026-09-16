(ns bendix.derivative-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.analysis :as an]
            [bendix.core :as bx :refer [differentiate simplify]]
            [bendix.poly-test :refer [eval-term]]
            [bendix.rules :as rules]
            [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.rewrite :as rw]))

(defn- d
  ([t] (d t {}))
  ([t opts] (:result (differentiate t :x opts))))

(defn- same-class?
  "Do a and b land in one class when saturated together under rules?"
  [rules a b]
  (let [g (bx/egraph)
        [g ia] (eg/add g a)
        [g ib] (eg/add g b)
        {:keys [egraph]} (rw/embiggen g rules {})]
    (= (eg/find egraph ia) (eg/find egraph ib))))

(def all (-> [] (into rules/trig) (into rules/powers) (into rules/exp-log)))

(deftest textbook-polynomials
  (is (= 2 (d [:+ [:* 2 :x] 3])))
  (is (= [:* 3 [:expt :x 2]] (d [:expt :x 3])))
  (is (= :y (d [:* :x :y])) "y is held constant")
  (is (= 0 (d 5)))
  (is (= 0 (d :y)))
  (is (= 1 (d :x)))
  (is (= [:* 2 :x] (d [:+ [:expt :x 2] [:expt :y 2]])))
  (is (= 1/2 (d [:/ :x 2])) "division by a constant is a ring operation")
  (is (= [:* 3 [:expt [:+ :x 1] 2]] (d [:expt [:+ :x 1] 3])) "the power rule's factored spelling beats the expansion"))

(deftest textbook-chain-rules
  (is (= [:* 2 [:cos [:* 2 :x]]] (d [:sin [:* 2 :x]])))
  (is (= [:* -1 [:sin :x]] (d [:cos :x])))
  (is (= [:* 2 [:exp [:* 2 :x]]] (d [:exp [:* 2 :x]])))
  (is (= [:expt :x -1] (d [:log :x])))
  (is (= [:* [:exp [:sin :x]] [:cos :x]] (d [:exp [:sin :x]])))
  (is (= [:* 2 :x [:cos [:+ [:expt :x 2] 1]]] (d [:sin [:+ [:expt :x 2] 1]])))
  (is (= [:* 2 [:sin :x] [:cos :x]] (d [:expt [:sin :x] 2])) "a folded square: the ring differentiates it")
  (is (= [:* 5 [:expt [:sin :x] 4] [:cos :x]] (d [:expt [:sin :x] 5])) "in one step, not five product rules")
  (is (= [:+ [:* :x [:cos :x]] [:sin :x]] (d [:* :x [:sin :x]])) "the product rule is polynomial calculus")
  (is (= 1 (d [:log [:exp :x]] {:rules rules/exp-log})) "exp x · (exp x)⁻¹ under exp-log")
  (is (same-class? rules/derivative
                   (d [:sin [:sin [:sin :x]]])
                   [:* [:cos [:sin [:sin :x]]] [:cos [:sin :x]] [:cos :x]])
      "nested chain rules"))

(deftest textbook-quotients-and-powers
  (is (= [:* -1 [:expt :x -2]] (d [:/ 1 :x])))
  (is (= [:* -1 :x [:expt :y -2]] (:result (differentiate [:/ :x :y] :y))))
  (is (= [:* -2 [:expt [:+ :x -1] -2]] (d [:/ [:+ :x 1] [:- :x 1]])) "(x+1)/(x−1): the ring collects the numerator")
  (is (= [:* 1/2 [:expt :x -1/2]] (d [:expt :x 1/2])) "a rational exponent")
  (is (= [:* -1 [:expt :x -2]] (d [:expt :x -1])) "a negative exponent")
  (is (= [:* :n [:expt :x [:+ :n -1]]] (d [:expt :x :n])) "a symbolic exponent: the log term is a product with zero")
  (is (same-class? (into rules/derivative rules/powers)
                   (d [:expt :x :x] {:rules rules/powers})
                   [:+ [:expt :x :x] [:* [:expt :x :x] [:log :x]]])
      "x^x under powers"))

(deftest textbook-independence-and-leftovers
  (is (= [:pi] (d [:* [:pi] :x])) "a nullary operator cannot depend on x")
  (is (= [:abs :y] (d [:* :x [:abs :y]])) "an unknown operator of another variable")
  (is (= 0 (d [:sin :y])))
  (let [r (differentiate [:abs :x] :x)]
    (is (= [:D [:abs :x] :x] (:result r)) "no rule for abs: the derivative stays, honestly")
    (is (= #{[:D [:abs :x] :x]} (:undifferentiated r)))
    (is (= (bx/default-cost [:abs 0] [1]) (first (:cost r))) "the cost of what is under the :D"))
  (let [r (differentiate [:* :x [:abs :x]] :x)]
    (is (= [:+ [:* :x [:D [:abs :x] :x]] [:abs :x]] (:result r)) "pushed inward as far as the rules go")
    (is (= #{[:D [:abs :x] :x]} (:undifferentiated r))))
  (is (= [:+ [:* [:f :x] [:D [:g :x] :x]] [:* [:g :x] [:D [:f :x] :x]]] (d [:* [:f :x] [:g :x]]))
      "f'g + fg' for unknown f and g beats D(fg)")
  (is (= #{} (:undifferentiated (differentiate [:sin :x] :x)))))

(deftest higher-and-nested-derivatives
  (is (= [:* 6 :x] (d [:D [:expt :x 3] :x])) "the second derivative, as a nested :D")
  (is (= [:* 6 :x] (d (d [:expt :x 3]))) "or by calling twice")
  (is (= [:cos :y] (:result (differentiate [:D [:* :x [:sin :y]] :x] :y))) "a mixed partial")
  (is (= [:* 3 :x] (:result (simplify [:+ [:D [:expt :x 2] :x] :x] {:rules rules/derivative})))
      "a :D inside any term given to simplify"))

(deftest the-result-shape
  (let [r (differentiate [:sin [:* 2 :x]] :x)]
    (is (= :saturated (:stop r)))
    (is (= #{} (:assuming r)))
    (is (= 0 (first (:cost r)))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"variable" (differentiate :x 2)))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"variable" (differentiate :x [:sin :x]))))

(defn- depth [t] (if (vector? t) (inc (reduce max 0 (map depth (rest t)))) 0))

(deftest saturation-takes-at-most-depth-plus-two-iterations
  ;; one iteration per :D the rules create along the deepest path, one
  ;; more to see nothing changed
  (doseq [t [[:sin [:* 2 :x]]
             [:sin [:sin [:sin :x]]]
             [:D [:expt :x 3] :x]
             [:exp [:sin [:+ :x [:cos :x]]]]]]
    (let [{:keys [iterations stop-reason egraph]} (bx/saturate [:D t :x] {:rules rules/derivative})]
      (is (= :saturated stop-reason))
      (is (<= iterations (+ (depth t) 2)) (pr-str t))
      (is (empty? (check/violations egraph))))))

;; ---------------------------------------------------------------------------
;; the reference differentiator: textbook rules over the tree as written

(defn ref-D
  "d/dx t by the textbook rules, structurally. Exponents are numbers;
  log's derivative is spelled as a negative power so the formal model
  evaluates it."
  [t x]
  (cond
    (number? t) 0
    (keyword? t) (if (= t x) 1 0)
    :else
    (let [[op & args] t
          D #(ref-D % x)
          u (first args)]
      (case op
        :+ (into [:+] (map D args))
        :- (if (= 1 (count args)) [:neg (D u)] (into [:-] (map D args)))
        :neg [:neg (D u)]
        :* (into [:+] (map-indexed (fn [i _] (into [:*] (map-indexed (fn [j b] (if (= i j) (D b) b)) args))) args))
        :/ (let [[a b] args] [:* [:- [:* (D a) b] [:* a (D b)]] [:expt b -2]])
        :expt (let [[u n] args] [:* n [:expt u (dec n)] (D u)])
        :sin [:* [:cos u] (D u)]
        :cos [:* -1 [:sin u] (D u)]
        :exp [:* [:exp u] (D u)]
        :log [:* [:expt u -1] (D u)]))))

(deftest the-reference-agrees-on-the-textbook
  (is (= [:* [:cos [:* 2 :x]] [:+ [:* 0 :x] [:* 2 1]]] (ref-D [:sin [:* 2 :x]] :x)))
  (is (= [:* 3 [:expt :x 2] 1] (ref-D [:expt :x 3] :x))))

(defn- size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(defn- value
  "eval-term, or ::undefined outside the domain."
  [t env]
  (try (eval-term t env)
       (catch clojure.lang.ExceptionInfo e
         (if (:undefined (ex-data e)) ::undefined (throw e)))))

(def leaf-gen (gen/elements [:x :y 1 2 -1 1/2]))

(def trig-term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :+) inner inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :-) inner inner)
                  (gen/tuple (gen/return :neg) inner)
                  (gen/tuple (gen/return :expt) inner (gen/choose -2 3))
                  (gen/tuple (gen/return :/) inner (gen/elements [:x :y 2 [:+ :x 1]]))
                  (gen/tuple (gen/return :sin) inner)
                  (gen/tuple (gen/return :cos) inner)]))
   leaf-gen))

(def exp-term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :-) inner inner)
                  (gen/tuple (gen/return :expt) inner (gen/choose -1 3))
                  (gen/tuple (gen/return :exp) inner)
                  (gen/tuple (gen/return :log) (gen/tuple (gen/return :exp) inner))]))
   (gen/elements [:x :y 1 2 -1])))

(def env-gen (gen/fmap (fn [[x y]] {:x x :y y})
                       (gen/tuple (gen/fmap #(/ % 7) gen/small-integer) (gen/fmap #(/ % 7) gen/small-integer))))

(def int-env-gen (gen/fmap (fn [[x y]] {:x x :y y}) (gen/tuple (gen/choose -2 3) (gen/choose -2 3))))

(defn- agrees-with-the-reference?
  "differentiate t is complete, saturated, lands in the reference's
  class under rules, and agrees with it numerically wherever the
  reference is defined; and its cost is a fixpoint."
  [t env rules]
  (let [{:keys [result stop cost undifferentiated]} (differentiate t :x {:rules rules :too-big 50})
        r (ref-D t :x)
        v (value r env)
        again (simplify result {:rules (into rules/derivative rules) :cost bx/no-D :too-big 50})]
    (and (= :saturated stop)
         (empty? undifferentiated)
         (same-class? (into rules/derivative rules) result r)
         (or (= ::undefined v) (= v (value result env)))
         (= cost (:cost again)))))

(deftest derivatives-agree-with-the-reference-over-trig
  (let [res (tc/quick-check
             200
             (prop/for-all [t trig-term-gen, env env-gen]
               (agrees-with-the-reference? t env rules/trig)))]
    (is (:pass? res) (pr-str res))))

(deftest derivatives-agree-with-the-reference-over-exp-log
  (let [res (tc/quick-check
             200
             (prop/for-all [t exp-term-gen, env int-env-gen]
               (agrees-with-the-reference? t env rules/exp-log)))]
    (is (:pass? res) (pr-str res))))

(deftest derivative-is-ring-consistent-at-saturation
  ;; every form the rules propose agrees in the ring with every other
  ;; in its class once every :D is resolved, so the polynomial oracle
  ;; finds nothing after the run; it is too strict after every
  ;; application, where `independent` has settled a class at 0 while a
  ;; chain rule's product still holds a :D the ring cannot see through
  (let [res (tc/quick-check
             100
             (prop/for-all [t trig-term-gen]
               (let [{:keys [stop-reason egraph]} (bx/saturate [:D t :x] {:rules rules/derivative :too-big 50})]
                 (and (= :saturated stop-reason)
                      (nil? (an/inconsistency (bx/materialize-all egraph)))))))]
    (is (:pass? res) (pr-str res)))
  (is (thrown? clojure.lang.ExceptionInfo
               (simplify [:D [:sin :y] :x] {:rules rules/derivative :dev? true :cost bx/no-D}))
      "the per-application check trips on exactly that transient"))

(deftest the-graph-behind-differentiate-is-well-formed
  (let [res (tc/quick-check
             100
             (prop/for-all [t trig-term-gen]
               (let [{:keys [egraph]} (bx/saturate [:D t :x] {:rules (into rules/derivative all) :too-big 50})]
                 (empty? (check/violations (bx/materialize-all egraph))))))]
    (is (:pass? res) (pr-str res))))
