(ns bendix.rules-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.core :as bx :refer [simplify]]
            [bendix.poly :as p]
            [bendix.poly-test :refer [eval-term]]
            [bendix.rules :as rules]
            [bendix.term :as bt]
            [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.rewrite :as rw]))

(defn- simp [t] (:result (simplify t {:rules rules/trig})))

(def both (into rules/trig rules/powers))

(defn- same-class?
  "Do a and b land in one class when saturated together under rules?
  The engine as its own oracle for results whose spelling may vary."
  [rules a b]
  (let [g (bx/egraph)
        [g ia] (eg/add g a)
        [g ib] (eg/add g b)
        {:keys [egraph]} (rw/embiggen g rules {})]
    (= (eg/find egraph ia) (eg/find egraph ib))))

(defn- size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(defn- count-op [op t]
  (if (vector? t) (reduce + (if (= op (first t)) 1 0) (map #(count-op op %) (rest t))) 0))

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
         (rules/render (p/sub (p/constant 1) (p/expt (p/variable (bt/placeholder :cos [(bt/class-ref 9)])) 2))))
      "a placeholder renders as the node over the argument's class")
  (is (= [[:* '?2 [:expt '?1 [:+ 2 '?3 '?4]]] {'?1 1 '?2 2 '?3 3 '?4 4}]
         (rules/render (p/mul (p/variable 2)
                              (p/variable (bt/placeholder :expt [(bt/class-ref 1)
                                                                 (bt/placeholder :+ [2 (bt/class-ref 3) (bt/class-ref 4)])])))))
      "a placeholder may have several children, nested, with constants"))

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
;; powers

(def xn [:expt :x :n])
(def xm [:expt :x :m])
(def yn [:expt :y :n])

(defn- simp-powers [t] (:result (simplify t {:rules rules/powers})))

(deftest textbook-powers
  (let [r (simp-powers [:* xn xm])]
    (is (same-class? rules/powers r [:expt :x [:+ :n :m]]))
    (is (= 1 (count-op :expt r)) "one power"))
  (let [r (simp-powers [:* xn :x])]
    (is (same-class? rules/powers r [:expt :x [:+ :n 1]]))
    (is (= 1 (count-op :expt r))))
  (is (= :x (simp-powers [:* [:expt :x -2] [:expt :x 3]])) "a negative constant exponent")
  (is (= 1 (simp-powers [:* :x [:expt :x -1]])) "x · x⁻¹ = 1, the 0⁰ convention")
  (is (= [:expt :x -2] (simp-powers [:* [:expt :x -1] [:expt :x -1]])))
  (is (= :x (simp-powers [:* [:expt :x 1/2] [:expt :x 1/2]])) "rational exponents")
  (let [r (simp-powers [:expt xn 2])]
    (is (same-class? rules/powers r [:expt :x [:* 2 :n]]) "a power to an integer power")
    (is (= 1 (count-op :expt r))))
  (let [r (simp-powers [:* [:expt [:sin :x] :n] [:sin :x]])]
    (is (same-class? rules/powers r [:expt [:sin :x] [:+ :n 1]]) "an opaque base"))
  (let [r (simp-powers [:* [:expt [:+ :x 1] :n] [:expt [:+ :x 1] :m]])]
    (is (same-class? rules/powers r [:expt [:+ :x 1] [:+ :n :m]]) "a compound base"))
  (let [r (simp-powers [:* [:* :y xn] [:* xm :y]])]
    (is (same-class? rules/powers r [:* [:expt :y 2] [:expt :x [:+ :n :m]]]) "the ring keeps y², the rule does x"))
  (let [r (simp-powers [:+ [:+ :a [:* xn xm]] :b])]
    (is (same-class? rules/powers r [:+ :a :b [:expt :x [:+ :n :m]]]) "inside a sum")
    (is (= 1 (count-op :expt r))))
  (let [r (simp-powers [:* [:expt :x 2] xn])]
    (is (same-class? rules/powers r [:expt :x [:+ :n 2]]) "a folded square joins the symbolic power"))
  (is (= [:* [:expt :x :n] [:expt :y :n]] (simp-powers [:* xn [:expt :y :n]])) "different bases stay")
  (is (= xn (simp-powers xn)) "one power stays")
  (is (= [:expt :x 3] (simp-powers [:* :x [:expt :x 2]])) "the ring alone: no rule needed"))

(defn- cost-powers [t] (:cost (simplify t {:rules both :too-big 50})))

(deftest power-spellings-reach-one-cost
  ;; whichever spelling the cost prefers exists, whatever the input
  ;; wrote: the split one by a node for an offset of 1 beside another
  ;; factor, the combined one otherwise
  (is (= [6 6 6] (map cost-powers [[:* :a :y yn]
                                   [:* :a [:expt :y [:+ :n 1]]]
                                   [:* [:* :a :y] yn]]))
      "y · yⁿ is a node cheaper than y^(n+1) inside a product")
  (is (= [:* :a :y yn] (simp-powers [:* :a [:expt :y [:+ :n 1]]])) "and is proposed for it")
  (is (= [7 7] (map cost-powers [[:* :a [:expt :y 2] yn] [:* :a [:expt :y [:+ :n 2]]]]))
      "an offset of 2 is cheaper combined")
  (is (= [7 7] (map cost-powers [[:* :a [:expt :y -1] yn] [:* :a [:expt :y [:+ :n -1]]]]))
      "a negative offset is not split")
  (is (= [8 8] (map cost-powers [[:* :a :y yn [:expt :y :m]] [:* :a [:expt :y [:+ 1 :n :m]]]])))
  (is (= [8 8] (map cost-powers [[:* :a :y [:expt :y [:* 2 :n]]] [:* :a [:expt :y [:+ 1 [:* 2 :n]]]]])))
  (is (apply = (map cost-powers [[:* :a [:sin :x] [:expt [:sin :x] :n]] [:* :a [:expt [:sin :x] [:+ :n 1]]]]))
      "an opaque base")
  (is (= 0 (simp-powers [:- [:* :y :y yn] [:expt :y [:+ :n 2]]])) "the two forms are one class")
  (let [t [:+ [:* :x :x [:* [:* :x [:* [:* :x :y :x] yn] [:+ [:* :x :x] [:expt :y -1]]]
                         [:+ :x [:* [:+ [:sin :x] :x] [:* [:sin :x] :y]]]]] :x]
        {:keys [result cost]} (simplify t {:rules both :too-big 50})]
    (is (= cost (cost-powers result))
        "the term seed 1789597929120 shrank to: pythagoras rendered x⁵·y·yⁿ on the second pass only")))

(deftest powers-saturate-quickly
  (let [{:keys [iterations stop-reason egraph]} (bx/saturate [:+ [:* xn xm] [:* [:expt :x -2] [:expt :x 3]]] {:rules rules/powers})]
    (is (= :saturated stop-reason))
    (is (<= iterations 3))
    (is (empty? (check/violations egraph)))))

(def pow-leaf-gen (gen/elements [:x :y 1 2 -1 [:sin :x]]))
(def exponent-gen (gen/elements [:n :m -2 -1 0 1 2 3]))

(def pow-term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :*) inner inner inner)
                  (gen/tuple (gen/return :expt) inner exponent-gen)]))
   pow-leaf-gen))

(def rational-gen (gen/fmap #(/ % 5) gen/small-integer))
(def pow-env-gen (gen/fmap (fn [[x y n m]] {:x x :y y :n n :m m})
                           (gen/tuple rational-gen rational-gen (gen/choose -2 3) (gen/choose -2 3))))

(defn- value
  "eval-term, or ::undefined outside the domain."
  [t env]
  (try (eval-term t env)
       (catch clojure.lang.ExceptionInfo e
         (if (:undefined (ex-data e)) ::undefined (throw e)))))

(deftest powers-preserve-value-where-defined
  (let [res (tc/quick-check
             200
             (prop/for-all [t pow-term-gen, env pow-env-gen]
               (let [{:keys [result stop cost]} (simplify t {:rules both :too-big 50})
                     again (simplify result {:rules both :too-big 50})
                     v (value t env)]
                 (and (= :saturated stop)
                      (or (= ::undefined v) (= v (value result env)))
                      (<= (size result) (size t))
                      (= cost (:cost again))))))]
    (is (:pass? res) (pr-str res))))

(deftest the-graph-behind-powers-is-well-formed
  (let [res (tc/quick-check
             100
             (prop/for-all [t pow-term-gen]
               (let [{:keys [egraph]} (bx/saturate t {:rules both :too-big 50})]
                 (empty? (check/violations (bx/materialize-all egraph))))))]
    (is (:pass? res) (pr-str res))))

(def power-base-gen (gen/elements [:x :y [:sin :x]]))
(def power-symbol-gen (gen/elements [:n :m [:+ :n :m] [:* 2 :n] [:* -1 :m]]))
(def cofactor-gen (gen/elements [nil :a 2 [:sin :x] [:expt :x :m]]))

(defn- power-spellings
  "b^(s+k) beside the cofactor, written four ways."
  [b k s cofactor]
  (let [bk (if (= 1 k) b [:expt b k])
        product (fn [fs]
                  (let [fs (if cofactor (cons cofactor fs) fs)]
                    (if (= 1 (count fs)) (first fs) (into [:*] fs))))]
    [(product [[:expt b [:+ s k]]])
     (product [bk [:expt b s]])
     (product [[:expt b s] bk])
     (if cofactor [:* [:* cofactor bk] [:expt b s]] [:* bk [:expt b s]])]))

(deftest power-spellings-reach-one-cost-in-any-context
  (let [res (tc/quick-check
             100
             (prop/for-all [b power-base-gen, k (gen/choose 1 3), s power-symbol-gen
                            cofactor cofactor-gen, context pow-term-gen]
               (apply = (map #(cost-powers [:+ context %]) (power-spellings b k s cofactor)))))]
    (is (:pass? res) (pr-str res))))

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

;; ---------------------------------------------------------------------------
;; exp-log

(def ex [:exp :x])
(def ey [:exp :y])
(def all (-> [] (into rules/trig) (into rules/powers) (into rules/exp-log)))

(defn- simp-exp [t] (:result (simplify t {:rules rules/exp-log})))

(deftest textbook-exp-log
  (is (= [:exp [:+ :x :y]] (simp-exp [:* ex ey])))
  (is (= [:exp [:+ :x :y]] (simp-exp [:exp [:+ :x :y]])) "already one exponential")
  (is (= [:exp [:+ :x :y :z]] (simp-exp [:* [:* ex ey] [:exp :z]])))
  (is (= [:exp :x] (simp-exp [:* [:exp [:+ :x :y]] [:exp [:* -1 :y]]])) "the arguments cancel in the ring")
  (is (= 1 (simp-exp [:* ex [:expt ex -1]])) "exp x · (exp x)⁻¹: exp 0 folds to 1")
  (is (= 1 (simp-exp [:exp 0])))
  (is (= 0 (simp-exp [:log 1])))
  (is (= 1 (simp-exp [:exp [:- :x :x]])))
  (is (= [:exp [:* 2 :x]] (simp-exp [:expt ex 2])) "exp(x)² and exp(2x) tie; the node order decides")
  (is (= [:exp :x] (simp-exp [:* [:exp [:* 1/2 :x]] [:exp [:* 1/2 :x]]])) "rational coefficients")
  (let [r (simp-exp [:* [:expt ex :n] ex])]
    (is (same-class? rules/exp-log r [:exp [:* [:+ :n 1] :x]]) "a symbolic exponent"))
  (is (= [:+ :x :y] (simp-exp [:log [:* ex ey]])) "log of a product: collected, then log-of-exp")
  (is (= [:* 2 :x] (simp-exp [:log [:expt ex 2]])))
  (is (= [:* 2 :x] (simp-exp [:log [:exp [:* 2 :x]]])))
  (is (= 0 (simp-exp [:- [:exp [:+ :x :y]] [:* ex ey]])))
  (is (= [:+ :a :b [:exp [:+ :x :y]]] (simp-exp [:+ [:+ :a [:* ex ey]] :b])) "inside a sum")
  (is (= [:+ [:exp [:* 2 :x]] -1] (simp-exp [:* [:+ ex 1] [:- ex 1]])))
  (is (= [:* ex [:+ ey [:exp :z]]] (simp-exp [:* ex [:+ ey [:exp :z]]])) "the factored form is smaller")
  (is (contains? #{[:exp [:+ :x 1]] [:exp [:+ 1 :x]]} (simp-exp [:* [:exp 1] ex])) "a constant argument")
  (is (same-class? rules/exp-log [:expt ex -1] [:exp [:* -1 :x]])
      "a lone power of an exponential: the rule visits the opaque class")
  (is (= [:sin [:exp [:+ :x :y]]] (simp-exp [:sin [:* ex ey]])))
  (is (= 0 (simp-exp [:- [:sin [:* ex ey]] [:sin [:exp [:+ :x :y]]]])) "merged under an opaque operator by congruence")
  (is (= ex (simp-exp ex)))
  (is (= [:log :x] (simp-exp [:log :x])))
  (is (= [:exp [:log :x]] (simp-exp [:exp [:log :x]])) "conditional: not this rule set's business"))

(deftest exp-log-saturates-quickly
  ;; collect, then log-of-exp, then collect what the log revealed,
  ;; then quiet: a constant, whatever the size of the sum around it
  (let [t [:+ [:log [:* ex ey]] [:* [:exp [:+ :x :y]] [:exp [:* -1 :y]]]]
        {:keys [iterations stop-reason egraph]} (bx/saturate t {:rules rules/exp-log})]
    (is (= :saturated stop-reason))
    (is (<= iterations 4))
    (is (empty? (check/violations egraph))))
  (let [{:keys [iterations stop-reason]} (bx/saturate [:log [:* ex ey]] {:rules rules/exp-log})]
    (is (= :saturated stop-reason))
    (is (<= iterations 3))))

(deftest one-class-spelled-two-ways
  ;; the cofactor is one class, written as x^(n+m) on one side and
  ;; collected from xⁿ·xᵐ on the other; the canonical spelling is what
  ;; lets pythagoras see one pair
  (is (= [:expt :x [:+ :n :m]]
         (:result (simplify [:+ [:* s2 [:expt :x [:+ :n :m]]] [:* c2 [:* xn xm]]] {:rules all}))))
  (is (= [:exp [:+ :x :y]]
         (:result (simplify [:+ [:* s2 [:exp [:+ :x :y]]] [:* c2 [:* ex ey]]] {:rules all}))))
  (is (= [:+ [:* :q s2] [:* c2 [:exp [:+ :x :y]]]]
         (:result (simplify [:+ [:* s2 :q] [:* c2 [:* ex ey]]] {:rules all})))
      "and does not invent a pair"))

(def exp-leaf-gen (gen/elements [:x :y 1 2 -1 ex ey [:exp [:+ :x :y]] [:exp [:* 2 :x]] [:log ex]]))

(def exp-term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :-) inner inner)
                  (gen/tuple (gen/return :neg) inner)
                  (gen/tuple (gen/return :expt) inner (gen/choose -1 3))
                  (gen/tuple (gen/return :exp) inner)
                  (gen/tuple (gen/return :log) (gen/tuple (gen/return :exp) inner))]))
   exp-leaf-gen))

(def exp-env-gen (gen/fmap (fn [[x y]] {:x x :y y}) (gen/tuple (gen/choose -2 3) (gen/choose -2 3))))

(deftest exp-log-preserves-value-where-defined
  (let [res (tc/quick-check
             200
             (prop/for-all [t exp-term-gen, env exp-env-gen]
               (let [{:keys [result stop cost]} (simplify t {:rules all :too-big 50})
                     again (simplify result {:rules all :too-big 50})
                     v (value t env)]
                 (and (= :saturated stop)
                      (or (= ::undefined v) (= v (value result env)))
                      (<= (size result) (size t))
                      (= cost (:cost again))))))]
    (is (:pass? res) (pr-str res))))

(deftest the-graph-behind-exp-log-is-well-formed
  (let [res (tc/quick-check
             100
             (prop/for-all [t exp-term-gen]
               (let [{:keys [egraph]} (bx/saturate t {:rules all :too-big 50})]
                 (empty? (check/violations (bx/materialize-all egraph))))))]
    (is (:pass? res) (pr-str res))))
