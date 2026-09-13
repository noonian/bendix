(ns bendix.analysis-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.analysis :as an]
            [bendix.core :as bx]
            [bendix.poly :as p]
            [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.gen :as cg]
            [cromulent.rewrite :as rw]))

(defn- ok? [g]
  (let [vs (check/violations g)]
    (is (empty? vs) (pr-str vs))
    g))

(defn- data [g id] (an/canonical g (eg/data g id :poly)))

(deftest like-terms-and-constants
  (let [g (bx/egraph)
        [g s] (eg/add g [:+ [:* 2 :x] [:* 3 :x]])
        [g c] (eg/add g [:+ 1 [:* 2 3]])
        g (eg/rebuild g)]
    (ok? g)
    (is (= {{:x 1} 5} (data g s)))
    (is (= {{} 7} (data g c)))
    (let [[g seven] (eg/add g 7)]
      (is (= (eg/find g seven) (eg/find g c)) "the index merges 7 into the class of 1 + 2·3"))
    (let [[g s'] (eg/add g [:* :x 5])]
      (is (= (eg/find g s') (eg/find g s)) "and x·5 into the class of 2x + 3x"))))

(deftest cancellation
  (let [g (bx/egraph)
        [g d] (eg/add g [:- [:+ :x :y] [:+ :y :x]])
        g (eg/rebuild g)]
    (ok? g)
    (is (= {} (data g d)))
    (let [[g z] (eg/add g 0)]
      (is (= (eg/find g z) (eg/find g d)) "0 joins the class"))))

(deftest arrangements-land-in-one-class
  ;; four spellings of a + b + c, no AC rules
  (let [sums [[:+ [:+ :a :b] :c] [:+ :c [:+ :b :a]] [:+ [:+ :c :a] :b] [:+ :a [:+ :b :c]]]
        g (eg/rebuild (reduce (fn [g t] (first (eg/add g t))) (bx/egraph) sums))]
    (ok? g)
    (is (= 1 (count (set (map #(cg/id-of g %) sums)))))
    (is (= 7 (eg/class-count g)) "a b c {a+b, b+a} {c+a} {b+c} {the sum}")
    (is (= 11 (eg/node-count g)) "3 leaves, 4 inner sums, 4 outer sums: nothing but what was written")))

(deftest opaque-atoms
  (let [g (bx/egraph)
        [g s] (eg/add g [:+ [:sin :x] [:sin :x]])
        [g sx] (eg/add g [:sin :x])
        g (eg/rebuild g)]
    (ok? g)
    (is (= {:atom (eg/find g sx)} (data g sx)))
    (is (= {{(eg/find g sx) 1} 2} (data g s)))
    (is (= [:* 2 [:sin :x]] (:result (bx/simplify [:+ [:sin :x] [:sin :x]]))))))

(deftest atoms-move-with-unions
  ;; 2·sin x and sin y + sin y are not congruent; once x = y the
  ;; analysis re-keys the sine atom and the index merges them
  (let [g (bx/egraph)
        [g a] (eg/add g [:* 2 [:sin :x]])
        [g b] (eg/add g [:+ [:sin :y] [:sin :y]])
        [g x] (eg/add g :x)
        [g y] (eg/add g :y)]
    (is (not= (eg/find g a) (eg/find g b)))
    (let [[g _] (eg/union g x y)
          g (eg/rebuild g)]
      (ok? g)
      (is (= (eg/find g a) (eg/find g b)))
      (is (every? #(eg/root? g %) (remove keyword? (p/atoms (data g a)))) "no stale atom ids"))))

(deftest too-big-and-conflict
  (let [g (bx/egraph {:too-big 3})
        [g big] (eg/add g [:expt [:+ [:+ :x :y] :z] 4])
        [g par] (eg/add g [:+ [:expt [:+ [:+ :x :y] :z] 4] 1])
        g (eg/rebuild g)]
    (ok? g)
    (is (= :too-big (data g big)))
    (is (= :too-big (data g par)) "propagates to parents"))
  (let [g (bx/egraph)
        [g x] (eg/add g :x)
        [g x1] (eg/add g [:+ :x 1])
        [g _] (eg/union g x x1)
        g (eg/rebuild g)]
    (ok? g)
    (is (= :conflict (data g x)))
    (is (= {:class (eg/find g x) :conflict true} (an/inconsistency g))))
  )

(deftest determining-equations-are-solved
  ;; a class holding two forms whose difference is linear in one atom
  ;; determines that atom: the analysis unions it with the constant
  (doseq [[assertion expected-a parent expected-parent]
          [[[:neg :a] 0 [:+ [:neg :a] 1] 1]              ; a = -a      => a = 0
           [[:* :a 1/2] 0 [:+ [:* :a 1/2] 1] 1]           ; a = a/2     => a = 0
           [[:+ [:* 2 :a] 1] -1 [:* :a 3] -3]             ; a = 2a + 1  => a = -1
           [[:- [:* 3 :a] 6] 3 [:+ :a :a] 6]]]            ; a = 3a - 6  => a = 3
    (testing (pr-str assertion)
      (let [g (bx/egraph)
            [g a] (eg/add g :a)
            [g other] (eg/add g assertion)
            [g s] (eg/add g parent)
            [g _] (eg/union g a other)
            g (eg/rebuild g)
            [g c] (eg/add g expected-a)]
        (ok? g)
        (is (= (p/constant expected-a) (data g a)))
        (is (= (eg/find g c) (eg/find g a)) "a is in the constant's class")
        (is (= (p/constant expected-parent) (data g s))))))
  ;; an equation in two atoms is not solved: it stays an assumption
  (let [g (bx/egraph)
        [g x] (eg/add g :x)
        [g y1] (eg/add g [:+ :y 1])
        [g _] (eg/union g x y1)
        g (eg/rebuild g)]
    (ok? g)
    (is (not (p/constant? (data g x))))))

(deftest assumptions-keep-the-smaller-form
  (let [g (bx/egraph)
        [g x] (eg/add g :x)
        [g y1] (eg/add g [:+ :y 1])
        [g _] (eg/union g x y1)
        g (eg/rebuild g)]
    (ok? g)
    (is (= {{:x 1} 1} (data g x)) "x is the smaller form")
    (is (= {:class (eg/find g x) :forms #{{{:x 1} 1} {{:y 1} 1, {} 1}}} (an/inconsistency g)))))

;; ---------------------------------------------------------------------------
;; the spelling of canonical forms

(deftest a-defined-atom-is-spelled-by-its-form
  ;; sin y is opaque until the graph asserts it is x + 1; from then on
  ;; every form that mentioned it is spelled with x + 1, so the two
  ;; products land in one class through the index
  (let [g (bx/egraph)
        [g p1] (eg/add g [:* :a [:sin :y]])
        [g p2] (eg/add g [:* :a [:+ :x 1]])
        [g s] (eg/add g [:sin :y])
        [g x1] (eg/add g [:+ :x 1])
        g (eg/rebuild g)]
    (is (not= (eg/find g p1) (eg/find g p2)))
    (let [[g _] (eg/union g s x1)
          g (eg/rebuild g)]
      (ok? g)
      (is (= {{:x 1} 1, {} 1} (data g s)) "the sine's class is worth x + 1")
      (is (= {{:a 1, :x 1} 1, {:a 1} 1} (data g p1)) "and its parent is spelled with it")
      (is (= (eg/find g p1) (eg/find g p2)) "so the index merges a·sin y with a·(x + 1)"))))

(deftest a-solved-variable-is-spelled-by-its-value
  ;; x + y and y + 2 once x = 2: the order alone keeps x + y, whose
  ;; coefficients are smaller, so the spelling rule is what merges them
  (let [g (bx/egraph)
        [g a] (eg/add g [:+ :x :y])
        [g b] (eg/add g [:+ :y 2])
        [g x] (eg/add g :x)
        [g two] (eg/add g 2)
        g (eg/rebuild g)]
    (is (not= (eg/find g a) (eg/find g b)))
    (let [[g _] (eg/union g x two)
          g (eg/rebuild g)]
      (ok? g)
      (is (= {{:y 1} 1, {} 2} (data g a)))
      (is (= (eg/find g a) (eg/find g b)))
      (is (nil? (an/inconsistency g)) "one spelling per class: nothing to report"))))

(deftest a-class-worth-one-atom-is-that-atom
  (let [g (bx/egraph)
        [g q] (eg/add g [:* [:sin :x] 1])
        [g s] (eg/add g [:sin :x])
        [g a] (eg/add g [:cos [:* [:sin :x] 1]])
        [g b] (eg/add g [:cos [:sin :x]])
        g (eg/rebuild g)]
    (ok? g)
    (is (= (eg/find g q) (eg/find g s)) "sin x · 1 is the class of sin x")
    (is (= (eg/find g a) (eg/find g b)) "so their cosines are congruent"))
  ;; the class then holds the form "its own atom", which must not hide
  ;; what the class learns later
  (let [g (bx/egraph)
        [g q] (eg/add g [:* [:sin :x] 1])
        [g n] (eg/add g [:neg [:* [:sin :x] 1]])
        [g s] (eg/add g [:sin :x])
        [g m] (eg/add g [:- 1 :y])
        [g _] (eg/union g s m)
        g (eg/rebuild g)]
    (ok? g)
    (is (= {{} 1, {:y 1} -1} (data g q)) "sin x = 1 − y: the real form wins over the class's own atom")
    (is (= {{:y 1} 1, {} -1} (data g n)) "and the parent is spelled with it")))

(deftest cyclic-definitions-stay-atoms
  (let [g (bx/egraph)
        [g s] (eg/add g [:sin :y])
        [g p] (eg/add g [:* [:sin :y] :a])
        [g _] (eg/union g s p)
        g (eg/rebuild g)
        r (eg/find g s)]
    (ok? g)
    (is (= {:atom r} (data g s)) "sin y = a·sin y mentions the sine: an equation, not a definition; the atom stays")
    (is (= #{{{r 1, :a 1} 1}} (an/forms g r)) "the equation is on record"))
  (let [g (bx/egraph)
        [g s] (eg/add g [:sin :y])
        [g c] (eg/add g [:cos :y])
        [g p] (eg/add g [:* [:cos :y] :a])
        [g q] (eg/add g [:* [:sin :y] :b])
        [g _] (eg/union g s p)
        [g _] (eg/union g c q)
        g (eg/rebuild g)]
    (ok? g)
    (is (= {{(eg/find g c) 1, :a 1} 1} (data g s)) "a two-cycle: sin y = a·cos y is a definition")
    (is (= {:atom (eg/find g c)} (data g c))
        "and cos y = b·sin y, spelled through it, mentions cos y: an equation, so the cosine stays an atom")))

(deftest exact-values-fold
  (let [g (bx/egraph)
        [g e0] (eg/add g [:exp [:- :x :x]])
        [g l1] (eg/add g [:log [:* 1 1]])
        [g ex] (eg/add g [:exp :x])
        g (eg/rebuild g)]
    (ok? g)
    (is (= {{} 1} (data g e0)) "exp 0 = 1")
    (is (= {} (data g l1)) "log 1 = 0")
    (is (= {:atom (eg/find g ex)} (data g ex)) "exp x stays opaque")
    (let [[g one] (eg/add g 1)]
      (is (= (eg/find g one) (eg/find g e0)) "and joins the class of 1"))))

(deftest non-ring-operators-are-opaque-whatever-their-children
  (let [big [:expt [:+ [:+ :x :y] :z] 4]
        g (bx/egraph {:too-big 3})
        [g b] (eg/add g big)
        [g s] (eg/add g [:sin big])
        [g d] (eg/add g [:- [:sin big] [:sin big]])
        g (eg/rebuild g)]
    (ok? g)
    (is (= :too-big (data g b)))
    (is (= {:atom (eg/find g s)} (data g s)) "sin of a too-big class is an atom, not too-big")
    (is (= {} (data g d)) "so sin(big) − sin(big) = 0")))

(deftest the-preference-is-pluggable
  ;; x = y + 1 asserted: the default keeps x, most-terms keeps y + 1,
  ;; and every parent follows the choice
  (let [assert-it (fn [opts]
                    (let [g (bx/egraph opts)
                          [g x] (eg/add g :x)
                          [g y1] (eg/add g [:+ :y 1])
                          [g sq] (eg/add g [:expt :x 2])
                          [g _] (eg/union g x y1)
                          g (eg/rebuild g)]
                      (ok? g)
                      [(data g x) (data g sq)]))]
    (is (= [{{:x 1} 1} {{:x 2} 1}] (assert-it {})))
    (is (= [{{:x 1} 1} {{:x 2} 1}] (assert-it {:prefer an/fewest-terms})))
    (is (= [{{:y 1} 1, {} 1} {{:y 2} 1, {:y 1} 2, {} 1}] (assert-it {:prefer (an/most-terms 200)})))
    (is (= [{{:x 1} 1} {{:x 2} 1}] (assert-it {:prefer an/lowest-degree}))
        "equal degree: the built-in order breaks the tie"))
  (is (= [:* 5 :x] (:result (bx/simplify [:+ [:* 2 :x] [:* 3 :x]] {:prefer an/fewest-atoms})))
      "simplify takes :prefer")
  (is (thrown? clojure.lang.ExceptionInfo
               (let [g (bx/egraph {:prefer (fn [p] (- (p/term-count p)))})
                     [g x] (eg/add g :x)
                     [g y1] (eg/add g [:+ :y 1])
                     [g _] (eg/union g x y1)]
                 (eg/rebuild g)))
      "a key that is not a vector of naturals is refused"))

;; ---------------------------------------------------------------------------
;; experiment 3: the soundness oracle

(def ring-rules
  [(rw/rule "comm-add" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "comm-mul" '[:* ?a ?b] '[:* ?b ?a])
   (rw/rule "assoc-add" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])
   (rw/rule "distrib" '[:* ?a [:+ ?b ?c]] '[:+ [:* ?a ?b] [:* ?a ?c]])])

(def wrong-rule (rw/rule "wrong" '[:* ?a ?b] '[:+ ?a ?b]))

(deftest the-oracle-catches-a-wrong-rule
  (let [t [:* [:+ :x 1] [:+ :y 2]]]
    (is (map? (bx/simplify t {:rules ring-rules :dev? true :iter-limit 6})) "sound rules pass")
    (let [e (try (bx/simplify t {:rules (conj ring-rules wrong-rule) :dev? true :iter-limit 6})
                 nil
                 (catch Exception e e))]
      (is (some? e))
      (is (= "wrong" (:rule (ex-data e))))
      (is (contains? (:problem (ex-data e)) :forms)))))

;; ---------------------------------------------------------------------------
;; properties

(deftest invariants-hold-with-poly
  (let [res (tc/quick-check
             100
             (prop/for-all [ops cg/script-gen]
               (empty? (check/violations (:egraph (cg/run-script (bx/egraph) ops))))))]
    (is (:pass? res) (pr-str res))))

(def atoms [:a :b :c :d :e :f])

(defn- nested-sum [xs]
  (reduce (fn [acc a] [:+ acc a]) (first xs) (rest xs)))

(deftest every-arrangement-of-a-sum-is-one-class
  (let [res (tc/quick-check
             100
             (prop/for-all [[n shuffles] (gen/bind (gen/choose 2 6)
                                                   (fn [n] (gen/tuple (gen/return n)
                                                                      (gen/vector (gen/shuffle (take n atoms)) 1 5))))]
               (let [sums (map nested-sum shuffles)
                     g (eg/rebuild (reduce (fn [g t] (first (eg/add g t))) (bx/egraph) sums))]
                 (and (empty? (check/violations g))
                      (= 1 (count (set (map #(cg/id-of g %) sums))))
                      (<= (eg/node-count g) (+ n (* (count sums) (dec n))))))))]
    (is (:pass? res) (pr-str res))))
