(ns bendix.rules
  "Rule sets, and the normal-form rules of IDEA.md section 3.

  A normal-form rule rewrites a class's polynomial rather than a
  node. Its searcher visits every root whose :poly data is a
  polynomial and asks a polynomial rewrite (fn [g id p] polys) for
  the other forms the class is worth; each is rendered as a pattern
  over the class ids it mentions and carried by its match as the
  right-hand side, so one rule says a different thing about every
  class. The runner instantiates and unions as for any rule, the
  analysis joins the new form in, and the index merges any other
  class that already had it.

  `pythagoras` is the first: reduction modulo sin²u + cos²u = 1 for
  every argument u, in both elimination orders; `trig` is the rule
  set that holds it. `combine-powers` is the second: in every
  monomial, the factors that are powers of one base become one
  power; `powers` holds it."
  (:require [bendix.analysis :as an]
            [bendix.poly :as poly]
            [bendix.term :as bt]
            [cromulent.core :as eg]
            [cromulent.rewrite :as rw]
            [cromulent.term :as term]))

;; ---------------------------------------------------------------------------
;; normal-form rules

(defn- id-var [id] (symbol (str "?" id)))

(defn render
  "p as a pattern plus the bindings it needs. A variable atom renders
  as itself, a class id as ?id bound to that id, and a placeholder as
  the same node with every class id so replaced. Returns
  [pattern bindings]."
  [p]
  (let [ids (into #{}
                  (mapcat (fn [a]
                            (cond (bt/class-id? a) [a]
                                  (bt/placeholder? a) (bt/class-ids a)
                                  :else nil)))
                  (poly/atoms p))
        bindings (into {} (map (fn [id] [(id-var id) id])) ids)
        pattern (poly/->term p (fn [a]
                                 (cond (bt/class-id? a) (id-var a)
                                       (bt/placeholder? a) (bt/map-class-ids id-var a)
                                       :else a)))]
    [pattern bindings]))

(defn normal-form-rule
  "A rule whose left-hand side is f, (fn [g id p] polys): the other
  polynomials the class id, whose canonical form is p, is worth. f
  sees only classes whose data is a polynomial and may return nil.
  Each polynomial becomes one match carrying its rendering as :rhs."
  [name f]
  (rw/rule name
           (fn [g]
             (into []
                   (mapcat (fn [r]
                             (let [d (an/canonical g (eg/data g r :poly))]
                               (when (an/polynomial? d)
                                 (map (fn [p']
                                        (let [[pattern bindings] (render p')]
                                          {:class r :bindings bindings :rhs pattern}))
                                      (distinct (f g r d)))))))
                   (eg/roots g)))
           nil))

;; ---------------------------------------------------------------------------
;; pythagoras

(defn- trig-pairs
  "For every argument class u with a sine or cosine among the atoms of
  p, {u {:sin s :cos c}}: the atom ids, a missing partner being the
  placeholder [:sin u] or [:cos u]."
  [g p]
  (let [roles (for [a (poly/atoms p)
                    :when (bt/class-id? a)
                    n (bt/nodes-with g a #{:sin :cos})
                    :when (= 1 (term/arity n))]
                [(term/child n 0) (term/operator n) a])
        pairs (reduce (fn [m [u op a]] (assoc-in m [u op] a)) {} roles)]
    (into {}
          (map (fn [[u {:keys [sin cos]}]]
                 [u {:sin (or sin (bt/placeholder :sin [(bt/class-ref u)]))
                     :cos (or cos (bt/placeholder :cos [(bt/class-ref u)]))}]))
          pairs)))

(defn- one-minus-square [b]
  (poly/sub (poly/constant 1) (poly/expt (poly/variable b) 2)))

(defn- eliminate
  "p with every square of the `from` role of every pair reduced to
  1 − (the `to` role)²; nil when nothing changes or a limit is passed.
  Pairs touch disjoint atoms, so the order of reduction does not
  matter."
  [p pairs from to limit]
  (let [q (reduce (fn [p [_ pair]]
                    (when p
                      (poly/reduce-square p (get pair from) (one-minus-square (get pair to)) limit)))
                  p
                  (sort-by key pairs))]
    (when (and q (not= q p)) q)))

(defn pythagorean-forms
  "The sine-free and cosine-free forms of p, when they differ from p:
  the polynomial rewrite behind `pythagoras`."
  [g _ p]
  (let [pairs (trig-pairs g p)
        limit (an/threshold g)]
    (when (seq pairs)
      (keep identity [(eliminate p pairs :sin :cos limit)
                      (eliminate p pairs :cos :sin limit)]))))

(def pythagoras
  "sin²u + cos²u = 1 for every argument u, as reduction of the class's
  normal form modulo that identity in both elimination orders. Finds
  the pair inside any sum or product, however it is arranged."
  (normal-form-rule "pythagoras" pythagorean-forms))

(def trig
  "The trig rule set."
  [pythagoras])

;; ---------------------------------------------------------------------------
;; powers

(defn- factor
  "What the atom a of a monomial is as a power: {:base B :k k :sym S}
  for B^(k + S), the base a class id, k a constant and S the class of
  a non-constant exponent or nil. A variable and an opaque atom that
  is not a power are their own base to the first power."
  [g a]
  (let [self (fn [id] {:base id :k 1 :sym nil})]
    (if (bt/variable? a)
      (self (eg/lookup g a))
      (if-let [n (bt/node-with g a :expt)]
        (if (= 2 (term/arity n))
          (let [b (term/child n 0), e (term/child n 1)
                d (an/canonical g (eg/data g e :poly))
                k (when (an/polynomial? d) (poly/constant-value d))]
            (if k {:base b :k k :sym nil} {:base b :k 0 :sym e}))
          (self a))
        (self a)))))

(defn- exponent-placeholder
  "The exponent k + Σ c·S as a placeholder: the constant first, then
  the symbolic parts by class id."
  [k syms]
  (let [parts (into (if (zero? k) [] [k])
                    (map (fn [[s c]] (if (= 1 c) (bt/class-ref s) (bt/placeholder :* [c (bt/class-ref s)]))))
                    (sort-by key syms))]
    (case (count parts)
      0 0
      1 (nth parts 0)
      (bt/placeholder :+ parts))))

(defn- combine-monomial
  "m with the factors that are powers of one base combined into one
  placeholder power, or nil when no base has two factors or a power
  raised to a power."
  [g m]
  (let [factors (map (fn [[a e]] (assoc (factor g a) :atom a :e e)) m)
        groups (group-by :base factors)
        combinable (filter (fn [[_ fs]]
                             (or (< 1 (count fs))
                                 (let [f (nth fs 0)]
                                   (and (< 1 (:e f)) (or (:sym f) (not= 1 (:k f)))))))
                           groups)]
    (when (seq combinable)
      (reduce (fn [m [b fs]]
                (let [k (reduce +' 0 (map #(*' (:k %) (:e %)) fs))
                      syms (reduce (fn [acc f] (if (:sym f) (update acc (:sym f) (fnil +' 0) (:e f)) acc)) {} fs)
                      power (bt/placeholder :expt [(bt/class-ref b) (exponent-placeholder k syms)])]
                  (assoc (reduce dissoc m (map :atom fs)) power 1)))
              m
              (sort-by key combinable)))))

(defn power-forms
  "p with every monomial's same-base powers combined, when that
  changes anything: the polynomial rewrite behind `combine-powers`."
  [g _ p]
  (let [p' (reduce-kv (fn [acc m c] (poly/add acc {(or (combine-monomial g m) m) c}))
                      poly/zero
                      p)]
    (when (not= p' p) [p'])))

(def combine-powers
  "x^a · x^b = x^(a+b), and (x^a)^n = x^(n·a) for an integer n, inside
  every monomial, for the powers the analysis holds as atoms: a
  negative or non-integer constant exponent, or a symbolic one. Sound
  on the principal branch wherever the left-hand side is defined; at
  x = 0 it follows the convention 0⁰ = 1 (IDEA.md section 10)."
  (normal-form-rule "combine-powers" power-forms))

(def powers
  "The powers rule set."
  [combine-powers])

;; ---------------------------------------------------------------------------
;; the oracle for this rule set

(defn- in-pythagorean-ideal?
  "Is d zero modulo sin²u + cos²u − 1 for every argument u it mentions?"
  [g d]
  (let [red (reduce (fn [d [_ {:keys [sin cos]}]]
                      (poly/reduce-square d sin (one-minus-square cos)))
                    d
                    (sort-by key (trig-pairs g d)))]
    (empty? red)))

(defn trig-inconsistency
  "nil when every class's forms agree modulo sin²u + cos²u = 1, else
  a map naming the first class whose forms differ by something
  outside that identity, or whose data is :conflict. The oracle for
  the trig rule set, as bendix.analysis/inconsistency is for ring-only
  rule sets."
  [g]
  (some (fn [r]
          (if (= :conflict (eg/data g r :poly))
            {:class r :conflict true}
            (let [fs (vec (an/forms g r))]
              (when (< 1 (count fs))
                (let [base (nth fs 0)]
                  (some (fn [f]
                          (let [d (poly/sub f base)]
                            (when-not (in-pythagorean-ideal? g d)
                              {:class r :forms (set fs) :difference d})))
                        (subvec fs 1)))))))
        (eg/roots g)))
