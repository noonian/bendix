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
  every argument u, in both elimination orders. `trig` is the rule
  set that holds it."
  (:require [bendix.analysis :as an]
            [bendix.poly :as poly]
            [cromulent.core :as eg]
            [cromulent.rewrite :as rw]))

;; ---------------------------------------------------------------------------
;; normal-form rules

(defn- id-var [id] (symbol (str "?" id)))

(defn- arg-var [u] (symbol (str "?u" u)))

(defn render
  "p as a pattern plus the bindings it needs. A variable atom renders
  as itself; an opaque class id as ?id bound to id; a placeholder
  atom [op u], a node the graph may not hold yet, as [op ?u<u>] with
  ?u<u> bound to the argument class u. Returns [pattern bindings]."
  [p]
  (let [atoms (poly/atoms p)
        bindings (into {}
                       (keep (fn [a]
                               (cond (integer? a) [(id-var a) a]
                                     (vector? a) [(arg-var (nth a 1)) (nth a 1)]
                                     :else nil)))
                       atoms)
        pattern (poly/->term p (fn [a]
                                 (cond (integer? a) (id-var a)
                                       (vector? a) [(nth a 0) (arg-var (nth a 1))]
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
                    :when (integer? a)
                    n (:nodes (eg/eclass g a))
                    :when (and (vector? n) (= 2 (count n)) (contains? #{:sin :cos} (nth n 0)))]
                [(eg/find g (nth n 1)) (nth n 0) a])
        pairs (reduce (fn [m [u op a]] (assoc-in m [u op] a)) {} roles)]
    (into {}
          (map (fn [[u {:keys [sin cos]}]]
                 [u {:sin (or sin [:sin u]) :cos (or cos [:cos u])}]))
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
