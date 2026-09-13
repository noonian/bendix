(ns bendix.analysis
  "E-class analyses for the CAS. The polynomial analysis is approach C
  of ../design/ac-problem.md: every class carries the normal form of
  what it is worth as a polynomial over ℚ, and classes with the same
  normal form are merged, so the commutative-ring identities never
  run as rules.

  Data of a class under :poly is one of

    polynomial   a bendix.poly value over atoms that are variables
                 (keywords) or the ids of opaque classes
    {:atom id}   the class is opaque (holds no ring node): it is its
                 own indeterminate, id being the class id; parents see
                 it as the variable id
    :too-big     a normal form past the term-count threshold
    :conflict    two forms that differ by a non-zero constant met
                 (x = x + 1): the e-graph asserts a contradiction

  A canonical form is spelled over undefined atoms only. Class ids
  inside data go stale when classes merge, and a class stops being
  opaque when a rule proves it is worth a ring expression
  (exp(x + y) = exp(x)·exp(y)). `canonical` runs every id through
  `find` and replaces every atom whose class has a polynomial form by
  that form, and cromulent recomputes the data of every class whose
  nodes or children change, so neither a stale id nor a stale
  spelling survives a rebuild.

  Two different polynomials in one class are an equation the e-graph
  asserts and the ring cannot prove: a user assumption, a true
  identity from outside the ring (sin²x + cos²x = 1), or an unsound
  rule. The join keeps the preferred form: the smaller under
  bendix.poly's well-founded order, behind a :prefer measure when one
  is given (`fewest-terms`, `lowest-degree`, `fewest-atoms`,
  `most-terms`), so a class settles after finitely many changes
  whatever the measure. The equation is also used: cromulent hands
  `reconcile` the forms that met in a class, and when two of them
  differ by α·v + β for a single atom v, v is unioned with the
  constant -β/α (a = a/2 gives a = 0; a = 2a + 1 gives a = -1). Under
  a ring-only rule set no such pair can be sound, which is what
  `inconsistency` checks in dev mode."
  (:require [bendix.poly :as poly]
            [bendix.term :as bt]
            [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn atom? [d] (and (map? d) (contains? d :atom)))

(defn polynomial? [d] (and (map? d) (not (contains? d :atom))))

(defn- the-analysis [g]
  (some #(when (= :poly (:name %)) %) (:analyses g)))

(defn threshold
  "The :too-big term-count threshold of g's polynomial analysis."
  [g]
  (:too-big (the-analysis g)))

;; ---------------------------------------------------------------------------
;; canonical forms

(declare expand)

(defn- itself?
  "Is the polynomial d the atom a to the first power and nothing else?"
  [d a]
  (and (= 1 (count d)) (= 1 (get d {a 1}))))

(defn- definition
  "What the atom a, a variable or a root, stands for in a canonical
  form: ::self when it is undefined (an opaque class, or a variable
  whose class is worth that variable); otherwise its class's form,
  itself expanded, or ::cyclic when the chain of definitions reaches
  a class in visited, or ::too-big past the limit. Variables are
  looked up only when the analysis state says some variable is
  defined."
  [g a visited limit]
  (let [r (if (bt/variable? a)
            (when (contains? (get-in g [:analysis-state :defined]) a) (eg/lookup g a))
            a)
        d (when r (eg/data g r :poly))]
    (cond
      (or (nil? r) (not (polynomial? d)) (itself? d a)) ::self
      (contains? visited r) ::cyclic
      :else (expand g d (conj visited r) limit))))

(defn- roots
  "p with every class-id atom replaced by its root."
  [g p]
  (poly/map-atoms #(if (bt/variable? %) % (eg/find g %)) p))

(defn- substitutions
  "The substitution of every defined atom of p by its definition, as
  a map, or ::cyclic or ::too-big. At the top level a cyclic atom
  stays an atom instead."
  [g p visited limit top?]
  (reduce (fn [acc a]
            (let [q (definition g a visited limit)]
              (case q
                ::self acc
                ::cyclic (if top? acc (reduced ::cyclic))
                ::too-big (reduced ::too-big)
                (assoc acc a q))))
          {}
          (poly/atoms p)))

(defn- expand
  "p spelled over undefined atoms; ::cyclic when some definition
  reaches visited, ::too-big past the limit."
  [g p visited limit]
  (let [p (roots g p)
        subst (substitutions g p visited limit false)]
    (cond
      (keyword? subst) subst
      (empty? subst) p
      :else (or (poly/substitute p subst limit) ::too-big))))

(defn canonical
  "d with every class-id atom replaced by its root in g, and every
  atom whose class has a different polynomial form (an opaque class
  a rule proved is worth a product, a variable the graph asserted
  equal to 2) replaced by that form, so that a canonical form is
  spelled over undefined atoms only. An atom whose chain of
  definitions reaches itself stays an atom; a form past the threshold
  is :too-big."
  [g d]
  (cond
    (atom? d) {:atom (eg/find g (:atom d))}
    (polynomial? d)
    (let [limit (threshold g)
          p (roots g d)
          subst (substitutions g p #{} limit true)]
      (cond
        (keyword? subst) :too-big
        (empty? subst) p
        :else (or (poly/substitute p subst limit) :too-big)))
    :else d))

(defn- note-defined-variables
  "Record in the analysis state every variable whose class is worth
  something other than itself, so that `canonical` looks up no other
  variable. Returns g'."
  [g id d]
  (reduce (fn [g v]
            (if (and (polynomial? d) (itself? d v))
              (update-in g [:analysis-state :defined] disj v)
              (update-in g [:analysis-state :defined] (fnil conj #{}) v)))
          g
          (filter bt/variable? (eg/nodes g id))))

(defn- as-poly [d]
  (if (atom? d) (poly/variable (:atom d)) d))

;; ---------------------------------------------------------------------------
;; make

(def ^:private ring-operators #{:+ :* :neg :- :expt :/})

(defn- exact-value
  "The constant an :exp or :log node is worth at the one point where
  that is exact, exp 0 = 1 and log 1 = 0; ::opaque otherwise."
  [g node]
  (let [op (term/operator node)
        d (when (= 1 (term/arity node))
            (canonical g (eg/data g (term/child node 0) :poly)))]
    (cond
      (not (polynomial? d)) ::opaque
      (and (= :exp op) (= poly/zero d)) (poly/constant 1)
      (and (= :log op) (= (poly/constant 1) d)) poly/zero
      :else ::opaque)))

(defn- ring-op
  "The polynomial of a compound node over its children's data, or
  ::opaque when the operator is not a ring operation over ℚ, whatever
  its children's data, or the node is one the ring cannot fold."
  [g node too-big]
  (let [op (term/operator node)]
    (cond
      (contains? #{:exp :log} op) (exact-value g node)
      (not (contains? ring-operators op)) ::opaque
      :else
      (let [ds (mapv #(canonical g (eg/data g % :poly)) (term/children node))
            n (count ds)]
        (cond
          (some nil? ds) ::opaque
          (some #{:conflict} ds) :conflict
          (some #{:too-big} ds) :too-big
          :else
          (let [ps (mapv as-poly ds)
                result (case op
                         :+ (poly/sum ps)
                         :* (poly/product ps)
                         :neg (when (= 1 n) (poly/neg (nth ps 0)))
                         :- (cond (= 1 n) (poly/neg (nth ps 0))
                                  (= 2 n) (poly/sub (nth ps 0) (nth ps 1))
                                  :else nil)
                         :expt (when (= 2 n)
                                 (let [e (poly/constant-value (nth ps 1))]
                                   (when (and e (integer? e) (not (neg? e)))
                                     (or (poly/expt (nth ps 0) e too-big) ::too-big))))
                         :/ (when (= 2 n)
                              (let [k (poly/constant-value (nth ps 1))]
                                (when (and k (not (zero? k)))
                                  (poly/scale (nth ps 0) (/ 1 k)))))
                         nil)]
            (cond
              (nil? result) ::opaque
              (= ::too-big result) :too-big
              (> (poly/term-count result) too-big) :too-big
              :else result)))))))

(defn- the-make [g]
  (:make (the-analysis g)))

(defn forms
  "The distinct canonical polynomial forms the class of r derives:
  one per ring node, plus the stored data. More than one means the
  e-graph asserts an equation the ring cannot see."
  [g r]
  (let [make (the-make g)]
    (into #{}
          (comp (map #(canonical g %)) (filter polynomial?))
          (cons (eg/data g r :poly)
                (map #(make g (eg/canonicalize g %) r) (:nodes (eg/eclass g r)))))))

(defn- solve
  "Every equation between two forms of one class that is linear in a
  single atom determines that atom: union it with the constant.
  Returns g'."
  [g forms]
  (let [fs (into [] (comp (map #(canonical g %)) (filter polynomial?) (distinct)) forms)]
    (reduce (fn [g [p q]]
              (if-let [[v value] (poly/linear-in-one-atom (poly/sub p q))]
                (let [[g vid] (if (bt/variable? v) (eg/add g v) [g v])
                      [g cid] (eg/add g value)]
                  (first (eg/union g vid cid)))
                g))
            g
            (for [i (range (count fs)), j (range (inc i) (count fs))] [(nth fs i) (nth fs j)]))))

;; ---------------------------------------------------------------------------
;; preference: which of two forms a class keeps

(defn fewest-terms
  "The default preference as a measure: fewer terms first; the
  built-in order then decides by degree, coefficient size and so on."
  [p]
  [(poly/term-count p)])

(defn lowest-degree
  "Lower total degree first, before term count."
  [p]
  [(inc (poly/degree p))])

(defn fewest-atoms
  "Fewer distinct indeterminates first."
  [p]
  [(count (poly/atoms p))])

(defn most-terms
  "More terms first, bounded by the threshold so that the measure
  stays well-founded: (most-terms 200) prefers the longer of two forms
  as long as it fits."
  [too-big]
  (fn [p] [(max 0 (- too-big (poly/term-count p)))]))

(defn- measure-key [prefer p]
  (let [k (prefer p)]
    (when-not (and (vector? k) (every? #(and (integer? %) (not (neg? %))) k))
      (throw (ex-info ":prefer must return a vector of natural numbers" {:key k :polynomial p})))
    k))

(defn- own-atom
  "The class id a form stands for when it is that atom and nothing
  else: {:atom id}, or the polynomial that is one class-id atom to the
  first power with coefficient 1 (what `sin x · 1` computes, and what
  the index then unions with the class of `sin x`). nil otherwise."
  [d]
  (cond
    (atom? d) (:atom d)
    (and (polynomial? d) (= 1 (count d)))
    (let [[m c] (first d)]
      (when (and (= 1 c) (= 1 (count m)))
        (let [[a e] (first m)]
          (when (and (= 1 e) (bt/class-id? a)) a))))
    :else nil))

(defn- defines?
  "Does the polynomial d define the atom id? A form that does not
  mention the atom does (exp(x)·exp(y) for exp(x + y), 1 − x for
  log(exp(1 − x))); a form that mentions it (a·sin y for sin y) is an
  equation the class records, and the atom stays its representative."
  [d id]
  (and (polynomial? d) (not (contains? (poly/atoms d) id))))

(defn- preferred
  "The form a class keeps of two polynomials: without a measure, the
  smaller under the built-in order; with one, the smaller key, shorter
  keys first and then lexicographic, so that any measure into vectors
  of naturals is well-founded, and ties go to the built-in order."
  [prefer a b]
  (if (nil? prefer)
    (poly/smaller a b)
    (let [c (compare (measure-key prefer a) (measure-key prefer b))]
      (cond (neg? c) a
            (pos? c) b
            :else (poly/smaller a b)))))

;; ---------------------------------------------------------------------------
;; the analysis

(defn poly-analysis
  "The polynomial normal-form analysis. Options: :too-big, the term
  count past which a normal form is abandoned (default 200); :prefer,
  a measure (fn [p] [n ...]) into vectors of natural numbers deciding
  which of two forms a class keeps (default: the built-in order,
  fewest terms first)."
  ([] (poly-analysis {}))
  ([{:keys [too-big prefer] :or {too-big 200}}]
   {:name :poly
    :too-big too-big
    :prefer prefer
    :make (fn [g node id]
            (cond
              (bt/constant? node) (poly/constant node)
              (bt/variable? node) (poly/variable node)
              (term/compound? node) (let [r (ring-op g node too-big)]
                                      (if (= ::opaque r) {:atom id} r))
              :else {:atom id}))
    ;; an atom, {:atom id} or its unit polynomial, is below :too-big
    ;; and below any form that defines it; a form that mentions the
    ;; atom is an equation, and the atom stays
    :merge (fn [g a b]
             (let [a (canonical g a), b (canonical g b)
                   ia (own-atom a), ib (own-atom b)]
               (cond
                 (= a b) a
                 (or (= :conflict a) (= :conflict b)) :conflict
                 (and ia ib) (if (= ia ib)
                               {:atom ia}
                               (preferred prefer (poly/variable ia) (poly/variable ib)))
                 ia (if (or (not (polynomial? b)) (defines? b ia)) b a)
                 ib (if (or (not (polynomial? a)) (defines? a ib)) a b)
                 (or (= :too-big a) (= :too-big b)) :too-big
                 :else (let [d (poly/sub a b)]
                         (if (poly/constant? d)
                           :conflict
                           (preferred prefer a b))))))
    :reconcile (fn [g _ datas] (solve g datas))
    ;; every class is indexed under its canonical form, an opaque class
    ;; under its own atom, so a class worth exactly sin x (sin x · 1) is
    ;; the class of sin x
    :modify (fn [g id]
              (let [d (canonical g (eg/data g id :poly))
                    g (note-defined-variables g id d)
                    key (cond (polynomial? d) d
                              (atom? d) (poly/variable (:atom d)))]
                (if-not key
                  g
                  (let [r (eg/find g id)
                        other (get-in g [:analysis-state :poly key])]
                    (if (and other (not= (eg/find g other) r))
                      (first (eg/union g other r))
                      (assoc-in g [:analysis-state :poly key] r))))))}))

(defn inconsistency
  "nil when every class is consistent, else a map describing the first
  class whose ring nodes compute different normal forms, or whose data
  is :conflict. Under a ring-only rule set any such class means an
  unsound rule fired; under other rule sets it is expected."
  [g]
  (some (fn [r]
          (if (= :conflict (eg/data g r :poly))
            {:class r :conflict true}
            (let [fs (forms g r)]
              (when (< 1 (count fs))
                {:class r :forms fs}))))
        (eg/roots g)))
