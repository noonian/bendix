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

  Class ids inside data go stale when classes merge; every use runs
  them through `find`, and cromulent recomputes the data of every
  class whose nodes or children change, so stale ids never survive a
  rebuild.

  Two different polynomials in one class are an equation the e-graph
  asserts and the ring cannot prove: a user assumption, a true
  identity from outside the ring (sin²x + cos²x = 1), or an unsound
  rule. The join keeps the smaller form under bendix.poly's
  well-founded order, so a class settles after finitely many changes.
  The equation is also used: cromulent hands `reconcile` the forms
  that met in a class, and when two of them differ by α·v + β for a
  single atom v, v is unioned with the constant -β/α (a = a/2 gives
  a = 0; a = 2a + 1 gives a = -1). Under a ring-only rule set no such
  pair can be sound, which is what `inconsistency` checks in dev
  mode."
  (:require [bendix.poly :as poly]
            [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn- exact? [x]
  (or (integer? x) (ratio? x)))

(defn atom? [d] (and (map? d) (contains? d :atom)))

(defn polynomial? [d] (and (map? d) (not (contains? d :atom))))

(defn canonical
  "d with every class-id atom replaced by its root in g."
  [g d]
  (cond
    (atom? d) {:atom (eg/find g (:atom d))}
    (polynomial? d) (poly/map-atoms #(if (keyword? %) % (eg/find g %)) d)
    :else d))

(defn- as-poly [d]
  (if (atom? d) (poly/variable (:atom d)) d))

(defn- ring-op
  "The polynomial of a compound node over its children's data, or
  ::opaque when the operator is not a ring operation over ℚ."
  [g node too-big]
  (let [op (term/operator node)
        ds (mapv #(canonical g (eg/data g % :poly)) (term/children node))
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
          :else result)))))

(defn- the-make [g]
  (:make (some #(when (= :poly (:name %)) %) (:analyses g))))

(defn threshold
  "The :too-big term-count threshold of g's polynomial analysis."
  [g]
  (:too-big (some #(when (= :poly (:name %)) %) (:analyses g))))

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
                (let [[g vid] (if (keyword? v) (eg/add g v) [g v])
                      [g cid] (eg/add g value)]
                  (first (eg/union g vid cid)))
                g))
            g
            (for [i (range (count fs)), j (range (inc i) (count fs))] [(nth fs i) (nth fs j)]))))

(defn poly-analysis
  "The polynomial normal-form analysis. Options: :too-big, the term
  count past which a normal form is abandoned (default 200)."
  ([] (poly-analysis {}))
  ([{:keys [too-big] :or {too-big 200}}]
   {:name :poly
    :too-big too-big
    :make (fn [g node id]
            (cond
              (exact? node) (poly/constant node)
              (keyword? node) (poly/variable node)
              (term/compound? node) (let [r (ring-op g node too-big)]
                                      (if (= ::opaque r) {:atom id} r))
              :else {:atom id}))
    :merge (fn [g a b]
             (let [a (canonical g a), b (canonical g b)]
               (cond
                 (= a b) a
                 (or (= :conflict a) (= :conflict b)) :conflict
                 (atom? a) b
                 (atom? b) a
                 (or (= :too-big a) (= :too-big b)) :too-big
                 :else (let [d (poly/sub a b)]
                         (if (poly/constant? d)
                           :conflict
                           (poly/smaller a b))))))
    :reconcile (fn [g _ datas] (solve g datas))
    :modify (fn [g id]
              (let [d (canonical g (eg/data g id :poly))]
                (if-not (polynomial? d)
                  g
                  (let [r (eg/find g id)
                        other (get-in g [:analysis-state :poly d])]
                    (if (and other (not= (eg/find g other) r))
                      (first (eg/union g other r))
                      (assoc-in g [:analysis-state :poly d] r))))))}))

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
