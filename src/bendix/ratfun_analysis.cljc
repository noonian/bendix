(ns bendix.ratfun-analysis
  "The rational-function analysis: every class carries the normal form
  of its value as a rational function over ℚ (bendix.ratfun), and
  classes with the same form are merged. Where the polynomial analysis
  (bendix.analysis) sees 1/x as an opaque atom, this one sees through
  division, so a partial-fraction identity, or any two spellings of
  one rational function, is proved by the index and never runs as a
  rule.

  Data of a class under :ratfun is one of

    form       a bendix.ratfun value over atoms that are variables
               (keywords) or the ids of opaque classes
    {:atom id} the class is opaque (holds no node this analysis can
               compute): it is its own indeterminate
    :too-big   a form past the size threshold, or one whose building
               would pass it
    :undefined a form whose denominator the e-graph has since proved
               zero (1/(x − y) once x = y): no value, and below any
               other data in a merge

  A division by a class whose form is zero, or a power that is not an
  integer constant, is opaque.

  As in the polynomial analysis, ids inside a form go stale when
  classes merge, and an opaque class may later be proved equal to a
  form; `canonical` maps every atom to its root and replaces an atom
  whose class now has a form by that form, so neither survives a
  rebuild.

  Classes are indexed by `bendix.ratfun/index-key`, which equal
  rational functions share however their denominators are split, so
  the index merges every two spellings of one function. Two forms of
  one function that meet in a class are joined into their common
  refinement (`bendix.ratfun/join`), whatever order they arrive in.

  Two forms of different functions in one class are an equation the
  e-graph asserts that the normal form does not prove: a user
  assumption, an identity from outside the field (sin²x + cos²x = 1),
  or an unsound rule. The class keeps the smaller under
  `bendix.ratfun/compare-ratfuns`, and indexes both, so either merges
  the class with any other that has it. `inconsistency` lists such
  classes, for tests.

  Scope: ℚ coefficients and free atoms; no exponent laws, no coefficient
  algebras. The polynomial analysis has both, and the two can run in
  one e-graph."
  (:require [bendix.ratfun :as rf]
            [bendix.term :as bt]
            [cromulent.core :as eg]
            [cromulent.term :as term]))

(def analysis-name :ratfun)

(defn atom? [d] (and (map? d) (contains? d :atom)))

(defn form? [d] (rf/ratfun? d))

(defn- the-analysis [g]
  (some #(when (= analysis-name (:name %)) %) (:analyses g)))

(defn threshold
  "The :too-big size threshold of g's rational-function analysis."
  [g]
  (:too-big (the-analysis g)))

;; ---------------------------------------------------------------------------
;; canonical forms

(declare canonical*)

(defn- atom-class
  "The class an atom names now: a variable's class if some variable is
  defined (`note-defined-variables`) and the graph holds this one, an
  id's root."
  [g a]
  (if (bt/variable? a)
    (when (contains? (get-in g [:analysis-state ::defined]) a) (eg/lookup g a))
    (eg/find g a)))

(defn- itself
  "The form an atom is when nothing defines it: the variable, or the
  root of the class id."
  [g a]
  (rf/variable (if (bt/variable? a) a (eg/find g a))))

(defn- definition
  "What the atom a stands for in a canonical form: its class's form if
  that is a form other than the atom itself and no chain of
  definitions reaches a class in visited; else the atom itself.
  ::too-big past the limit, ::undefined when a denominator in the
  definition is now zero."
  [g a visited limit]
  (let [r (atom-class g a)
        d (when r (eg/data g r analysis-name))
        self (itself g a)]
    (if (or (nil? r) (not (form? d)) (= d self) (contains? visited r))
      self
      (canonical* g d (conj visited r) limit))))

(defn- canonical*
  [g d visited limit]
  (let [as (rf/atoms d)
        subst (into {} (map (fn [a] [a (definition g a visited limit)])) as)]
    (cond
      (some #{::too-big} (vals subst)) ::too-big
    (some #{::undefined} (vals subst)) ::undefined
      (every? (fn [[a r]] (= r (rf/variable a))) subst) d
      :else (let [r (rf/substitute d subst limit)]
              (cond (nil? r) ::undefined
                    (= rf/too-big r) ::too-big
                    :else r)))))

(defn canonical
  "d with every atom replaced by its root and every atom whose class
  now has a form replaced by that form. An atom whose chain of
  definitions reaches itself stays an atom; a form past the threshold
  is :too-big, and one with a denominator now zero :undefined. An atom
  or a keyword is returned as it is, its id mapped to its root."
  [g d]
  (cond
    (atom? d) {:atom (eg/find g (:atom d))}
    (form? d) (let [r (canonical* g d #{} (threshold g))]
                (case r ::too-big :too-big ::undefined :undefined r))
    :else d))

(defn- as-form [g d]
  (if (atom? d) (rf/variable (eg/find g (:atom d))) d))

;; ---------------------------------------------------------------------------
;; make

(def field-operators #{:+ :* :neg :- :/ :expt})

(defn- integer-exponent
  [d]
  (when (form? d)
    (let [k (rf/constant-value d)]
      (when (and (some? k) (integer? k)) k))))

(defn- field-op
  "The form of a compound node over its children's data, ::opaque when
  the node is not field arithmetic this analysis can fold, :too-big
  when a child is or the result would be."
  [g node too-big]
  (let [op (term/operator node)]
    (if-not (contains? field-operators op)
      ::opaque
      (let [ds (mapv #(canonical g (eg/data g % analysis-name)) (term/children node))
            n (count ds)]
        (cond
          (some nil? ds) ::opaque
          (some #{:undefined} ds) ::opaque
          (some #{:too-big} ds) :too-big
          :else
          (let [fs (mapv #(as-form g %) ds)
                result (case op
                         :+ (rf/sum fs)
                         :* (rf/product fs)
                         :neg (when (= 1 n) (rf/neg (fs 0)))
                         :- (case n 1 (rf/neg (fs 0)) 2 (rf/sub (fs 0) (fs 1)) nil)
                         :/ (when (= 2 n) (rf/div (fs 0) (fs 1) too-big))
                         :expt (when (= 2 n)
                                 (when-let [e (integer-exponent (ds 1))]
                                   (rf/expt (fs 0) e too-big)))
                         nil)]
            (cond
              (nil? result) ::opaque
              (= rf/too-big result) :too-big
              (> (rf/size result) too-big) :too-big
              :else result)))))))

;; ---------------------------------------------------------------------------
;; the index

(defn- index-form
  "Union the class of id with the class the index holds under the
  form f's `bendix.ratfun/index-key`, if another; else index it under
  id. Returns g'."
  [g id f]
  (let [k (rf/index-key f)
        r (eg/find g id)
        other (get-in g [:analysis-state analysis-name k])]
    (if (and other (not= (eg/find g other) r))
      (first (eg/union g other r :ratfun))
      (assoc-in g [:analysis-state analysis-name k] r))))

(defn- key-of [g d]
  (let [d (canonical g d)]
    (cond (form? d) d
          (atom? d) (rf/variable (:atom d)))))

(defn- built-from?
  "Is the class of a reachable from the class of c through the
  children of nodes this analysis cannot compute: is c, as structure
  the field cannot see through, built from a? As in bendix.analysis,
  field nodes are equations a class records and are not followed."
  [g c a too-big]
  (let [a (eg/find g a)]
    (loop [stack [(eg/find g c)], seen #{}]
      (if (empty? stack)
        false
        (let [r (peek stack), stack (pop stack)]
          (cond
            (= r a) true
            (contains? seen r) (recur stack seen)
            :else (recur (into stack
                               (for [n (eg/nodes g r)
                                     :when (and (term/compound? n) (= ::opaque (field-op g n too-big)))
                                     ch (term/children n)]
                                 (eg/find g ch)))
                         (conj seen r))))))))

(defn- defines?
  "Does the form d define the opaque class id: is it a form that
  mentions neither id nor an atom built from id? A form over an atom
  built from id spells id over its own structure (a primitive over
  its derivative), which bendix.analysis's derivative soak found
  holding a class to a bloated definition; it is an equation the class
  records, and the atom stays."
  [g d id too-big]
  (and (form? d)
       (not (contains? (rf/atoms d) id))
       (not-any? #(built-from? g % id too-big)
                 (filter bt/class-id? (rf/atoms d)))))

(defn- note-defined-variables
  "Record every variable whose class is worth something other than
  itself, so that `canonical` looks up no other variable. Returns g'."
  [g id d]
  (reduce (fn [g v]
            (if (and (form? d) (= d (rf/variable v)))
              (update-in g [:analysis-state ::defined] disj v)
              (update-in g [:analysis-state ::defined] (fnil conj #{}) v)))
          g
          (filter bt/variable? (eg/nodes g id))))

;; ---------------------------------------------------------------------------
;; the analysis

(defn ratfun-analysis
  "The rational-function normal-form analysis. Option :too-big, the
  form size (bendix.ratfun/size) past which a class gives up
  (default 1000)."
  ([] (ratfun-analysis {}))
  ([{:keys [too-big] :or {too-big 1000}}]
   {:name analysis-name
    :too-big too-big
    :make (fn [g node id]
            (cond
              (bt/constant? node) (rf/constant node)
              (bt/variable? node) (rf/variable node)
              (term/compound? node) (let [r (field-op g node too-big)]
                                      (if (= ::opaque r) {:atom id} r))
              :else {:atom id}))
    :merge (fn [g a b]
             (let [a (canonical g a), b (canonical g b)]
               (cond
                 (nil? a) b
                 (nil? b) a
                 (= :undefined a) b
                 (= :undefined b) a
                 (and (form? a) (form? b)) (if (rf/same-function? a b) (rf/join a b) (rf/smaller a b))
                 (= a b) a
                 (and (atom? a) (atom? b)) (if (< (:atom a) (:atom b)) a b)
                 (atom? a) (if (or (= :too-big b) (defines? g b (:atom a) too-big)) b a)
                 (atom? b) (if (or (= :too-big a) (defines? g a (:atom b) too-big)) a b)
                 :else :too-big)))
    :reconcile (fn [g id datas]
                 (reduce (fn [g d] (if-let [k (key-of g d)] (index-form g id k) g))
                         g
                         (distinct datas)))
    :modify (fn [g id]
              (let [d (canonical g (eg/data g id analysis-name))
                    g (note-defined-variables g id d)]
                (if-let [k (key-of g d)]
                  (index-form g id k)
                  g)))}))

(defn egraph
  "An e-graph carrying the rational-function analysis. opts as
  `ratfun-analysis` takes them, and :explain? for cromulent."
  ([] (egraph {}))
  ([opts] (eg/egraph {:analyses [(ratfun-analysis opts)] :explain? (:explain? opts)})))

(defn form
  "The canonical data of the class of id: a form, {:atom id} or
  :too-big."
  [g id]
  (canonical g (eg/data g id analysis-name)))

(defn forms
  "The canonical forms the nodes of the class of r compute, with the
  stored data, one per function (`bendix.ratfun/index-key`)."
  [g r]
  (let [make (:make (the-analysis g))]
    (into #{}
          (comp (map #(canonical g %)) (filter form?) (map rf/index-key))
          (cons (eg/data g r analysis-name)
                (map #(make g (eg/canonicalize g %) r) (eg/nodes g r))))))

(defn inconsistency
  "nil when every class's nodes compute one function, else the first
  class whose nodes compute more than one, with their index keys."
  [g]
  (some (fn [r]
          (let [fs (forms g r)]
            (when (< 1 (count fs)) {:class r :forms fs})))
        (eg/roots g)))
