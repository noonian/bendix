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
  power; `powers` holds it. `combine-exp` is its mirror image: in
  every monomial, the factors that are powers of exponentials become
  one exponential of the sum of their arguments; `exp-log` holds it
  with the pattern rule `log-of-exp`.

  `derivative` (IDEA.md section 3, \"Differentiation\") differentiates:
  `ring-derivative` is a normal-form rule over the pattern [:D ?u ?x]
  that computes the total derivative of ?u's polynomial, so linearity,
  the product rule and folded powers are polynomial calculus and not
  rules; the chain rule is one pattern rule per operator; and
  `independent` is [:D ?u ?x] = 0 when ?u cannot depend on ?x."
  (:require [bendix.analysis :as an]
            [bendix.poly :as poly]
            [bendix.term :as bt]
            [cromulent.core :as eg]
            [cromulent.pattern :as pat]
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

(defn- matches-for
  "One match per polynomial, carrying its rendering as :rhs and the
  rendering's bindings merged into the match's."
  [class bindings polys]
  (map (fn [p']
         (let [[pattern b] (render p')]
           {:class class :bindings (merge bindings b) :rhs pattern}))
       (distinct polys)))

(defn normal-form-rule
  "A rule whose left-hand side is f, (fn [g id p] polys): the other
  polynomials the class id, whose canonical form is p, is worth. f
  sees every class whose data is a polynomial, and every opaque class
  as its unit polynomial {{id 1} 1}, and may return nil. Each
  polynomial becomes one match carrying its rendering as :rhs.

  With a pattern, f is (fn [g bindings] polys) and sees the pattern's
  matches instead of every root: the polynomials the matched class is
  worth, given what the pattern bound."
  ([name f]
   (rw/rule name
            (fn [g]
              (into []
                    (mapcat (fn [r]
                              (let [d (an/canonical g (eg/data g r :poly))
                                    p (cond (an/polynomial? d) d
                                            (an/atom? d) (poly/variable (:atom d)))]
                                (when p
                                  (matches-for r {} (f g r p))))))
                    (eg/roots g)))
            nil))
  ([name pattern f]
   (rw/rule name
            (fn [g]
              (into []
                    (mapcat (fn [{:keys [class bindings]}]
                              (matches-for class bindings (f g bindings))))
                    (pat/ematch g pattern)))
            nil)))

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
;; exp-log

(defn- exp-factor
  "When the atom a of a monomial is a power of an exponential, that
  is, `factor` finds a base whose class holds [:exp u]: {:u u :k k
  :sym S} for exp(u)^(k + S). Else nil."
  [g a]
  (let [{:keys [base k sym]} (factor g a)]
    (when-let [n (bt/node-with g base :exp)]
      (when (= 1 (term/arity n))
        {:u (term/child n 0) :k k :sym sym}))))

(defn- scaled
  "The placeholder for coeff · u, coeff a constant or a placeholder: u
  itself when coeff is 1."
  [coeff u]
  (if (= 1 coeff) (bt/class-ref u) (bt/placeholder :* [coeff (bt/class-ref u)])))

(defn- collect-monomial
  "m with its exponential factors collected into one exponential of
  the sum of their scaled arguments, or nil when m holds none, or
  exactly one to the first power."
  [g m]
  (let [fs (keep (fn [[a e]] (when-let [f (exp-factor g a)] (assoc f :atom a :e e))) m)
        lone? (and (= 1 (count fs))
                   (let [f (nth fs 0)] (and (= 1 (:e f)) (= 1 (:k f)) (nil? (:sym f)))))]
    (when (and (seq fs) (not lone?))
      (let [by-u (reduce (fn [acc {:keys [u k sym e]}]
                           (cond-> (update-in acc [u :k] (fnil +' 0) (*' k e))
                             sym (update-in [u :syms sym] (fnil +' 0) e)))
                         {}
                         fs)
            terms (keep (fn [[u {:keys [k syms]}]]
                          (let [coeff (exponent-placeholder k (or syms {}))]
                            (when-not (= 0 coeff) (scaled coeff u))))
                        (sort-by key by-u))
            arg (case (count terms)
                  0 0
                  1 (nth terms 0)
                  (bt/placeholder :+ (vec terms)))]
        (assoc (reduce dissoc m (map :atom fs)) (bt/placeholder :exp [arg]) 1)))))

(defn exp-forms
  "p with every monomial's exponential factors collected, when that
  changes anything: the polynomial rewrite behind `combine-exp`."
  [g _ p]
  (let [p' (reduce-kv (fn [acc m c] (poly/add acc {(or (collect-monomial g m) m) c}))
                      poly/zero
                      p)]
    (when (not= p' p) [p'])))

(def combine-exp
  "exp(a)·exp(b) = exp(a + b) and exp(a)^n = exp(n·a), inside every
  monomial, for whatever exponent the factors carry: the exponential
  factors of a monomial become one exponential of the sum of their
  scaled arguments, which the analysis then normalizes. Sound on the
  reals wherever the input is defined, exp being never zero; exp 0
  folds to 1 in the analysis."
  (normal-form-rule "combine-exp" exp-forms))

(def log-of-exp
  "log(exp x) = x."
  (rw/rule "log-of-exp" '[:log [:exp ?x]] '?x))

(def exp-log
  "The exp-log rule set, its unconditional part: exp(log x) = x and
  log(ab) = log a + log b wait for the sign lattice (IDEA.md
  section 5)."
  [combine-exp log-of-exp])

;; ---------------------------------------------------------------------------
;; derivative

(defn- undefined-variable
  "The variable the class of id is, when it holds a variable leaf and
  is worth that variable and nothing else; nil otherwise."
  [g id]
  (let [d (an/canonical g (eg/data g id :poly))]
    (when (an/polynomial? d)
      (some (fn [n] (when (and (bt/variable? n) (= (poly/variable n) d)) n))
            (eg/nodes g id)))))

(defn- constant-data
  "The constant the class of id is worth, or nil."
  [g id]
  (let [d (an/canonical g (eg/data g id :poly))]
    (when (an/polynomial? d) (poly/constant-value d))))

(defn derivative-form
  "The total derivative of the polynomial p with respect to the
  variable x, whose class is xid: Σ ∂p/∂a · D(a) over the atoms a of
  p, with D(x) = 1, D(y) = 0 for another variable (canonical forms
  are spelled over undefined atoms, which are independent of x by
  convention) and D(c) = the placeholder [:D c x] for an opaque
  class c."
  [p x xid]
  (poly/sum (keep (fn [a]
                    (cond
                      (= a x) (poly/derivative p a)
                      (bt/variable? a) nil
                      :else (poly/mul (poly/derivative p a)
                                      (poly/variable (bt/placeholder :D [(bt/class-ref a) (bt/class-ref xid)])))))
                  (poly/atoms p))))

(defn ring-derivative-forms
  "The polynomial rewrite behind `ring-derivative`: for a match of
  [:D ?u ?x] where ?x is an undefined variable and ?u's canonical
  data is a polynomial, that polynomial's total derivative. Declines
  when ?u is opaque (the chain rules' case), :too-big or :conflict."
  [g bindings]
  (let [xid (get bindings '?x)
        uid (get bindings '?u)]
    (when-let [x (undefined-variable g xid)]
      (let [d (an/canonical g (eg/data g uid :poly))]
        (when (an/polynomial? d)
          [(derivative-form d x xid)])))))

(def ring-derivative
  "The derivative of a class worth a polynomial, computed from the
  polynomial: linearity, the product rule and the power rule for the
  exponents the analysis folds never run as rules."
  (normal-form-rule "ring-derivative" '[:D ?u ?x] ring-derivative-forms))

(defn independent?
  "Can the value of the class of id not depend on the undefined
  variable x? Yes when its canonical polynomial mentions no atom that
  depends on x, an undefined variable depending on x only when it is
  x; or, for an opaque or :too-big class, when some constant leaf or
  compound node of the class has only children that cannot depend on
  x. A :conflict class, a variable leaf in a class with other data
  and a class already on the walk count as depending."
  [g id x]
  (letfn [(indep? [id visited]
            (let [r (eg/find g id)]
              (if (contains? visited r)
                false
                (let [visited (conj visited r)
                      d (an/canonical g (eg/data g r :poly))]
                  (cond
                    (an/polynomial? d)
                    (every? (fn [a] (if (bt/variable? a) (not= a x) (indep? a visited)))
                            (poly/atoms d))
                    (= :conflict d) false
                    :else
                    (boolean (some (fn [n]
                                     (cond
                                       (bt/constant? n) true
                                       (term/compound? n) (every? #(indep? % visited) (term/children n))
                                       :else false))
                                   (eg/nodes g r))))))))]
    (indep? id #{})))

(def independent
  "[:D u x] = 0 when u cannot depend on x: d/dx π, d/dx |y|, d/dx f(y)
  for any operator f."
  (rw/rule "independent" '[:D ?u ?x] 0
           :when (fn [g bindings]
                   (let [x (undefined-variable g (get bindings '?x))]
                     (and (some? x) (independent? g (get bindings '?u) x))))))

(def d-sin (rw/rule "d-sin" '[:D [:sin ?u] ?x] '[:* [:cos ?u] [:D ?u ?x]]))
(def d-cos (rw/rule "d-cos" '[:D [:cos ?u] ?x] '[:* -1 [:sin ?u] [:D ?u ?x]]))
(def d-exp (rw/rule "d-exp" '[:D [:exp ?u] ?x] '[:* [:exp ?u] [:D ?u ?x]]))
(def d-log
  "Spelled as a negative power, so `powers` can combine it."
  (rw/rule "d-log" '[:D [:log ?u] ?x] '[:* [:expt ?u -1] [:D ?u ?x]]))

(def d-quotient
  "(a'b − ab')·b⁻², for the divisions the analysis holds as atoms:
  division by a constant is a ring operation and needs no rule."
  (rw/rule "d-quotient" '[:D [:/ ?a ?b] ?x]
           '[:* [:- [:* [:D ?a ?x] ?b] [:* ?a [:D ?b ?x]]] [:expt ?b -2]]
           :when (fn [g bindings] (nil? (constant-data g (get bindings '?b))))))

(def d-power
  "n·u^(n−1)·u' for a non-zero constant n. For a non-negative integer
  n the analysis has folded the power and `ring-derivative` covers
  it, but the factored spelling this proposes is one the class would
  not otherwise hold. When u' is a constant the rule folds it in, so
  3(x+1)² carries no ·1."
  (rw/rule "d-power" '[:D [:expt ?u ?n] ?x]
           (fn [g bindings]
             (let [n (constant-data g (get bindings '?n))
                   xid (get bindings '?x)
                   x (undefined-variable g xid)
                   d (when x (an/canonical g (eg/data g (get bindings '?u) :poly)))
                   du (when (an/polynomial? d) (poly/constant-value (derivative-form d x xid)))]
               (cond
                 (or (nil? n) (zero? n)) nil
                 (nil? du) [:* n [:expt '?u (- n 1)] [:D '?u '?x]]
                 (zero? du) 0
                 :else [:* (*' n du) [:expt '?u (- n 1)]])))))

(def d-power-symbolic
  "u^v (v·u'/u + log u · v'), spelled v·u^(v−1)·u' + u^v·log u·v', for
  an exponent that is not a constant; when v cannot depend on x the
  second term is a product with a class worth zero and the analysis
  drops it. Holds where u > 0 (IDEA.md section 5)."
  (rw/rule "d-power-symbolic" '[:D [:expt ?u ?v] ?x]
           '[:+ [:* ?v [:expt ?u [:+ ?v -1]] [:D ?u ?x]]
                [:* [:expt ?u ?v] [:log ?u] [:D ?v ?x]]]
           :when (fn [g bindings] (nil? (constant-data g (get bindings '?v))))))

(def derivative
  "The derivative rule set. A :D no rule removes stays; `bendix.core/no-D`
  counts it and `differentiate` reports it."
  [ring-derivative independent d-sin d-cos d-exp d-log d-quotient d-power d-power-symbolic])

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
