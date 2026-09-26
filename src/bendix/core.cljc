(ns bendix.core
  "The simplifier: add a term, saturate under rules and the polynomial
  analysis, materialize normal forms, extract the cheapest term.

    (simplify [:+ [:* 2 :x] [:* 3 :x]])
    ;; => {:result [:* 5 :x] :cost 3 :stop :saturated :assuming #{}}

  Options: :rules (default none), :cost (default `default-cost`; a
  function of the saturated e-graph that returns a cromulent cost
  function, so a plain cost f is `(constantly f)`), :dev? (check the
  normal forms after every rule application and throw naming the
  rule), :too-big for the analysis (bendix.analysis/poly-analysis),
  and the runner's limits.

  The costs that ship are `default-cost` and `no-D`. Under them and
  the rule sets that ship, equal spellings of a value reach one cost
  and the cost of a result is a fixpoint; any other cost function is
  sound and promises nothing more (IDEA.md section 6).

    (differentiate [:sin [:* 2 :x]] :x)
    ;; => {:result [:* 2 [:cos [:* 2 :x]]] :cost [0 385/64] ... :undifferentiated #{}}

  is `simplify` of [:D t x] under the derivative rules and `no-D`, a
  cost that counts what is still under a :D before size (IDEA.md
  section 3, \"Differentiation\")."
  (:require [bendix.analysis :as an]
            [bendix.poly :as poly]
            [bendix.rules :as rules]
            [bendix.term :as bt]
            [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.rewrite :as rw]
            [cromulent.term :as term]))

(defn egraph
  "An e-graph carrying the polynomial analysis."
  ([] (egraph {}))
  ([opts] (eg/egraph {:analyses [(an/poly-analysis opts)]})))

(def normal-form-operators #{:+ :* :expt})

(defn size
  "AST size, with a slight preference for the operators normal forms
  are written in: x/2 and (1/2)·x have the same size, and this picks
  the latter. Exact, so results are the same on every runtime: 65/64
  is a ratio on the JVM and Jolt and the exact double 1.015625 in
  JavaScript, written as a division because the ClojureScript
  compiler has no ratio constant. A plain cromulent cost;
  `default-cost` is this and a charge."
  [node child-costs]
  (+ (if (and (term/compound? node) (not (contains? normal-form-operators (term/operator node))))
       (/ 65 64)
       1)
     (reduce + child-costs)))

(defn- product?
  [node]
  (and (term/compound? node) (= :* (term/operator node))))

(defn- product-bases
  "Class id -> `bendix.rules/power-bases` of it, for every class that is a
  child of a :* node of g."
  [g]
  (reduce (fn [table r]
            (reduce (fn [table node]
                      (if (product? node)
                        (reduce (fn [table c]
                                  (if (contains? table c) table (assoc table c (rules/power-bases g c))))
                                table
                                (term/children node))
                        table))
                    table
                    (eg/nodes g r)))
          {}
          (eg/roots g)))

(defn- repeated-bases
  "How many bases appear in more than one child of the :* node."
  [g table node]
  (let [seen (reduce (fn [seen c]
                       (reduce (fn [seen b] (update seen b (fnil inc 0)))
                               seen
                               (get table (eg/find g c))))
                     {}
                     (term/children node))]
    (count (filter #(< 1 (val %)) seen))))

(def repeated-base-charge
  "What a :* node pays for each base that appears in more than one of
  its children. One power per base is never more than a node larger
  than the same product with the base repeated, so 2 makes it the
  cheaper by at least one (IDEA.md section 6)."
  2)

(defn default-cost
  "The default cost for the e-graph g: `size`, and a product pays
  `repeated-base-charge` for each base it repeats, so y · y^n loses to
  y^(n+1) and y · y to y^2, as the established systems print them. The
  bases of a child are read from its class's canonical form
  (`bendix.rules/power-bases`), so the charge sees through nesting. A
  constant on a node: monotone as `size` is."
  [g]
  (let [table (product-bases g)]
    (fn [node child-costs]
      (cond-> (size node child-costs)
        (product? node) (+ (* repeated-base-charge (repeated-bases g table node)))))))

(defn no-D
  "A vector cost for the e-graph g, [undifferentiated size]: the sizes
  of the arguments of every :D node summed, then `default-cost`.
  Compared lexicographically by the extractor, so a derivative pushed
  inward always beats the same derivative left whole, a
  derivative-free spelling beats any other, and the cheapest of those
  wins. Monotone: the first component never decreases from a child to
  its parent and the second strictly increases."
  [g]
  (let [size-cost (default-cost g)]
    (fn [node child-costs]
      (let [size (size-cost node (mapv second child-costs))
            under (reduce + 0 (map first child-costs))]
        [(if (and (term/compound? node) (= :D (term/operator node)) (pos? (term/arity node)))
           (+ under (second (nth child-costs 0)))
           under)
         size]))))

(defn materialize
  "Add the normal form of the class of id as a term and union it in,
  so extraction can choose it. Returns g'. Opaque atoms render as
  their cheapest term."
  [g id]
  (let [d (an/canonical g (eg/data g id :poly))]
    (if-not (an/polynomial? d)
      g
      (let [best (ex/extractor g)
            t (poly/->term d (fn [a] (if (bt/variable? a) a (:term (best a)))))
            [g nid] (eg/add g t)]
        (eg/rebuild (first (eg/union g nid id)))))))

(defn materialize-all
  "Materialize every class's normal form: one extractor for the
  renderings, every term added, one union each, one rebuild. Adding
  to a dirty e-graph is what the runner's apply phase does too."
  [g]
  (let [best (ex/extractor g)
        render (fn [a] (if (bt/variable? a) a (:term (best a))))]
    (eg/rebuild
     (reduce (fn [g r]
               (let [d (an/canonical g (eg/data g r :poly))]
                 (if-not (an/polynomial? d)
                   g
                   (let [[g nid] (eg/add g (poly/->term d render))]
                     (first (eg/union g nid r))))))
             g
             (eg/roots g)))))

(def ^:private runner-keys
  [:iter-limit :node-limit :time-limit-ms :scheduler :match-limit :ban-length :timeline?])

(defn saturate
  "Add t and run rules to saturation or a limit; the e-graph and the
  root come back with the runner's result."
  ([t] (saturate t {}))
  ([t {:keys [rules dev?] :or {rules []} :as opts}]
   (let [g (egraph (select-keys opts [:too-big]))
         [g root] (eg/add g t)
         res (rw/embiggen g rules (cond-> (select-keys opts runner-keys)
                                    dev? (assoc :check an/inconsistency)))]
     (assoc res :root root))))

(defn term-cost
  "What the term t costs as it is written, under the cromulent cost
  function cost-fn in g. Every subterm of t must be in g, as the
  subterms of what was added are."
  [g cost-fn t]
  (letfn [(walk [t]
            (if (term/compound? t)
              (let [kids (mapv walk (term/children t))
                    node (term/make (term/operator t) (mapv :id kids))]
                {:id (eg/lookup g node) :cost (cost-fn node (mapv :cost kids))})
              {:id (eg/lookup g t) :cost (cost-fn t [])}))]
    (:cost (walk t))))

(defn simplify
  "The cheapest form of t under the rules and the cost, a function of
  the saturated e-graph that returns a cromulent cost function
  (`default-cost`, `no-D`, or `(constantly f)` for a plain f)."
  ([t] (simplify t {}))
  ([t {:keys [cost dev?] :or {cost default-cost} :as opts}]
   (let [{:keys [egraph root stop-reason]} (saturate t opts)
         g (materialize-all egraph)]
     (when dev?
       (when-let [problem (an/inconsistency g)]
         (throw (ex-info "inconsistent normal forms after materialization" problem))))
     (let [{:keys [term cost]} (ex/extract g root (cost g))]
       {:result term :cost cost :stop stop-reason :assuming #{}}))))

(defn- subterms-with
  "The set of subterms of t headed by op."
  [op t]
  (if (term/compound? t)
    (into (if (= op (term/operator t)) #{t} #{})
          (mapcat #(subterms-with op %))
          (term/children t))
    #{}))

(defn differentiate
  "The derivative of t with respect to the variable x: `simplify` of
  [:D t x] under `bendix.rules/derivative` together with the caller's
  :rules, extracted under `no-D`. The result adds :undifferentiated,
  the set of :D subterms no rule could remove, empty when the
  derivative is complete."
  ([t x] (differentiate t x {}))
  ([t x opts]
   (when-not (bt/variable? x)
     (throw (ex-info "the variable of differentiation must be a variable" {:variable x})))
   (let [rules (into [] (distinct) (concat rules/derivative (:rules opts)))
         res (simplify [:D t x] (assoc opts :rules rules :cost no-D))]
     (assoc res :undifferentiated (subterms-with :D (:result res))))))
