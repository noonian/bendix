(ns bendix.core
  "The simplifier: add a term, saturate under rules and the polynomial
  analysis, materialize normal forms, extract the cheapest term.

    (simplify [:+ [:* 2 :x] [:* 3 :x]])
    ;; => {:result [:* 5 :x] :cost 3 :stop :saturated :assuming #{}}

  Options: :rules (default none), :cost (default `default-cost`),
  :dev? (check the normal forms after every rule application and
  throw naming the rule), :too-big, and the runner's limits."
  (:require [bendix.analysis :as an]
            [bendix.poly :as poly]
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

(defn default-cost
  "AST size, with a slight preference for the operators normal forms
  are written in: x/2 and (1/2)·x have the same size, and this picks
  the latter. Exact, so results are the same on every runtime."
  [node child-costs]
  (+ (if (and (term/compound? node) (not (contains? normal-form-operators (term/operator node))))
       65/64
       1)
     (reduce + child-costs)))

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
  ([t {:keys [rules dev? too-big] :or {rules []} :as opts}]
   (let [g (egraph (if too-big {:too-big too-big} {}))
         [g root] (eg/add g t)
         res (rw/embiggen g rules (cond-> (select-keys opts runner-keys)
                                    dev? (assoc :check an/inconsistency)))]
     (assoc res :root root))))

(defn simplify
  "The cheapest form of t under the rules and cost function."
  ([t] (simplify t {}))
  ([t {:keys [cost dev?] :or {cost default-cost} :as opts}]
   (let [{:keys [egraph root stop-reason]} (saturate t opts)
         g (materialize-all egraph)]
     (when dev?
       (when-let [problem (an/inconsistency g)]
         (throw (ex-info "inconsistent normal forms after materialization" problem))))
     (let [{:keys [term cost]} (ex/extract g root cost)]
       {:result term :cost cost :stop stop-reason :assuming #{}}))))
