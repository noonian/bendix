(ns bendix.term
  "The CAS's vocabulary over cromulent's term seam.

  cromulent.term knows the shape of a node (operator, children) and
  nothing else; what a leaf means is the CAS's decision (IDEA.md
  section 1), and this namespace is the one place that decision is
  read:

    variable     a keyword in leaf position                :x
    constant     an exact number (bendix.num)              2, 1/2
    class id     an integer naming an e-class; occurs only in
                 analysis data and placeholders, never in a term
    placeholder  a node the graph may not hold yet, over class
                 references and constants, which a rule renders as a
                 pattern to create it
    class ref    {:class id} inside a placeholder, so that a constant
                 leaf (an exponent, say) is not mistaken for an id

  An atom of a polynomial (bendix.poly) is a variable, a class id or
  a placeholder. Rules and analyses ask their questions here rather
  than testing types in place, so the format can change (a record, a
  protocol) in one namespace."
  (:require [bendix.num :as num]
            [cromulent.core :as eg]
            [cromulent.term :as term]))

;; ---------------------------------------------------------------------------
;; leaves and atoms

(defn variable?
  "Is x a variable (a keyword in leaf position)?"
  [x]
  (keyword? x))

(defn constant?
  "Is x a constant (an exact number: an integer or a ratio)?"
  [x]
  (num/rational? x))

(defn class-id?
  "Is a, an atom of a polynomial, an e-class id?"
  [a]
  (integer? a))

(defn placeholder?
  "Is a, an atom of a polynomial, a placeholder (a node over class ids)?"
  [a]
  (term/compound? a))

;; ---------------------------------------------------------------------------
;; placeholders

(defn class-ref
  "A reference to the class id, as a placeholder leaf."
  [id]
  {:class id})

(defn class-ref?
  [x]
  (and (map? x) (contains? x :class)))

(defn placeholder
  "The placeholder for the node op over its children: class
  references, constants, or placeholders."
  [op children]
  (term/make op children))

(defn class-ids
  "Every class id a placeholder refers to, as a set."
  [p]
  (cond
    (term/compound? p) (into #{} (mapcat class-ids) (term/children p))
    (class-ref? p) #{(:class p)}
    :else #{}))

(defn map-class-ids
  "p with every class reference replaced by (f id), placeholders
  inside placeholders included; constants stay."
  [f p]
  (cond
    (term/compound? p) (term/map-children #(map-class-ids f %) p)
    (class-ref? p) (f (:class p))
    :else p))

;; ---------------------------------------------------------------------------
;; reading classes

(defn nodes-with
  "The canonical nodes of the class of id whose operator is in ops
  (a set), as a vector in cromulent's node order, so callers are
  deterministic across runtimes."
  [g id ops]
  (->> (eg/nodes g id)
       (filter #(and (term/compound? %) (contains? ops (term/operator %))))
       (sort term/compare-nodes)
       vec))

(defn node-with
  "The first canonical node with operator op in the class of id, or
  nil."
  [g id op]
  (nth (nodes-with g id #{op}) 0 nil))
