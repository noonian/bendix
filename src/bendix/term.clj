(ns bendix.term
  "The CAS's vocabulary over cromulent's term seam.

  cromulent.term knows the shape of a node (operator, children) and
  nothing else; what a leaf means is the CAS's decision (IDEA.md
  section 1), and this namespace is the one place that decision is
  read:

    variable     a keyword in leaf position                :x
    constant     an exact number                           2, 1/2
    class id     an integer naming an e-class; occurs only in
                 analysis data and placeholders, never in a term
    placeholder  a node over class ids that the graph may not hold
                 yet, which a rule renders as a pattern to create it

  An atom of a polynomial (bendix.poly) is a variable, a class id or
  a placeholder. Rules and analyses ask their questions here rather
  than testing types in place, so the format can change (a record, a
  protocol) in one namespace."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

;; ---------------------------------------------------------------------------
;; leaves and atoms

(defn variable?
  "Is x a variable (a keyword in leaf position)?"
  [x]
  (keyword? x))

(defn constant?
  "Is x a constant (an exact number)?"
  [x]
  (or (integer? x) (ratio? x)))

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

(defn placeholder
  "The placeholder for the node op over the class ids."
  [op ids]
  (term/make op ids))

(defn class-ids
  "Every class id a placeholder mentions, as a set."
  [p]
  (if (term/compound? p)
    (into #{} (mapcat class-ids) (term/children p))
    #{p}))

(defn map-class-ids
  "p with every class id replaced by (f id), placeholders inside
  placeholders included."
  [f p]
  (if (term/compound? p)
    (term/map-children #(map-class-ids f %) p)
    (f p)))

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
