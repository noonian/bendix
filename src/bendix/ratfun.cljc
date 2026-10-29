(ns bendix.ratfun
  "Rational functions over ℚ in a normal form: a numerator, expanded,
  over a denominator kept as a product of factors.

    {:num p :den {d e ...}}

  p is a bendix.poly polynomial; each d is a non-constant polynomial
  with leading coefficient 1 (`bendix.poly/leading-term`) and e its
  positive exponent; no d divides p. Zero is {:num {} :den {}}; a
  polynomial is itself over the empty denominator. Plain maps, so
  equality is structural and a form can key an index.

  A denominator factor comes from inverting a polynomial. Its scalar
  and the content of its monomials are split off, so that x·y·(x − y)
  becomes the factors x, y and x − y, and what remains is one factor.
  The form is unique, so equal rational functions have equal forms,
  whenever every factor is irreducible: then no factor divides the
  numerator, distinct factors are coprime, and ℚ[atoms] factors
  uniquely. A product remembers how its numerator factors (`hint`),
  so (x − y)·(x + y) inverted gives two factors. A reducible
  polynomial with no such history (x² − y² inverted) is kept whole,
  and the form may then be one of several for its function. Equal
  forms always mean equal functions: the normal form is sound
  everywhere and complete where the factors are irreducible, which a
  denominator that is a product of linear forms always is.

  Atoms are those of bendix.poly: keywords, class ids, placeholders.
  The ring is free: no exponent laws, ℚ coefficients only."
  (:refer-clojure :exclude [zero?])
  (:require [bendix.num :as num]
            [bendix.poly :as poly]))

;; ---------------------------------------------------------------------------
;; construction

(def zero {:num poly/zero :den {}})

(def one {:num (poly/constant 1) :den {}})

(defn from-poly [p] {:num p :den {}})

(defn constant [k] (from-poly (poly/constant k)))

(defn variable [v] (from-poly (poly/variable v)))

(defn zero? [r] (empty? (:num r)))

(defn polynomial?
  "Is r a polynomial (an empty denominator)?"
  [r]
  (empty? (:den r)))

(defn constant-value
  "k when r is the constant k, else nil."
  [r]
  (when (polynomial? r) (poly/constant-value (:num r))))

(defn ratfun?
  "Is x a form of this namespace?"
  [x]
  (and (map? x) (contains? x :num) (contains? x :den)))

;; ---------------------------------------------------------------------------
;; normalizing

(defn- den-poly
  "The denominator of r expanded."
  [den]
  (reduce-kv (fn [acc d e] (poly/mul acc (poly/expt d e))) (poly/constant 1) den))

(defn hint
  "Polynomials whose product is r's numerator up to a non-zero scalar:
  what is known of how the numerator factors, kept as metadata so it
  never changes a form's equality or hash. A product remembers its
  operands' hints, so inverting x·y·(x − y)·(x + y) written as a
  product gives the factors one at a time and not their expansion,
  which no content split could take apart. Absent, the numerator
  itself."
  [r]
  (or (::factors (meta r)) [(:num r)]))

(defn- with-hint [r hs]
  (if (and hs (seq (:num r)))
    (with-meta r {::factors (vec (remove poly/constant? hs))})
    r))

(defn- divide-hint
  "hs with one of its polynomials divided by d, or nil when none is
  divisible by it."
  [hs d]
  (loop [i 0]
    (when (< i (count hs))
      (if-let [q (poly/divide (nth hs i) d)]
        (assoc hs i q)
        (recur (inc i))))))

(defn- cancel
  "num over den with every factor divided out of num as often as it
  divides it. hs, a hint for num (see `hint`), is kept up to date, or
  dropped when a division cannot be read off one of its polynomials."
  ([num den] (cancel num den nil))
  ([num den hs]
   (if (empty? num)
     zero
     (loop [num num, hs (some-> hs vec), out {}, ds (seq den)]
       (if-let [[[d e] & more] ds]
         (let [[num hs e] (loop [num num, hs hs, e e]
                            (if-let [q (when (pos? e) (poly/divide num d))]
                              (recur q (some-> hs (divide-hint d)) (dec e))
                              [num hs e]))]
           (recur num hs (if (pos? e) (assoc out d e) out) more))
         (with-hint {:num num :den out} hs))))))

(defn- content
  "p as [c m q]: p = c · m · q, c a rational, m a monomial whose atoms
  divide every term of p, and q with leading coefficient 1 and no
  such atom. p is not zero."
  [p]
  (let [atoms (poly/atoms p)
        m (into {}
                (keep (fn [v]
                        (let [e (reduce min (map #(get (key %) v 0) p))]
                          (when (pos? e) [v e]))))
                atoms)
        q (poly/divide p {m 1})
        c (poly/leading-coefficient q)]
    [c m (poly/scale q (num/div 1 c))]))

(defn- factors
  "The denominator factors of r's non-zero numerator, as [c den]:
  numerator = c · Π d^e. Each polynomial of r's hint is split into
  its scalar, its monomial content and the rest."
  [r]
  (let [den (reduce (fn [den h]
                      (let [[_ m q] (content h)]
                        (cond-> (reduce-kv (fn [den v e] (update den (poly/variable v) (fnil + 0) e)) den m)
                          (not (poly/constant? q)) (update q (fnil + 0) 1))))
                    {}
                    (hint r))]
    ;; every d has leading coefficient 1 and the order is
    ;; multiplicative, so the product's leading coefficient is 1 too
    [(poly/leading-coefficient (:num r)) den]))

;; ---------------------------------------------------------------------------
;; arithmetic

(defn add [a b]
  (cond
    (zero? a) b
    (zero? b) a
    :else
    (let [den (merge-with max (:den a) (:den b))
          lift (fn [{:keys [num] d :den}]
                 (poly/mul num (den-poly (into {} (keep (fn [[f e]]
                                                         (let [k (- e (get d f 0))]
                                                           (when (pos? k) [f k]))))
                                                       den))))]
      (cancel (poly/add (lift a) (lift b)) den))))

(defn sum [rs] (reduce add zero rs))

(defn neg [r] (update r :num poly/neg))

(defn sub [a b] (add a (neg b)))

(defn scale [r k] (if (clojure.core/zero? k) zero (update r :num poly/scale k)))

(defn mul [a b]
  (if (or (zero? a) (zero? b))
    zero
    (cancel (poly/mul (:num a) (:num b)) (merge-with + (:den a) (:den b)) (into (hint a) (hint b)))))

(defn product [rs] (reduce mul one rs))

(defn inverse
  "1/r, or nil for zero."
  [r]
  (when-not (zero? r)
    (let [[c den] (factors r)]
      (cancel (poly/scale (den-poly (:den r)) (num/div 1 c)) den (vec (mapcat (fn [[d e]] (repeat e d)) (:den r)))))))

(defn div
  "a/b, or nil when b is zero."
  [a b]
  (some->> (inverse b) (mul a)))

(defn expt
  "r to the integer power n; nil for a negative power of zero."
  [r n]
  (cond
    (neg? n) (some-> (inverse r) (expt (- n)))
    (clojure.core/zero? n) one
    :else (cancel (poly/expt (:num r) n) (into {} (map (fn [[d e]] [d (* e n)])) (:den r))
                  (vec (apply concat (repeat n (hint r)))))))

;; ---------------------------------------------------------------------------
;; reading

(defn atoms
  "The atoms r mentions."
  [r]
  (into (poly/atoms (:num r)) (mapcat poly/atoms) (keys (:den r))))

(defn size
  "Terms in the numerator and in every denominator factor."
  [r]
  (reduce + (poly/term-count (:num r)) (map poly/term-count (keys (:den r)))))

(defn evaluate
  "The value of r under env, a map from atom to rational; nil where
  the denominator vanishes."
  [r env]
  (let [d (poly/evaluate (den-poly (:den r)) env)]
    (when-not (clojure.core/zero? d)
      (num/div (poly/evaluate (:num r) env) d))))

(defn- evaluate-poly
  "p with each atom v replaced by (f v), a form, as a form."
  [p f]
  (reduce-kv (fn [acc m c]
               (add acc (scale (reduce-kv (fn [x v e] (mul x (expt (f v) e))) one m) c)))
             zero
             p))

(defn substitute
  "r with each atom v replaced by (f v), a form. Atoms that become
  equal combine, and the result is normalized again. nil when a
  denominator factor becomes zero."
  [r f]
  (reduce-kv (fn [acc d e] (when acc (some->> (expt (evaluate-poly d f) (- e)) (mul acc))))
             (evaluate-poly (:num r) f)
             (:den r)))

(defn compare-ratfuns
  "A total, well-founded order: smaller `size` first, then the
  denominators expanded and the numerators by `bendix.poly/compare-polys`.
  A lexicographic product of well-founded orders is well-founded, so a
  class that keeps the smallest form it derives changes finitely often."
  [a b]
  (let [c (compare (size a) (size b))]
    (if (not= 0 c)
      c
      (let [c (poly/compare-polys (den-poly (:den a)) (den-poly (:den b)))]
        (if (not= 0 c) c (poly/compare-polys (:num a) (:num b)))))))

(defn smaller [a b] (if (pos? (compare-ratfuns a b)) b a))

;; ---------------------------------------------------------------------------
;; to terms

(defn ->term
  "r as a term: the numerator's canonical term over the product of the
  factors in `bendix.poly/compare-polys` order, a power for an
  exponent past 1. atom->term renders an atom (`bendix.poly/->term`)."
  ([r] (->term r identity))
  ([r atom->term]
   (let [n (poly/->term (:num r) atom->term)
         ds (mapv (fn [[d e]]
                    (let [t (poly/->term d atom->term)]
                      (if (= 1 e) t [:expt t e])))
                  (sort-by key poly/compare-polys (:den r)))]
     (case (count ds)
       0 n
       1 [:/ n (ds 0)]
       [:/ n (into [:*] ds)]))))
