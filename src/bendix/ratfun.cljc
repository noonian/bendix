(ns bendix.ratfun
  "Rational functions over ℚ in a normal form: a numerator, expanded,
  over a denominator kept as a product of factors.

    {:num p :den {d e ...}}

  p is a bendix.poly polynomial; each d is a non-constant polynomial
  with leading coefficient 1 (`bendix.poly/leading-term`) and e its
  positive exponent. Every d is squarefree, every two are coprime, and
  none shares a factor with p (each checked with `bendix.poly/gcd`).
  Zero is {:num {} :den {}}; a polynomial is itself over the empty
  denominator. Plain maps, so a form can key an index.

  A denominator factor comes from inverting a polynomial. Its scalar
  and the content of its monomials are split off, so that x·y·(x − y)
  becomes the factors x, y and x − y, and what remains is one factor,
  refined by gcds against the others. A product remembers how its
  numerator factors (`hint`), so (x − y)·(x + y) inverted gives two
  factors; x² − y² inverted with no such history is one. Without
  factoring polynomials the split into factors is therefore not
  unique, but the function's `index-key` is: the numerator and the
  denominator's squarefree parts, which equal rational functions
  always share. Compare and index forms by it (`same-function?`), and
  `join` two splittings of one function into their common
  refinement.

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

(def too-big
  "What an operation given a size limit returns past it."
  ::too-big)

(defn- size* [r]
  (reduce + (poly/term-count (:num r)) (map poly/term-count (keys (:den r)))))

(defn- over? [r limit] (and limit (> (size* r) limit)))

(defn- den-poly
  "The denominator of r expanded; nil past limit terms."
  ([den] (den-poly den nil))
  ([den limit]
   (reduce-kv (fn [acc d e]
                (let [acc (some->> (poly/expt d e limit) (poly/mul acc))]
                  (if (or (nil? acc) (and limit (> (count acc) limit))) (reduced nil) acc)))
              (poly/constant 1)
              den)))

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

(defn- add-factor [den d e]
  (if (or (clojure.core/zero? e) (poly/constant? d)) den (update den d (fnil + 0) e)))

(defn- common-factor
  "The non-constant gcd of p and the factor d, or nil when they are
  coprime. A linear d is irreducible, so it divides p or is coprime."
  ([p d] (common-factor p (poly/atoms p) d))
  ([p p-atoms d]
   (cond
    (poly/constant? p) nil
    (not-any? p-atoms (poly/atoms d)) nil
    (= 1 (poly/degree d)) (when (poly/divide p d) d)
    :else (let [g (poly/gcd p d)] (when-not (poly/constant? g) g)))))

(defn- split-once
  "den with one factor that is not squarefree, or one pair of factors
  that are not coprime, split by a gcd; nil when every factor is
  squarefree and every two are coprime."
  [den]
  (let [fs (vec (keys den))]
    (or (some (fn [d]
                (when (< 1 (poly/degree d))
                  (some (fn [v]
                          (let [g (poly/gcd d (poly/derivative d v))]
                            (when-not (poly/constant? g)
                              (-> (dissoc den d)
                                  (add-factor g (den d))
                                  (add-factor (poly/divide d g) (den d))))))
                        (poly/atoms d))))
              fs)
        (some (fn [[a b]]
                (when-let [g (common-factor a b)]
                  (-> (dissoc den a b)
                      (add-factor g (+ (den a) (den b)))
                      (add-factor (poly/divide a g) (den a))
                      (add-factor (poly/divide b g) (den b)))))
              (for [i (range (count fs)), j (range (inc i) (count fs))] [(fs i) (fs j)])))))

(defn- basis
  "den with its factors refined until each is squarefree and every two
  are coprime; the product is unchanged. Each split lowers the factors'
  total degree or, at the same degree, adds a factor, so it ends."
  [den]
  ;; distinct factors with leading coefficient 1, all linear, are
  ;; already squarefree and coprime: the common case, and ribbon's
  (if (every? #(= 1 (poly/degree %)) (keys den))
    den
    (loop [den den]
      (if-let [den' (split-once den)] (recur den') den))))

(defn- divide-hint
  "hs with d divided out of its polynomials, piece by piece, or nil when
  d does not divide their product."
  [hs d]
  (loop [i 0, hs hs, d d]
    (cond
      (poly/constant? d) hs
      (= i (count hs)) nil
      :else (if-let [g (common-factor (nth hs i) d)]
              (recur i (assoc hs i (poly/divide (nth hs i) g)) (poly/divide d g))
              (recur (inc i) hs d)))))

(defn- cancel
  "num over den in normal form: den's factors refined (`basis`), then
  every factor that shares a factor with num split by their gcd and the
  shared part divided out of num. hs, a hint for num (see `hint`), is
  kept up to date, or dropped when a division cannot be read off it."
  ([num den] (cancel num den nil))
  ([num den hs]
   (if (empty? num)
     zero
     (loop [num num, hs (some-> hs vec), den (basis den)]
       (if-let [[d g] (let [as (poly/atoms num)]
                        (some (fn [d] (when-let [g (common-factor num as d)] [d g])) (keys den)))]
         (let [e (den d)]
           (if (= g d)
             (recur (poly/divide num d) (some-> hs (divide-hint d)) (add-factor (dissoc den d) d (dec e)))
             (recur num hs (basis (-> (dissoc den d) (add-factor g e) (add-factor (poly/divide d g) e))))))
         (with-hint {:num num :den den} hs))))))

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

(defn- factor-map
  "Polynomials hs as a factorization {d e}: each split into its scalar,
  its monomial content and the rest, with leading coefficient 1."
  [hs]
  (reduce (fn [den h]
            (let [[_ m q] (content h)]
              (reduce-kv (fn [den v e] (add-factor den (poly/variable v) e))
                         (add-factor den q 1)
                         m)))
          {}
          hs))

(defn- factors
  "The denominator factors of r's non-zero numerator, as [c den]:
  numerator = c · Π d^e, read off r's hint."
  [r]
  ;; every d has leading coefficient 1 and the order is
  ;; multiplicative, so the product's leading coefficient is 1 too
  [(poly/leading-coefficient (:num r)) (factor-map (hint r))])

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
  "1/r, or nil for zero. With a limit, `too-big` when the expanded
  denominator or the result passes limit terms."
  ([r] (inverse r nil))
  ([r limit]
   (when-not (zero? r)
     (let [[c den] (factors r)
           d (den-poly (:den r) limit)]
       (if (nil? d)
         too-big
         (let [r' (cancel (poly/scale d (num/div 1 c)) den (vec (mapcat (fn [[d e]] (repeat e d)) (:den r))))]
           (if (over? r' limit) too-big r')))))))

(defn div
  "a/b, or nil when b is zero. With a limit, `too-big` past it."
  ([a b] (div a b nil))
  ([a b limit]
   (let [i (inverse b limit)]
     (if (or (nil? i) (= too-big i))
       i
       (let [r (mul a i)] (if (over? r limit) too-big r))))))

(defn expt
  "r to the integer power n; nil for a negative power of zero. With a
  limit, `too-big` as soon as a power being built passes limit terms."
  ([r n] (expt r n nil))
  ([r n limit]
   (cond
     (neg? n) (let [i (inverse r limit)]
                (if (or (nil? i) (= too-big i)) i (expt i (- n) limit)))
     (clojure.core/zero? n) one
     :else (if-let [p (poly/expt (:num r) n limit)]
             (let [r' (cancel p (into {} (map (fn [[d e]] [d (* e n)])) (:den r))
                              (vec (apply concat (repeat n (hint r)))))]
               (if (over? r' limit) too-big r'))
             too-big))))

;; ---------------------------------------------------------------------------
;; reading

(defn atoms
  "The atoms r mentions."
  [r]
  (into (poly/atoms (:num r)) (mapcat poly/atoms) (keys (:den r))))

(defn size
  "Terms in the numerator and in every denominator factor."
  [r]
  (size* r))

(defn evaluate
  "The value of r under env, a map from atom to rational; nil where
  the denominator vanishes."
  [r env]
  (let [d (poly/evaluate (den-poly (:den r)) env)]
    (when-not (clojure.core/zero? d)
      (num/div (poly/evaluate (:num r) env) d))))

(defn- evaluate-poly
  "p with each atom v replaced by (f v), a form, as a form; `too-big`
  past limit."
  [p f limit]
  (reduce-kv (fn [acc m c]
               (let [t (reduce-kv (fn [x v e]
                                    (let [x (let [pw (expt (f v) e limit)]
                                              (when-not (= too-big pw) (mul x pw)))]
                                      (if (or (nil? x) (over? x limit)) (reduced nil) x)))
                                  one
                                  m)
                     acc (when t (add acc (scale t c)))]
                 (if (or (nil? acc) (over? acc limit)) (reduced too-big) acc)))
             zero
             p))

(defn substitute
  "r with each atom v replaced by (f v), a form. Atoms that become
  equal combine, and the result is normalized again. The numerator is
  substituted one polynomial of its hint at a time, so what is known
  of how it factors survives. nil when a denominator factor becomes
  zero; with a limit, `too-big` as soon as a form being built passes
  limit terms."
  ([r f] (substitute r f nil))
  ([r f limit]
   (if (zero? r)
     zero
     (let [hs (hint r)
           s (num/div (poly/leading-coefficient (:num r))
                      (reduce num/mul 1 (map poly/leading-coefficient hs)))
           step (fn [acc x] (cond (= too-big x) (reduced too-big)
                                  (nil? x) (reduced nil)
                                  :else (let [r (mul acc x)] (if (over? r limit) (reduced too-big) r))))
           n (reduce step (constant s) (map #(evaluate-poly % f limit) hs))]
       (reduce-kv (fn [acc d e]
                    (if (or (nil? acc) (= too-big acc))
                      (reduced acc)
                      (let [b (evaluate-poly d f limit)]
                        (if (= too-big b)
                          (reduced too-big)
                          (let [x (expt b (- e) limit)]
                            (step acc x))))))
                  n
                  (:den r))))))

;; ---------------------------------------------------------------------------
;; equality and order

(defn index-key
  "What two forms of one rational function share, however their
  denominators are split into factors: the numerator and, for each
  exponent e, the product of the factors raised to e. With every
  factor squarefree and every two coprime (`cancel`'s invariant) that
  product is the denominator's squarefree part of multiplicity e,
  which is unique, and the numerator is coprime to the denominator,
  which is monic; so equal functions have equal keys and unequal
  functions unequal ones. Expanded per exponent, not whole, so a high
  power of one factor stays small."
  [r]
  {:num (:num r)
   :den (reduce-kv (fn [acc d e] (update acc e (fnil poly/mul (poly/constant 1)) d)) {} (:den r))})

(defn same-function?
  "Are a and b forms of one rational function?"
  [a b]
  (= (index-key a) (index-key b)))

(defn- multiplicity [d b]
  (loop [d d, k 0]
    (if-let [q (poly/divide d b)] (recur q (inc k)) k)))

(defn- refine
  "The common refinement of two factorizations {d e} of one polynomial:
  the `basis` of their factors together, each element with the
  exponent that keeps a's product."
  [a b]
  (if (= a b)
    a
    (let [bs (keys (basis (merge-with + a b)))]
      (reduce-kv (fn [acc d e]
                   (reduce (fn [acc x] (add-factor acc x (* e (multiplicity d x)))) acc bs))
                 {}
                 a))))

(defn join
  "a and b, two forms of one rational function (`same-function?`), as
  one form that keeps what each knows of how it factors: the common
  refinement of their denominators and of their hints. Symmetric, so a
  class that meets both forms in any order ends with the same one."
  [a b]
  (let [ma (::factors (meta a)), mb (::factors (meta b))
        hs (cond (nil? ma) mb
                 (nil? mb) ma
                 (= ma mb) ma
                 :else (vec (mapcat (fn [[d e]] (repeat e d))
                                    (refine (factor-map ma) (factor-map mb)))))]
    (with-hint {:num (:num a) :den (refine (:den a) (:den b))} hs)))

(defn- compare-seqs [cmp xs ys]
  (let [c (compare (count xs) (count ys))]
    (if (not= 0 c)
      c
      (or (first (remove #{0} (map cmp xs ys))) 0))))

(defn- compare-entries [[e1 p1] [e2 p2]]
  (let [c (compare e1 e2)]
    (if (not= 0 c) c (poly/compare-polys p1 p2))))

(defn compare-ratfuns
  "A total, well-founded order: smaller `size` first, then the
  denominators' `index-key` parts, the numerators by
  `bendix.poly/compare-polys`, and last the factors themselves, which
  tells apart two splittings of one function. A lexicographic product
  of well-founded orders is well-founded, so a class that keeps the
  smallest form it derives changes finitely often."
  [a b]
  (let [c (compare (size a) (size b))]
    (if (not= 0 c)
      c
      (let [c (compare-seqs compare-entries (sort-by key (:den (index-key a))) (sort-by key (:den (index-key b))))]
        (if (not= 0 c)
          c
          (let [c (poly/compare-polys (:num a) (:num b))]
            (if (not= 0 c)
              c
              (let [fs #(sort compare-entries (map (fn [[d e]] [e d]) (:den %)))]
                (compare-seqs compare-entries (fs a) (fs b))))))))))

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

;; ---------------------------------------------------------------------------
;; Laurent expansion in one atom

(defn laurent
  "The first n terms of r's Laurent expansion in the atom v, about
  v = ∞ (the default) or v = 0 (`at` :zero): a vector of [k c], c the
  coefficient of v^k, a rational function of the other atoms, with k
  falling from the leading power at ∞ and rising from the lowest at 0.
  The first entry is the leading term and is never zero; later
  coefficients may be. Exact: the expansion is series division of the
  numerator by the denominator, both written as polynomials in v.
  Empty for zero."
  ([r v n] (laurent r v n :infinity))
  ([r v n at]
   (when-not (and (integer? n) (<= 0 n))
     (throw (ex-info "laurent takes a number of terms n ≥ 0" {:n n})))
   (when-not (#{:infinity :zero} at)
     (throw (ex-info "laurent expands at :infinity or :zero" {:at at})))
   (if (zero? r)
     []
     (let [num-c (poly/coefficients-in (:num r) v)
           den-c (poly/coefficients-in (den-poly (:den r)) v)
           ;; read the coefficients outward from the leading end: at ∞
           ;; from the top power down, at 0 from the bottom power up
           [pick dir] (if (= at :zero) [min 1] [max -1])
           a (reduce pick (keys num-c))
           b (reduce pick (keys den-c))
           nth-num (fn [i] (from-poly (get num-c (+ a (* dir i)) poly/zero)))
           nth-den (fn [j] (from-poly (get den-c (+ b (* dir j)) poly/zero)))
           lead (nth-den 0)]
       (loop [k 0, cs []]
         (if (= k n)
           (vec (map-indexed (fn [i c] [(+ (- a b) (* dir i)) c]) cs))
           (let [c (div (reduce (fn [acc j] (sub acc (mul (nth-den j) (nth cs (- k j)))))
                                (nth-num k)
                                (range 1 (inc k)))
                        lead)]
             (recur (inc k) (conj cs c)))))))))

(defn leading
  "[k c]: the leading power of the atom v in r at v = ∞ (or at v = 0
  with `at` :zero) and its coefficient; nil for zero."
  ([r v] (leading r v :infinity))
  ([r v at] (first (laurent r v 1 at))))
