(ns bendix.poly
  "Sparse multivariate polynomials over a coefficient algebra.

  A polynomial is a map from monomial to non-zero coefficient; a
  monomial is a map from atom to positive integer exponent. The zero
  polynomial is {}, the constant k is {{} k}, 2x + x² is
  {{:x 1} 2, {:x 2} 1}. Plain maps, so equality is structural and
  hashing is what the e-graph's analysis index needs; a total order
  (`compare-polys`) exists for the cases that need a canonical choice,
  and it is well-founded: below any polynomial there are only finitely
  many others, which is what lets an e-class analysis that keeps the
  smallest form converge.

  Coefficients come from a bendix.algebra. Each function that touches
  a coefficient takes the algebra as its first argument; the arities
  without it use `bendix.algebra/rational`. Where an optional limit
  exists, the algebra arity takes it explicitly (nil for none). A
  polynomial does not carry its algebra; callers pass it consistently.

  Exponents come from the atoms. `laws`, a function from atom to
  bendix.exponent law (nil: every atom is free), says which powers of
  an atom are equal, and each function that multiplies monomials takes
  it after the algebra and keeps every exponent canonical under it:
  with x idempotent, x · x is x. Under laws a polynomial is the normal
  form of an element of the quotient by them. The arities without laws
  are the free polynomial ring; `derivative` and `reduce-square` have
  no other.

  Atoms are opaque here; bendix.term says what they mean (a
  variable, an e-class id, a placeholder). This namespace only orders
  them: keywords first, then integers, then anything else by its
  printed form. `map-atoms` renames them; `substitute` replaces them
  by polynomials."
  (:require [bendix.algebra :as alg]
            [bendix.exponent :as ex]
            [bendix.num :as num]))

;; ---------------------------------------------------------------------------
;; construction and arithmetic

(def zero {})

(defn constant
  ([k] (constant alg/rational k))
  ([algebra k] (if (alg/zero? algebra k) zero {{} k})))

(defn variable
  ([v] (variable alg/rational v))
  ([algebra v] {{v 1} (alg/one algebra)}))

(defn constant-value
  "k if p is the constant k, else nil."
  ([p] (constant-value alg/rational p))
  ([algebra p]
   (cond
     (empty? p) (alg/zero algebra)
     (and (= 1 (count p)) (contains? p {})) (get p {})
     :else nil)))

(defn constant?
  ([p] (constant? alg/rational p))
  ([algebra p] (some? (constant-value algebra p))))

(defn- add-term [algebra p m c]
  (let [c' (if-let [c0 (get p m)] (alg/add algebra c0 c) c)]
    (if (alg/zero? algebra c') (dissoc p m) (assoc p m c'))))

(defn add
  ([p q] (add alg/rational p q))
  ([algebra p q] (reduce-kv (fn [acc m c] (add-term algebra acc m c)) p q)))

(defn scale
  ([p k] (scale alg/rational p k))
  ([algebra p k]
   (if (alg/zero? algebra k)
     zero
     ;; products can vanish when the algebra has zero divisors
     (reduce-kv (fn [acc m c]
                  (let [c' (alg/mul algebra c k)]
                    (if (alg/zero? algebra c') acc (assoc acc m c'))))
                {}
                p))))

(defn neg
  ([p] (neg alg/rational p))
  ([algebra p] (scale algebra p (alg/neg algebra (alg/one algebra)))))

(defn sub
  ([p q] (sub alg/rational p q))
  ([algebra p q] (add algebra p (neg algebra q))))

(defn- times-power
  "The monomial m times v^e, the exponent of v canonical under its
  law; v drops out when that exponent is 0."
  [laws m v e]
  (let [e' (ex/normalize (when laws (laws v)) (+ (get m v 0) e))]
    (if (zero? e') (dissoc m v) (assoc m v e'))))

(defn- mul-monomials [laws m1 m2]
  (if (nil? laws)
    (merge-with + m1 m2)
    (reduce-kv (fn [m v e] (times-power laws m v e)) m1 m2)))

(defn mul
  ([p q] (mul alg/rational nil p q))
  ([algebra p q] (mul algebra nil p q))
  ([algebra laws p q]
   (reduce-kv (fn [acc m1 c1]
                (reduce-kv (fn [acc m2 c2] (add-term algebra acc (mul-monomials laws m1 m2) (alg/mul algebra c1 c2)))
                           acc
                           q))
              zero
              p)))

(defn expt
  "p to a non-negative integer power, by squaring. With a limit, nil
  as soon as any intermediate result has more terms than the limit."
  ([p n] (expt alg/rational nil p n nil))
  ([p n limit] (expt alg/rational nil p n limit))
  ([algebra p n limit] (expt algebra nil p n limit))
  ([algebra laws p n limit]
   (let [ok? (fn [q] (or (nil? limit) (<= (count q) limit)))]
     (loop [acc (constant algebra (alg/one algebra)), base p, n n]
       (cond
         (not (and (ok? acc) (ok? base))) nil
         (zero? n) acc
         (odd? n) (recur (mul algebra laws acc base) (if (= 1 n) base (mul algebra laws base base)) (quot n 2))
         :else (recur acc (mul algebra laws base base) (quot n 2)))))))

(defn inverse
  "p⁻¹ when p is a unit the algebra and the laws can see: one term
  whose coefficient is a unit and whose atoms are all units (laws of
  index 0), v^e becoming v^(period − e). nil otherwise; without laws,
  for anything but a unit constant."
  ([algebra p] (inverse algebra nil p))
  ([algebra laws p]
   (when (= 1 (count p))
     (let [[m c] (first p)
           c' (alg/inv algebra c)]
       (when (and c' (every? #(ex/unit? (when laws (laws %))) (keys m)))
         {(reduce-kv (fn [m' v e] (times-power laws m' v (- e))) {} m) c'})))))

(defn reduce-square
  "p modulo a² − q: every a^e becomes a^(e mod 2)·q^(e div 2), so a
  appears at most linearly. With a limit, nil as soon as an
  intermediate result has more terms than the limit. This is
  reduction by the single-polynomial Gröbner basis {a² − q}; for
  q = 1 − c² it is the Pythagorean identity."
  ([p v q] (reduce-square alg/rational p v q nil))
  ([p v q limit] (reduce-square alg/rational p v q limit))
  ([algebra p v q limit]
   (let [ok? (fn [r] (or (nil? limit) (<= (count r) limit)))]
     (reduce-kv (fn [acc m c]
                  (when acc
                    (let [e (get m v 0)]
                      (if (< e 2)
                        (add-term algebra acc m c)
                        (let [m' (if (odd? e) (assoc m v 1) (dissoc m v))
                              qk (expt algebra q (quot e 2) limit)
                              acc' (when qk (add algebra acc (scale algebra (mul algebra {m' (alg/one algebra)} qk) c)))]
                          (when (and acc' (ok? acc')) acc'))))))
                zero
                p))))

(defn derivative
  "∂p/∂v: the partial derivative of p with respect to the atom v,
  every other atom held constant. Each monomial holding v^e becomes
  the monomial with v^(e−1) and its coefficient times the image of e
  in the algebra; a polynomial that does not mention v gives zero.
  Formal: an atom with a law has no derivative (x² = x would make
  2x = 1)."
  ([p v] (derivative alg/rational p v))
  ([algebra p v]
   (reduce-kv (fn [acc m c]
                (let [e (get m v 0)]
                  (if (zero? e)
                    acc
                    (add-term algebra acc (if (= 1 e) (dissoc m v) (assoc m v (dec e))) (alg/mul algebra c (alg/from-integer algebra e))))))
              zero
              p)))

(defn sum
  ([ps] (sum alg/rational ps))
  ([algebra ps] (reduce #(add algebra %1 %2) zero ps)))

(defn product
  ([ps] (product alg/rational nil ps))
  ([algebra ps] (product algebra nil ps))
  ([algebra laws ps] (reduce #(mul algebra laws %1 %2) (constant algebra (alg/one algebra)) ps)))

(defn term-count [p] (count p))

(defn degree
  "Total degree; -1 for zero."
  [p]
  (reduce max -1 (map (fn [[m _]] (reduce + 0 (vals m))) p)))

(defn atoms
  "The set of atoms p mentions."
  [p]
  (into #{} (mapcat keys) (keys p)))

(defn map-atoms
  "p with every atom replaced by (f atom). Atoms that map to the same
  atom combine, as do terms that become equal."
  ([f p] (map-atoms alg/rational nil f p))
  ([algebra f p] (map-atoms algebra nil f p))
  ([algebra laws f p]
   (reduce-kv (fn [acc m c]
                (add-term algebra acc (reduce-kv (fn [m' v e] (mul-monomials laws m' {(f v) e})) {} m) c))
              zero
              p)))

(defn under
  "The free polynomial p under the laws: every exponent made
  canonical, terms that become equal combined."
  [algebra laws p]
  (map-atoms algebra laws identity p))

(defn substitute
  "p with every atom that subst maps replaced by the polynomial it
  maps to; other atoms stay. With a limit, nil as soon as an
  intermediate result has more terms than the limit."
  ([p subst] (substitute alg/rational nil p subst nil))
  ([p subst limit] (substitute alg/rational nil p subst limit))
  ([algebra p subst limit] (substitute algebra nil p subst limit))
  ([algebra laws p subst limit]
   (let [ok? (fn [q] (or (nil? limit) (<= (count q) limit)))]
     (reduce-kv (fn [acc m c]
                  (let [q (reduce-kv (fn [q v e]
                                       (let [r (get subst v)
                                             pe (if (nil? r) {{v e} (alg/one algebra)} (expt algebra laws r e limit))
                                             q' (when pe (mul algebra laws q pe))]
                                         (if (and q' (ok? q')) q' (reduced nil))))
                                     (constant algebra (alg/one algebra))
                                     m)
                        acc' (when q (add algebra acc (scale algebra q c)))]
                    (if (and acc' (ok? acc')) acc' (reduced nil))))
                zero
                p))))

(defn evaluate
  "The value of p under env, a map from atom to coefficient."
  ([p env] (evaluate alg/rational p env))
  ([algebra p env]
   (reduce-kv (fn [acc m c]
                (alg/add algebra acc (alg/mul algebra c (reduce-kv (fn [x v e] (alg/mul algebra x (alg/pow algebra (get env v) e)))
                                                   (alg/one algebra)
                                                   m))))
              (alg/zero algebra)
              p)))

;; ---------------------------------------------------------------------------
;; ordering

(defn- atom-key [v]
  (cond (keyword? v) [0 (str v)]
        (integer? v) [1 v]
        :else [2 (pr-str v)]))

(defn- monomial-key
  "Graded lexicographic: higher total degree first, then the sorted
  atom/exponent list."
  [m]
  [(- (reduce + 0 (vals m)))
   (vec (sort (map (fn [[v e]] [(atom-key v) (- e)]) m)))])

(defn sorted-terms
  "The terms of p as [monomial coefficient] pairs in canonical order."
  [p]
  (sort-by (fn [[m _]] (monomial-key m)) compare p))

(defn- compare-coefficients [algebra x y]
  (let [c (compare (alg/size algebra x) (alg/size algebra y))]
    (if (not= 0 c) c (alg/cmp algebra x y))))

(defn compare-polys
  "A total order: fewer terms first, then lower degree, then smaller
  coefficients by the algebra's size, then term by term in canonical order comparing
  monomials, then coefficients by the algebra's order. Every component
  before the last is a natural number or a choice among finitely
  many, so the order is well-founded: no infinite descending chain
  exists, and a class that keeps the smallest form it derives can
  only change finitely often."
  ([p q] (compare-polys alg/rational p q))
  ([algebra p q]
   (let [c (compare (term-count p) (term-count q))]
     (if (not= 0 c)
       c
       (let [c (compare (degree p) (degree q))]
         (if (not= 0 c)
           c
           (let [c (compare (reduce num/add 0 (map #(alg/size algebra %) (vals p)))
                            (reduce num/add 0 (map #(alg/size algebra %) (vals q))))]
             (if (not= 0 c)
               c
               (loop [ps (sorted-terms p), qs (sorted-terms q)]
                 (if (empty? ps)
                   0
                   (let [[[mp cp] & ps] ps, [[mq cq] & qs] qs
                         c (compare (monomial-key mp) (monomial-key mq))]
                     (if (not= 0 c)
                       c
                       (let [c (compare-coefficients algebra cp cq)]
                         (if (not= 0 c) c (recur ps qs)))))))))))))))

(defn linear-in-one-atom
  "When p is α·v + β for one atom v and α a unit, [v (- β/α)]: the
  value of v that makes p zero. Otherwise nil."
  ([p] (linear-in-one-atom alg/rational p))
  ([algebra p]
   (let [as (atoms p)]
     (when (and (= 1 (count as)) (= 1 (degree p)))
       (let [v (first as)
             alpha (get p {v 1})
             beta (get p {} (alg/zero algebra))]
         (when (and alpha (<= (count p) 2))
           (when-let [x (alg/div algebra beta alpha)]
             [v (alg/neg algebra x)])))))))

(defn smaller
  "The smaller of p and q under `compare-polys`."
  ([p q] (smaller alg/rational p q))
  ([algebra p q] (if (pos? (compare-polys algebra p q)) q p)))

;; ---------------------------------------------------------------------------
;; to and from terms

(defn- factor-term [atom->term [v e]]
  (let [t (atom->term v)]
    (if (= 1 e) t [:expt t e])))

(defn- monomial-term [algebra atom->term m c]
  (let [factors (mapv #(factor-term atom->term %) (sort-by (fn [[v _]] (atom-key v)) m))
        factors (if (= (alg/one algebra) c) factors (into [(alg/write-literal algebra c)] factors))]
    (case (count factors)
      0 (alg/write-literal algebra (alg/one algebra))
      1 (first factors)
      (into [:*] factors))))

(defn ->term
  "The canonical term of p: a sum of products in canonical order,
  written with n-ary :+ and :*. atom->term renders an atom as a term
  (a keyword renders as itself); a coefficient renders as the
  algebra's literal."
  ([p] (->term alg/rational p identity))
  ([p atom->term] (->term alg/rational p atom->term))
  ([algebra p atom->term]
   (let [terms (mapv (fn [[m c]] (monomial-term algebra atom->term m c)) (sorted-terms p))]
     (case (count terms)
       0 (alg/write-literal algebra (alg/zero algebra))
       1 (first terms)
       (into [:+] terms)))))
