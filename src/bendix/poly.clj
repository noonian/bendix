(ns bendix.poly
  "Sparse multivariate polynomials over the exact rationals.

  A polynomial is a map from monomial to non-zero coefficient; a
  monomial is a map from atom to positive integer exponent. The zero
  polynomial is {}, the constant k is {{} k}, 2x + x² is
  {{:x 1} 2, {:x 2} 1}. Plain maps, so equality is structural and
  hashing is what the e-graph's analysis index needs; a total order
  (`compare-polys`) exists for the cases that need a canonical choice,
  and it is well-founded: below any polynomial there are only finitely
  many others, which is what lets an e-class analysis that keeps the
  smallest form converge.
  Coefficient arithmetic promotes to bignums; nothing here overflows.

  Atoms are opaque here; bendix.term says what they mean (a
  variable, an e-class id, a placeholder). This namespace only orders
  them: keywords first, then integers, then anything else by its
  printed form. `map-atoms` renames them; `substitute` replaces them
  by polynomials.")

;; ---------------------------------------------------------------------------
;; construction and arithmetic

(def zero {})

(defn constant [k] (if (zero? k) zero {{} k}))

(defn variable [a] {{a 1} 1})

(defn constant-value
  "k if p is the constant k, else nil."
  [p]
  (cond
    (empty? p) 0
    (and (= 1 (count p)) (contains? p {})) (get p {})
    :else nil))

(defn constant?
  [p]
  (some? (constant-value p)))

(defn- add-term [p m c]
  (let [c' (+' (get p m 0) c)]
    (if (zero? c') (dissoc p m) (assoc p m c'))))

(defn add [p q]
  (reduce-kv add-term p q))

(defn scale [p k]
  (if (zero? k)
    zero
    (reduce-kv (fn [acc m c] (assoc acc m (*' c k))) {} p)))

(defn neg [p] (scale p -1))

(defn sub [p q] (add p (neg q)))

(defn- mul-monomials [m1 m2] (merge-with + m1 m2))

(defn mul [p q]
  (reduce-kv (fn [acc m1 c1]
               (reduce-kv (fn [acc m2 c2] (add-term acc (mul-monomials m1 m2) (*' c1 c2)))
                          acc
                          q))
             zero
             p))

(defn expt
  "p to a non-negative integer power, by squaring. With a limit, nil
  as soon as any intermediate result has more terms than the limit."
  ([p n] (expt p n nil))
  ([p n limit]
   (let [ok? (fn [q] (or (nil? limit) (<= (count q) limit)))]
     (loop [acc (constant 1), base p, n n]
       (cond
         (not (and (ok? acc) (ok? base))) nil
         (zero? n) acc
         (odd? n) (recur (mul acc base) (if (= 1 n) base (mul base base)) (quot n 2))
         :else (recur acc (mul base base) (quot n 2)))))))

(defn reduce-square
  "p modulo a² − q: every a^e becomes a^(e mod 2)·q^(e div 2), so a
  appears at most linearly. With a limit, nil as soon as an
  intermediate result has more terms than the limit. This is
  reduction by the single-polynomial Gröbner basis {a² − q}; for
  q = 1 − c² it is the Pythagorean identity."
  ([p a q] (reduce-square p a q nil))
  ([p a q limit]
   (let [ok? (fn [r] (or (nil? limit) (<= (count r) limit)))]
     (reduce-kv (fn [acc m c]
                  (when acc
                    (let [e (get m a 0)]
                      (if (< e 2)
                        (add-term acc m c)
                        (let [m' (if (odd? e) (assoc m a 1) (dissoc m a))
                              qk (expt q (quot e 2) limit)
                              acc' (when qk (add acc (scale (mul {m' 1} qk) c)))]
                          (when (and acc' (ok? acc')) acc'))))))
                zero
                p))))

(defn derivative
  "∂p/∂a: the partial derivative of p with respect to the atom a,
  every other atom held constant. Each monomial holding a^e becomes
  the monomial with a^(e−1) and its coefficient times e; a polynomial
  that does not mention a gives zero."
  [p a]
  (reduce-kv (fn [acc m c]
               (let [e (get m a 0)]
                 (if (zero? e)
                   acc
                   (add-term acc (if (= 1 e) (dissoc m a) (assoc m a (dec e))) (*' c e)))))
             zero
             p))

(defn sum [ps] (reduce add zero ps))

(defn product [ps] (reduce mul (constant 1) ps))

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
  [f p]
  (reduce-kv (fn [acc m c]
               (add-term acc (reduce-kv (fn [m' a e] (merge-with + m' {(f a) e})) {} m) c))
             zero
             p))

(defn substitute
  "p with every atom that subst maps replaced by the polynomial it
  maps to; other atoms stay. With a limit, nil as soon as an
  intermediate result has more terms than the limit."
  ([p subst] (substitute p subst nil))
  ([p subst limit]
   (let [ok? (fn [q] (or (nil? limit) (<= (count q) limit)))]
     (reduce-kv (fn [acc m c]
                  (let [q (reduce-kv (fn [q a e]
                                       (let [r (get subst a)
                                             pe (if (nil? r) {{a e} 1} (expt r e limit))
                                             q' (when pe (mul q pe))]
                                         (if (and q' (ok? q')) q' (reduced nil))))
                                     (constant 1)
                                     m)
                        acc' (when q (add acc (scale q c)))]
                    (if (and acc' (ok? acc')) acc' (reduced nil))))
                zero
                p))))

(defn evaluate
  "The value of p under env, a map from atom to number."
  [p env]
  (reduce-kv (fn [acc m c]
               (+' acc (*' c (reduce-kv (fn [v a e]
                                          (let [x (get env a)]
                                            (*' v (reduce *' 1 (repeat e x)))))
                                        1
                                        m))))
             0
             p))

;; ---------------------------------------------------------------------------
;; ordering

(defn- atom-key [a]
  (cond (keyword? a) [0 (str a)]
        (integer? a) [1 a]
        :else [2 (pr-str a)]))

(defn- monomial-key
  "Graded lexicographic: higher total degree first, then the sorted
  atom/exponent list."
  [m]
  [(- (reduce + 0 (vals m)))
   (vec (sort (map (fn [[a e]] [(atom-key a) (- e)]) m)))])

(defn sorted-terms
  "The terms of p as [monomial coefficient] pairs in canonical order."
  [p]
  (sort-by (fn [[m _]] (monomial-key m)) compare p))

(defn- coefficient-size
  "|numerator| + denominator: a natural number, so that only finitely
  many coefficients are smaller than any given one."
  [c]
  (if (ratio? c)
    (+' (abs (numerator c)) (denominator c))
    (+' (abs c) 1)))

(defn- compare-coefficients [a b]
  (let [c (compare (coefficient-size a) (coefficient-size b))]
    (if (not= 0 c) c (compare a b))))

(defn compare-polys
  "A total order: fewer terms first, then lower degree, then smaller
  coefficients by size (|numerator| + denominator), then term by term
  in canonical order comparing monomials, then coefficients by value.
  Every component before the last is a natural number or a choice
  among finitely many, so the order is well-founded: no infinite
  descending chain exists, and a class that keeps the smallest form
  it derives can only change finitely often."
  [p q]
  (let [c (compare (term-count p) (term-count q))]
    (if (not= 0 c)
      c
      (let [c (compare (degree p) (degree q))]
        (if (not= 0 c)
          c
          (let [c (compare (reduce +' 0 (map coefficient-size (vals p)))
                           (reduce +' 0 (map coefficient-size (vals q))))]
            (if (not= 0 c)
              c
              (loop [ps (sorted-terms p), qs (sorted-terms q)]
                (if (empty? ps)
                  0
                  (let [[[mp cp] & ps] ps, [[mq cq] & qs] qs
                        c (compare (monomial-key mp) (monomial-key mq))]
                    (if (not= 0 c)
                      c
                      (let [c (compare-coefficients cp cq)]
                        (if (not= 0 c) c (recur ps qs))))))))))))))

(defn linear-in-one-atom
  "When p is α·v + β for one atom v and α ≠ 0, [v (- β/α)]: the value
  of v that makes p zero. Otherwise nil."
  [p]
  (let [as (atoms p)]
    (when (and (= 1 (count as)) (= 1 (degree p)))
      (let [v (first as)
            alpha (get p {v 1})
            beta (get p {} 0)]
        (when (and alpha (<= (count p) 2))
          [v (- (/ beta alpha))])))))

(defn smaller
  "The smaller of p and q under `compare-polys`."
  [p q]
  (if (pos? (compare-polys p q)) q p))

;; ---------------------------------------------------------------------------
;; to and from terms

(defn- factor-term [atom->term [a e]]
  (let [t (atom->term a)]
    (if (= 1 e) t [:expt t e])))

(defn- monomial-term [atom->term m c]
  (let [factors (mapv #(factor-term atom->term %) (sort-by (fn [[a _]] (atom-key a)) m))
        factors (if (= 1 c) factors (into [c] factors))]
    (case (count factors)
      0 1
      1 (first factors)
      (into [:*] factors))))

(defn ->term
  "The canonical term of p: a sum of products in canonical order,
  written with n-ary :+ and :*. atom->term renders an atom as a term
  (a keyword renders as itself)."
  ([p] (->term p identity))
  ([p atom->term]
   (let [terms (mapv (fn [[m c]] (monomial-term atom->term m c)) (sorted-terms p))]
     (case (count terms)
       0 0
       1 (first terms)
       (into [:+] terms)))))
