(ns bendix.algebra
  "Coefficient algebras for bendix.poly: commutative rings with 1.

  `rational`, the exact rationals of bendix.num, is the default.
  `inv` is partial, nil on a non-unit. `size` and `cmp` support
  bendix.poly's well-founded order: `size` is a natural number with
  finitely many coefficients below any bound, `cmp` a total order."
  (:refer-clojure :exclude [zero? neg])
  (:require [bendix.num :as num]))

(defprotocol Coefficients
  (zero [this] "The additive identity.")
  (one [this] "The multiplicative identity.")
  (zero? [this c] "Is c zero?")
  (add [this a b] "a + b.")
  (neg [this a] "−a.")
  (mul [this a b] "a · b.")
  (from-integer [this n] "The image of the integer n in the algebra.")
  (inv [this a] "a⁻¹, or nil when a is not a unit.")
  (size [this c] "A natural number; finitely many coefficients have a smaller size.")
  (cmp [this a b] "A total order on coefficients, as compare."))

(defn sub [algebra a b] (add algebra a (neg algebra b)))

(defn div
  "a / b, or nil when b is not a unit."
  [algebra a b]
  (when-let [b' (inv algebra b)] (mul algebra a b')))

(defn pow
  "a to a non-negative integer power."
  [algebra a n]
  (loop [acc (one algebra), base a, n n]
    (cond
      (clojure.core/zero? n) acc
      (odd? n) (recur (mul algebra acc base) (mul algebra base base) (quot n 2))
      :else (recur acc (mul algebra base base) (quot n 2)))))

;; ---------------------------------------------------------------------------
;; the rationals

(def rational
  "ℚ over bendix.num."
  (reify Coefficients
    (zero [_] 0)
    (one [_] 1)
    (zero? [_ c] (clojure.core/zero? c))
    (add [_ a b] (num/add a b))
    (neg [_ a] (num/neg a))
    (mul [_ a b] (num/mul a b))
    (from-integer [_ n] n)
    (inv [_ a] (when-not (clojure.core/zero? a) (num/div 1 a)))
    ;; |numerator| + denominator
    (size [_ c] (if (num/ratio? c)
                  (num/add (num/abs (num/numerator c)) (num/denominator c))
                  (num/add (num/abs c) 1)))
    (cmp [_ a b] (num/cmp a b))))
