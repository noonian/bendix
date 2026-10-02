(ns bendix.algebra
  "Coefficient algebras for bendix.poly: commutative rings with 1.

  `rational`, the exact rationals of bendix.num, is the default.
  `(gf2 w)` is GF(2^w) for w in 1..32 on every runtime, its elements
  the integers 0..2^w − 1 read as bit patterns; GF(2^64), JVM and Jolt
  only, is bendix.algebra64/gf2-64.

  `inv` is partial, nil on a non-unit. `size` and `cmp` support
  bendix.poly's well-founded order: `size` is a natural number with
  finitely many coefficients below any bound, `cmp` a total order.
  `read-literal` and `write-literal` are the algebra's spelling of its
  elements as term constants: in ℚ a constant is its value, in
  GF(2^w) an integer is a bit pattern, so 3 + 5 is 6 there, and a
  ratio or an integer outside the field is not a literal."
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
  (cmp [this a b] "A total order on coefficients, as compare.")
  (read-literal [this x] "The coefficient the term constant x denotes, or nil when x is not a literal of this algebra.")
  (write-literal [this c] "The term constant that denotes the coefficient c."))

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
    (cmp [_ a b] (num/cmp a b))
    (read-literal [_ x] (when (num/rational? x) x))
    (write-literal [_ c] c)))

;; ---------------------------------------------------------------------------
;; GF(2^w), w ≤ 32
;;
;; Written as catalytic.algebra writes it (../../time-and-space/
;; catalytic-buffer), so the two agree bit for bit on every runtime:
;; elements are canonical unsigned integers, a bitwise result is
;; normalized with `mod` rather than trusted to JavaScript's signed
;; 32-bit coercion, and the doubling step subtracts 2^w before any
;; bitwise operation, so no operand exceeds 2^32.

(defn- pow2 [w] (reduce * 1 (repeat w 2)))

(defn- gf-mul [m tail x c]
  (loop [x x, c c, acc 0]
    (if (clojure.core/zero? c)
      acc
      (let [acc (if (odd? c) (mod (bit-xor acc x) m) acc)
            x2 (* 2 x)
            x2 (if (>= x2 m) (mod (bit-xor (- x2 m) tail) m) x2)]
        (recur x2 (quot c 2) acc)))))

(defn- gf-pow [m tail x e]
  (loop [base x, e e, acc 1]
    (if (clojure.core/zero? e)
      acc
      (recur (gf-mul m tail base base) (quot e 2) (if (odd? e) (gf-mul m tail acc base) acc)))))

(defrecord GF2 [w m tail]
  Coefficients
  (zero [_] 0)
  (one [_] 1)
  (zero? [_ c] (clojure.core/zero? c))
  (add [_ a b] (mod (bit-xor a b) m))
  ;; characteristic 2: every element is its own negative
  (neg [_ a] a)
  (mul [_ a b] (gf-mul m tail a b))
  ;; n·1, which is 1 for odd n and 0 for even: not the bit pattern n
  (from-integer [_ n] (mod n 2))
  ;; a^(2^w − 2)
  (inv [_ a] (when-not (clojure.core/zero? a) (gf-pow m tail a (- m 2))))
  (size [_ c] c)
  (cmp [_ a b] (compare a b))
  (read-literal [_ x] (when (and (integer? x) (<= 0 x) (< x m)) x))
  (write-literal [_ c] c))

(defn- prime-factors
  "Distinct prime factors of n ≥ 1 by trial division; fine to 2^32 − 1."
  [n]
  (loop [n n, p 2, out []]
    (cond (= n 1) out
          (> (* p p) n) (conj out n)
          (clojure.core/zero? (mod n p)) (recur (loop [n n] (if (clojure.core/zero? (mod n p)) (recur (quot n p)) n))
                                                (inc p) (conj out p))
          :else (recur n (inc p) out))))

(defn primitive?
  "Is x^w + tail primitive: does 2 have multiplicative order exactly
  2^w − 1 modulo it? That makes the quotient a field, with 2 a
  generator. For w ≥ 2."
  [w tail]
  (let [m (pow2 w), units (dec m)]
    (and (= 1 (gf-pow m tail 2 units))
         (every? #(not= 1 (gf-pow m tail 2 (quot units %))) (prime-factors units)))))

(def ^:private smallest-primitive-tail
  (memoize (fn [w] (first (filter #(primitive? w %) (range 1 (pow2 w) 2))))))

(defn gf2
  "GF(2^w) for w in 1..32: polynomials over GF(2) modulo x^w + tail,
  an element the integer whose bits are its coefficients. (gf2 1) is
  GF(2). The default tail is the smallest that makes the modulus
  primitive, found by search: 0x1D, 0x2D and 0xAF at w = 8, 16 and 32,
  catalytic.algebra's moduli. (gf2 w tail) takes another; its
  irreducibility is the caller's to witness (`primitive?`)."
  ([w]
   (when-not (and (integer? w) (<= 1 w 32))
     (throw (ex-info "gf2 takes widths 1..32 (bendix.algebra64 has 64)" {:w w})))
   (gf2 w (if (= 1 w) 1 (smallest-primitive-tail w))))
  ([w tail]
   (when-not (and (integer? w) (<= 1 w 32))
     (throw (ex-info "gf2 takes widths 1..32 (bendix.algebra64 has 64)" {:w w})))
   (when-not (and (integer? tail) (odd? tail) (< tail (pow2 w)))
     (throw (ex-info "the tail must be odd and below 2^w" {:w w :tail tail})))
   (->GF2 w (pow2 w) tail)))
