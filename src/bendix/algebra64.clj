(ns bendix.algebra64
  "GF(2^64), JVM and Jolt only: JavaScript numbers cannot hold 64-bit
  words. Polynomials over GF(2) modulo x^64 + x^4 + x^3 + x + 1,
  catalytic.gf64's field (../../time-and-space/catalytic-buffer), whose
  elements are signed longs read as bit patterns, so the literal -1 is
  the all-ones word, as in three-registers."
  (:require [bendix.algebra :as alg]))

(def ^:private i64-min -9223372036854775808)
(def ^:private i64-max 9223372036854775807)

(defn- mul64
  "Carry-less product reduced modulo x^64 + x^4 + x^3 + x + 1."
  [a b]
  (loop [a a, b b, acc 0]
    (if (zero? b)
      acc
      (let [acc (if (= 1 (bit-and b 1)) (bit-xor acc a) acc)
            hi (neg? a)
            a (bit-shift-left a 1)
            a (if hi (bit-xor a 0x1B) a)]
        (recur a (unsigned-bit-shift-right b 1) acc)))))

(defn- pow64
  "a^e, e read as an unsigned 64-bit exponent."
  [a e]
  (loop [base a, e e, acc 1]
    (if (zero? e)
      acc
      (recur (mul64 base base)
             (unsigned-bit-shift-right e 1)
             (if (= 1 (bit-and e 1)) (mul64 acc base) acc)))))

(defn- bit-length [x]
  (loop [x x, n 0]
    (if (zero? x) n (recur (unsigned-bit-shift-right x 1) (inc n)))))

(defrecord GF2-64 []
  alg/Coefficients
  (zero [_] 0)
  (one [_] 1)
  (zero? [_ c] (zero? c))
  (add [_ a b] (bit-xor a b))
  (neg [_ a] a)
  (mul [_ a b] (mul64 a b))
  (from-integer [_ n] (mod n 2))
  ;; a^(2^64 − 2): the exponent −2 read unsigned
  (inv [_ a] (when-not (zero? a) (pow64 a -2)))
  ;; finitely many words below any bit length
  (size [_ c] (bit-length c))
  ;; unsigned order: flipping the sign bit maps it onto signed order
  (cmp [_ a b] (compare (bit-xor a i64-min) (bit-xor b i64-min)))
  (read-literal [_ x] (when (and (integer? x) (<= i64-min x i64-max)) (long x)))
  (write-literal [_ c] c))

(def gf2-64
  "GF(2^64) over signed-long bit patterns."
  (->GF2-64))
