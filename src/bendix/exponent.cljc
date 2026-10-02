(ns bendix.exponent
  "Exponent laws: what the powers of an atom are.

  An exponent is not an element of the coefficient algebra. It counts
  factors, so it lives in the monoid its base generates, and every
  monoid with one generator is ℕ with n and n + period identified from
  n = index on. A law is that pair, [index period]: it says
  x^(index + period) = x^index and nothing shorter. No law (nil) is the
  free monoid ℕ, a formal indeterminate.

    idempotent           [1 1]      x² = x: a Boolean atom
    (field-element q)    [1 (q−1)]  x^q = x: an atom ranging over GF(q)
    (root-of-unity m)    [0 m]      x^m = 1

  Index 0 makes the monoid the group ℤ/period: the atom is a unit and
  takes negative exponents. Index 1 keeps x⁰ apart from the cycle
  x, x², …, x^period: over GF(q), x^(q−1) is 1 everywhere but at 0, so
  it is not x⁰. For q = 2^w the monoid is the w-bit words under ones'
  complement addition (end-around carry), whose two zeros are those
  two exponents.

  bendix.poly takes laws as a function from atom to law, nil meaning
  every atom is free; a map from atom to law is such a function, and
  `(constantly idempotent)` says every atom is Boolean.")

(defn law
  "The law x^(index + period) = x^index, checked."
  [index period]
  (when-not (and (integer? index) (<= 0 index) (integer? period) (<= 1 period))
    (throw (ex-info "a law is an index ≥ 0 and a period ≥ 1" {:index index :period period})))
  (when (and (zero? index) (= 1 period))
    (throw (ex-info "index 0 with period 1 says the atom is 1: write 1" {:index index :period period})))
  [index period])

(def idempotent
  "x² = x: a Boolean atom."
  (law 1 1))

(defn field-element
  "x^q = x: an atom ranging over the field of q elements."
  [q]
  (law 1 (dec q)))

(defn root-of-unity
  "x^m = 1: an atom of multiplicative order dividing m, m ≥ 2."
  [m]
  (law 0 m))

(defn unit?
  "Does the law make its atom a unit: is its index 0?"
  [law]
  (and (some? law) (zero? (nth law 0))))

(defn normalize
  "The canonical exponent equal to the integer e under the law: e
  itself below index + period, else its representative on the cycle.
  A negative e needs a unit."
  [law e]
  (if (nil? law)
    (if (neg? e)
      (throw (ex-info "a negative exponent needs a unit" {:exponent e}))
      e)
    (let [[index period] law]
      (cond
        (and (<= 0 e) (< e (+ index period))) e
        (and (neg? e) (pos? index)) (throw (ex-info "a negative exponent needs a unit" {:exponent e :law law}))
        :else (+ index (mod (- e index) period))))))
