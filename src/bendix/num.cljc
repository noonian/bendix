(ns bendix.num
  "Exact rational arithmetic on every runtime: the CAS's numbers.

  On the JVM and on Jolt a number is what Clojure has, a long, a
  bignum or a ratio, and the operations are +' *' and / with bignum
  promotion.

  In ClojureScript an integer is a JavaScript number when it is a safe
  integer (|n| ≤ 2^53 − 1), and a non-integer rational is a Ratio:
  numerator over positive denominator in lowest terms, printed as 1/2,
  equal and hashed by value, ordered by value against numbers and
  Ratios. A Ratio's two fields are JavaScript numbers when both are
  safe, and native BigInts otherwise; an integer too large to be safe
  is a Ratio of BigInts with denominator 1. Every operation is first
  tried in numbers, exactly as it always was, and goes to BigInts only
  where a number would not be exact, so a computation that fits in
  2^53 gives the same values, of the same types, as it did before
  BigInts; one that does not, which used to throw, now continues.
  No BigInt leaves this namespace: numerator and denominator return
  numbers or Ratios too.

  A Ratio is never zero, and is an integer only when that integer is
  too large to be safe. So zero?, integer? and = against the literals
  0, 1 and -1 keep their meaning on plain numbers and answer false on
  a Ratio, and only the sites that add, multiply, divide or compare a
  coefficient go through this namespace; exponents are plain integers
  everywhere.

  `read-string` is the EDN reader with 1/2 exact on every runtime;
  ClojureScript's own reader turns it into 0.5, and an integer of 16
  or more digits into an inexact double, so there the text is scanned
  for both first and each becomes a tagged literal."
  (:refer-clojure :exclude [abs numerator denominator ratio? rational? read-string])
  (:require [clojure.string :as str]
            #?(:clj [clojure.edn :as edn]
               :cljs [cljs.reader :as edn])))

;; ---------------------------------------------------------------------------
;; the representation

#?(:cljs
   (declare cmp))

#?(:cljs
   (defn- big?
     "Is x a native BigInt?"
     [x]
     (identical? "bigint" (js* "typeof ~{}" x))))

#?(:cljs
   (def ^:private big-one (js/BigInt 1)))

#?(:cljs
   (deftype Ratio [n d]
     Object
     (toString [_] (if (and (big? d) (== d big-one)) (str n) (str n "/" d)))
     IEquiv
     (-equiv [_ o] (and (instance? Ratio o) (== n (.-n o)) (== d (.-d o))))
     IHash
     (-hash [_] (if (big? n)
                  (hash (str n "/" d))
                  (hash-combine (hash n) (hash d))))
     IComparable
     (-compare [this o] (cmp this o))
     IPrintWithWriter
     (-pr-writer [this w _] (-write w (.toString this)))))

#?(:cljs
   (defn- ok
     "x, when it is an integer JavaScript holds exactly; nil otherwise."
     [x]
     (when (js/Number.isSafeInteger x) x)))

#?(:cljs
   (defn- gcd [a b]
     (loop [a (js/Math.abs a), b (js/Math.abs b)]
       (if (zero? b) a (recur b (rem a b))))))

#?(:cljs
   (defn- big-gcd [a b]
     (let [zero (js/BigInt 0)
           a (if (< a zero) (- a) a)
           b (if (< b zero) (- b) b)]
       (loop [a a, b b]
         (if (== b zero) a (recur b (js* "~{} % ~{}" a b)))))))

#?(:cljs
   (def ^:private max-safe (js/BigInt js/Number.MAX_SAFE_INTEGER)))

#?(:cljs
   (defn- safe-big? [x]
     (and (<= x max-safe) (<= (- max-safe) x))))

#?(:cljs
   (defn- from-big
     "The value n/d, BigInts already in lowest terms with d > 0, in its
     one representation: a number when it is a safe integer, a Ratio of
     numbers when both fields are safe, a Ratio of BigInts otherwise."
     [n d]
     (cond
       (and (== d big-one) (safe-big? n)) (js/Number n)
       (and (safe-big? n) (safe-big? d)) (Ratio. (js/Number n) (js/Number d))
       :else (Ratio. n d))))

#?(:cljs
   (defn- big-ratio
     "n/d in lowest terms from BigInts, d non-zero."
     [n d]
     (let [zero (js/BigInt 0)]
       (when (== d zero)
         (throw (ex-info "division by zero" {:numerator (str n)})))
       (let [[n d] (if (< d zero) [(- n) (- d)] [n d])
             g (big-gcd n d)]
         (if (== n zero)
           0
           (from-big (js* "~{} / ~{}" n g) (js* "~{} / ~{}" d g)))))))

#?(:cljs
   (defn- parts
     "The numerator and denominator of an exact number as BigInts."
     [x]
     (cond (number? x) [(js/BigInt x) big-one]
           (big? x) [x big-one]
           (big? (.-n x)) [(.-n x) (.-d x)]
           :else [(js/BigInt (.-n x)) (js/BigInt (.-d x))])))

#?(:cljs
   (defn- small?
     "Is x a number, or a Ratio of numbers: the path that never needs
     BigInts unless an intermediate passes 2^53?"
     [x]
     (or (number? x) (and (instance? Ratio x) (number? (.-n x))))))

#?(:cljs
   (defn- num-ratio
     "n/d in lowest terms from safe integers, d non-zero: the original
     path."
     [n d]
     (let [s (if (neg? d) -1 1)
           g (gcd n d)
           n (/ (* s n) g)
           d (/ (* s d) g)]
       (if (== 1 d) n (Ratio. n d)))))

(defn ratio
  "The rational n/d in lowest terms: an integer when d divides n."
  [n d]
  #?(:clj (/ n d)
     :cljs (cond
             (and (number? n) (number? d))
             (cond (zero? d) (throw (ex-info "division by zero" {:numerator n}))
                   (and (ok n) (ok d)) (num-ratio n d)
                   :else (throw (ex-info "exact arithmetic needs integers; this one is not exact" {:value n :d d})))
             :else (let [[an ad] (parts n), [bn bd] (parts d)]
                     (big-ratio (* an bd) (* ad bn))))))

(defn ratio?
  "Is x a non-integer rational, or, in ClojureScript, an integer too
  large to be a safe JavaScript number?"
  [x]
  #?(:clj (clojure.core/ratio? x)
     :cljs (instance? Ratio x)))

(defn rational?
  "Is x an exact number: an integer or a ratio?"
  [x]
  (or (integer? x) (ratio? x)))

(defn numerator [x]
  #?(:clj (if (clojure.core/ratio? x) (clojure.core/numerator x) x)
     :cljs (cond (not (ratio? x)) x
                 (big? (.-n x)) (from-big (.-n x) big-one)
                 :else (.-n x))))

(defn denominator [x]
  #?(:clj (if (clojure.core/ratio? x) (clojure.core/denominator x) 1)
     :cljs (cond (not (ratio? x)) 1
                 (big? (.-d x)) (from-big (.-d x) big-one)
                 :else (.-d x))))

;; ---------------------------------------------------------------------------
;; arithmetic

#?(:cljs
   (defn- big-add [a b]
     (let [[an ad] (parts a), [bn bd] (parts b)]
       (big-ratio (+ (* an bd) (* bn ad)) (* ad bd)))))

#?(:cljs
   (defn- big-mul [a b]
     (let [[an ad] (parts a), [bn bd] (parts b)]
       (big-ratio (* an bn) (* ad bd)))))

(defn add [a b]
  #?(:clj (+' a b)
     :cljs (cond
             (and (number? a) (number? b))
             (or (ok (+ a b)) (big-add a b))
             (and (small? a) (small? b))
             (let [an (numerator a), ad (denominator a), bn (numerator b), bd (denominator b)]
               (if-let [^number x (ok (* an bd))]
                 (if-let [^number y (ok (* bn ad))]
                   (if-let [s (ok (+ x y))]
                     (if-let [q (ok (* ad bd))]
                       (num-ratio s q)
                       (big-add a b))
                     (big-add a b))
                   (big-add a b))
                 (big-add a b)))
             :else (big-add a b))))

(defn mul [a b]
  #?(:clj (*' a b)
     :cljs (cond
             (and (number? a) (number? b))
             (or (ok (* a b)) (big-mul a b))
             (and (small? a) (small? b))
             (let [n (ok (* (numerator a) (numerator b)))
                   d (ok (* (denominator a) (denominator b)))]
               (if (and n d) (num-ratio n d) (big-mul a b)))
             :else (big-mul a b))))

(defn neg [a]
  #?(:clj (-' a)
     :cljs (if (number? a) (- a) (Ratio. (- (.-n a)) (.-d a)))))

(defn sub [a b] (add a (neg b)))

(defn div
  "a/b, exact; b must not be zero."
  [a b]
  #?(:clj (/ a b)
     :cljs (if (and (small? a) (small? b))
             (let [^number n (ok (* (numerator a) (denominator b)))
                   ^number d (ok (* (denominator a) (numerator b)))]
               (cond (and n d (zero? d)) (throw (ex-info "division by zero" {:numerator n}))
                     (and n d) (num-ratio n d)
                     :else (let [[an ad] (parts a), [bn bd] (parts b)]
                             (big-ratio (* an bd) (* ad bn)))))
             (let [[an ad] (parts a), [bn bd] (parts b)]
               (big-ratio (* an bd) (* ad bn))))))

(defn abs [a]
  #?(:clj (clojure.core/abs a)
     :cljs (cond (number? a) (js/Math.abs a)
                 (big? (.-n a)) (Ratio. (if (< (.-n a) (js/BigInt 0)) (- (.-n a)) (.-n a)) (.-d a))
                 :else (Ratio. (js/Math.abs (.-n a)) (.-d a)))))

(defn expt
  "a to a non-negative integer power."
  [a n]
  (loop [acc 1, i n]
    (if (zero? i) acc (recur (mul acc a) (dec i)))))

(defn cmp
  "compare, for two exact numbers."
  [a b]
  #?(:clj (compare a b)
     :cljs (if (and (number? a) (number? b))
             (compare a b)
             (let [x (when (and (small? a) (small? b)) (ok (* (numerator a) (denominator b))))
                   y (when (and (small? a) (small? b)) (ok (* (numerator b) (denominator a))))]
               (if (and x y)
                 (compare x y)
                 (let [[an ad] (parts a), [bn bd] (parts b)
                       x (* an bd), y (* bn ad)]
                   (cond (< x y) -1 (> x y) 1 :else 0)))))))

(defn ->double [a]
  #?(:clj (double a)
     :cljs (cond (number? a) a
                 (big? (.-n a))
                 ;; scale both down to keep each a finite double
                 (let [n (.-n a), d (.-d a)
                       digits (fn [x] (count (str (if (< x (js/BigInt 0)) (- x) x))))
                       e (max 0 (- (max (digits n) (digits d)) 300))
                       s (js* "~{} ** ~{}" (js/BigInt 10) (js/BigInt e))]
                   (/ (js/Number (js* "~{} / ~{}" n s)) (js/Number (js* "~{} / ~{}" d s))))
                 :else (/ (.-n a) (.-d a)))))

;; ---------------------------------------------------------------------------
;; reading

#?(:cljs
   (defn- parse-ratio [s]
     (if-let [[_ n d] (re-matches #"([+-]?\d+)/(\d+)" s)]
       (if (and (< (count n) 16) (< (count d) 16))
         (ratio (js/parseInt n 10) (js/parseInt d 10))
         (big-ratio (js/BigInt n) (js/BigInt d)))
       (big-ratio (js/BigInt s) big-one))))

#?(:cljs
   (defn- tag-ratios
     "text with every ratio token, and every integer of 16 or more
     digits, delimited by whitespace or a bracket, as a tagged literal
     the reader hands to `parse-ratio`."
     [text]
     (str/replace text #"(^|[\s\[\](){}])([+-]?(?:\d+/\d+|\d{16,}))(?=$|[\s\[\](){}])" "$1#bendix/r \"$2\"")))

(defn read-string
  "EDN, with ratios and large integers exact on every runtime; nil for
  an empty string."
  [text]
  #?(:clj (edn/read-string text)
     :cljs (edn/read-string {:readers {'bendix/r parse-ratio} :eof nil} (tag-ratios text))))
