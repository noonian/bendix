(ns bendix.num
  "Exact rational arithmetic on every runtime: the CAS's numbers.

  On the JVM and on Jolt a number is what Clojure has, a long, a
  bignum or a ratio, and the operations are +' *' and / with bignum
  promotion. In ClojureScript an integer is a JavaScript number that
  stays within 2^53, an operation whose result would not throws, and
  a non-integer rational is a Ratio: numerator over positive
  denominator in lowest terms, printed as 1/2, equal and hashed by
  value, ordered by value against numbers and Ratios. A Ratio is
  never zero and never an integer, so zero?, integer? and = against
  the literals 0, 1 and -1 keep their meaning on plain numbers and
  answer false on a Ratio, and only the sites that add, multiply,
  divide or compare a coefficient go through this namespace;
  exponents are plain integers everywhere.

  `read-string` is the EDN reader with 1/2 exact on every runtime;
  ClojureScript's own reader turns it into 0.5, so there the text is
  scanned for ratios first and each becomes a tagged literal."
  (:refer-clojure :exclude [abs numerator denominator ratio? rational? read-string])
  (:require [clojure.string :as str]
            #?(:clj [clojure.edn :as edn]
               :cljs [cljs.reader :as edn])))

;; ---------------------------------------------------------------------------
;; the representation

#?(:cljs
   (declare cmp))

#?(:cljs
   (deftype Ratio [n d]
     Object
     (toString [_] (str n "/" d))
     IEquiv
     (-equiv [_ o] (and (instance? Ratio o) (== n (.-n o)) (== d (.-d o))))
     IHash
     (-hash [_] (hash-combine (hash n) (hash d)))
     IComparable
     (-compare [this o] (cmp this o))
     IPrintWithWriter
     (-pr-writer [_ w _] (-write w (str n "/" d)))))

#?(:cljs
   (defn- safe
     "x, when it is an integer JavaScript can hold exactly."
     [x]
     (if (js/Number.isSafeInteger x)
       x
       (throw (ex-info "exact arithmetic overflowed 2^53" {:value x})))))

#?(:cljs
   (defn- gcd [a b]
     (loop [a (js/Math.abs a), b (js/Math.abs b)]
       (if (zero? b) a (recur b (rem a b))))))

(defn ratio
  "The rational n/d in lowest terms: an integer when d divides n."
  [n d]
  #?(:clj (/ n d)
     :cljs (if (zero? d)
             (throw (ex-info "division by zero" {:numerator n}))
             (let [s (if (neg? d) -1 1)
                   g (gcd n d)
                   n (safe (/ (* s n) g))
                   d (safe (/ (* s d) g))]
               (if (== 1 d) n (Ratio. n d))))))

(defn ratio?
  "Is x a non-integer rational?"
  [x]
  #?(:clj (clojure.core/ratio? x)
     :cljs (instance? Ratio x)))

(defn rational?
  "Is x an exact number: an integer or a ratio?"
  [x]
  (or (integer? x) (ratio? x)))

(defn numerator [x]
  #?(:clj (if (clojure.core/ratio? x) (clojure.core/numerator x) x)
     :cljs (if (ratio? x) (.-n x) x)))

(defn denominator [x]
  #?(:clj (if (clojure.core/ratio? x) (clojure.core/denominator x) 1)
     :cljs (if (ratio? x) (.-d x) 1)))

;; ---------------------------------------------------------------------------
;; arithmetic

(defn add [a b]
  #?(:clj (+' a b)
     :cljs (if (and (number? a) (number? b))
             (safe (+ a b))
             (let [an (numerator a), ad (denominator a), bn (numerator b), bd (denominator b)]
               (ratio (safe (+ (safe (* an bd)) (safe (* bn ad)))) (safe (* ad bd)))))))

(defn mul [a b]
  #?(:clj (*' a b)
     :cljs (if (and (number? a) (number? b))
             (safe (* a b))
             (ratio (safe (* (numerator a) (numerator b))) (safe (* (denominator a) (denominator b)))))))

(defn neg [a]
  #?(:clj (-' a)
     :cljs (if (number? a) (- a) (Ratio. (- (.-n a)) (.-d a)))))

(defn sub [a b] (add a (neg b)))

(defn div
  "a/b, exact; b must not be zero."
  [a b]
  #?(:clj (/ a b)
     :cljs (ratio (safe (* (numerator a) (denominator b))) (safe (* (denominator a) (numerator b))))))

(defn abs [a]
  #?(:clj (clojure.core/abs a)
     :cljs (if (number? a) (js/Math.abs a) (Ratio. (js/Math.abs (.-n a)) (.-d a)))))

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
             (let [x (safe (* (numerator a) (denominator b)))
                   y (safe (* (numerator b) (denominator a)))]
               (compare x y)))))

(defn ->double [a]
  #?(:clj (double a)
     :cljs (if (number? a) a (/ (.-n a) (.-d a)))))

;; ---------------------------------------------------------------------------
;; reading

#?(:cljs
   (defn- parse-ratio [s]
     (let [[_ n d] (re-matches #"([+-]?\d+)/(\d+)" s)]
       (ratio (js/parseInt n 10) (js/parseInt d 10)))))

#?(:cljs
   (defn- tag-ratios
     "text with every ratio token, delimited by whitespace or a
     bracket, as a tagged literal the reader hands to `parse-ratio`."
     [text]
     (str/replace text #"(^|[\s\[\](){}])([+-]?\d+/\d+)(?=$|[\s\[\](){}])" "$1#bendix/r \"$2\"")))

(defn read-string
  "EDN, with ratios exact on every runtime; nil for an empty string."
  [text]
  #?(:clj (edn/read-string text)
     :cljs (edn/read-string {:readers {'bendix/r parse-ratio} :eof nil} (tag-ratios text))))
