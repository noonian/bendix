(ns bendix.exponent-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.algebra :as alg]
            [bendix.analysis :as an]
            [bendix.core :as core]
            [bendix.exponent :as ex]
            [bendix.poly :as p]
            [cromulent.core :as eg]))

(def F2 (alg/gf2 1))
(def F4 (alg/gf2 2))

(def boolean-atoms (constantly ex/idempotent))

;; ---------------------------------------------------------------------------
;; laws

(deftest laws
  (is (= [1 1] ex/idempotent))
  (is (= [1 255] (ex/field-element 256)))
  (is (= [0 3] (ex/root-of-unity 3)))
  (is (ex/unit? (ex/root-of-unity 3)))
  (is (not (ex/unit? ex/idempotent)))
  (is (not (ex/unit? nil)) "a free atom is not a unit")
  (is (thrown? clojure.lang.ExceptionInfo (ex/law 0 1)) "x = 1 is not an atom")
  (is (thrown? clojure.lang.ExceptionInfo (ex/law -1 2)))
  (is (thrown? clojure.lang.ExceptionInfo (ex/law 1 0))))

(deftest canonical-exponents
  (is (= [0 1 1 1] (map #(ex/normalize ex/idempotent %) [0 1 2 7])))
  (is (= [0 1 2 3 1 2 3 1] (map #(ex/normalize (ex/field-element 4) %) (range 8)))
      "x⁴ = x: the cycle is 1 2 3, and 0 is outside it")
  (is (= [0 1 2 0 1] (map #(ex/normalize (ex/root-of-unity 3) %) (range 5))))
  (is (= [2 1 0] (map #(ex/normalize (ex/root-of-unity 3) %) [-1 -2 -3])) "a unit takes negative exponents")
  (is (= [0 1 2 3 4 3 4 3] (map #(ex/normalize (ex/law 3 2) %) (range 8))) "x⁵ = x³")
  (is (= 5 (ex/normalize nil 5)) "no law: ℕ")
  (is (thrown? clojure.lang.ExceptionInfo (ex/normalize ex/idempotent -1)))
  (is (thrown? clojure.lang.ExceptionInfo (ex/normalize nil -1))))

(defn- end-around-carry
  "Ones' complement addition of two w-bit words: the carry out of the
  top bit comes back in at the bottom."
  [w a b]
  (let [q (bit-shift-left 1 w), s (+ a b)]
    (if (>= s q) (inc (- s q)) s)))

(deftest the-exponents-of-a-field-atom-are-ones-complement-words
  (doseq [w [1 2 3 4]]
    (let [F (alg/gf2 w), q (bit-shift-left 1 w), law (ex/field-element q)]
      (is (= (range q) (map #(ex/normalize law %) (range q)))
          "every w-bit word is canonical, the two zeros 0 and 2^w − 1 included")
      (is (every? (fn [[a b]] (= (end-around-carry w a b) (ex/normalize law (+ a b))))
                  (for [a (range q), b (range q)] [a b])))
      (is (every? (fn [[x a b]] (= (alg/mul F (alg/pow F x a) (alg/pow F x b))
                                   (alg/pow F x (ex/normalize law (+ a b)))))
                  (for [x (range q), a (range q), b (range q)] [x a b]))
          "and that addition is multiplication of powers, at 0 too")
      (is (= (cons 0 (repeat (dec q) 1)) (map #(alg/pow F % (dec q)) (range q)))
          "the other zero: x^(q−1) is 1 everywhere but at 0, where x⁰ is 1 as well"))))

;; ---------------------------------------------------------------------------
;; polynomials under laws

(deftest polynomials-under-laws
  (let [x (p/variable F2 :x), y (p/variable F2 :y)]
    (is (= x (p/mul F2 boolean-atoms x x)))
    (is (= x (p/expt F2 boolean-atoms x 1000 nil)))
    (is (= (p/add F2 x y) (p/expt F2 boolean-atoms (p/add F2 x y) 2 nil)) "(x + y)² = x + y in GF(2)")
    (is (= x (p/under F2 boolean-atoms {{:x 3} 1, {:x 2} 1, {:x 1} 1})) "x³ + x² + x = x")
    (is (= x (p/map-atoms F2 boolean-atoms {:x :x, :y :x} (p/mul F2 x y))) "x·y with y renamed to x")
    (is (= x (p/substitute F2 boolean-atoms (p/mul F2 x y) {:y x} nil))))
  (let [x (p/variable :x), y (p/variable :y)]
    (is (= {{:x 1, :y 1} 2, {:x 1} 1, {:y 1} 1} (p/expt alg/rational boolean-atoms (p/add x y) 2 nil))
        "over ℚ the cross term stays: the multilinear form of (x + y)²")
    (is (= p/zero (p/mul alg/rational boolean-atoms x (p/sub (p/constant 1) x))) "x(1 − x) = 0")
    (is (= {{:x 1, :y 2} 1} (p/mul alg/rational {:x ex/idempotent} (p/mul x y) (p/mul x y))) "a law for x alone")
    (is (= {{:x 2} 1} (p/mul x x)) "no laws: the free ring, as before")))

(deftest units
  (let [laws {:w (ex/root-of-unity 3)}
        w (p/variable F4 :w)]
    (is (= w (p/inverse F4 laws {{:w 2} 1})) "(w²)⁻¹ = w")
    (is (= (p/constant F4 1) (p/mul F4 laws {{:w 2} 1} w)) "w³ = 1")
    (is (= {{:w 2} 3} (p/inverse F4 laws {{:w 1} 2})) "2⁻¹ = 3 in GF(4)")
    (is (nil? (p/inverse F4 laws (p/add F4 w (p/constant F4 1)))) "a sum is not a unit the laws can see")
    (is (nil? (p/inverse F4 laws (p/variable F4 :x))) "x has no law")
    (is (nil? (p/inverse F4 {:x (ex/field-element 4)} (p/variable F4 :x))) "a field atom may be 0"))
  (is (= {{} 1/2} (p/inverse alg/rational (p/constant 2))))
  (is (nil? (p/inverse alg/rational (p/variable :x))))
  (is (nil? (p/inverse alg/rational p/zero))))

(defn- points [q]
  (for [x (range q), y (range q)] {:x x :y y}))

(defn- table [F q poly]
  (mapv #(p/evaluate F poly %) (points q)))

(deftest the-normal-form-decides-equality-of-functions
  ;; a polynomial in n atoms with every exponent below q is one
  ;; function GF(q)ⁿ → GF(q), and there are as many of the one as of
  ;; the other
  (doseq [w [1 2 3]]
    (let [F (alg/gf2 w), q (bit-shift-left 1 w), laws (constantly (ex/field-element q))
          monomial (gen/map (gen/elements [:x :y]) (gen/choose 1 (* 2 q)) {:max-elements 2})
          free (gen/fmap (fn [terms] (p/sum F (map (fn [[m c]] {m c}) terms)))
                         (gen/vector (gen/tuple monomial (gen/choose 1 (dec q))) 0 4))
          res (tc/quick-check
               200
               (prop/for-all [a free, b free, k (gen/choose 1 3)]
                 (let [a' (p/under F laws a), b' (p/under F laws b)
                       ;; the same function, every exponent a period or more further round the cycle
                       further (into {} (map (fn [[m c]] [(into {} (map (fn [[v e]] [v (+ e (* k (dec q)))])) m) c])) a')]
                   (and (every? (fn [m] (every? #(<= 1 % (dec q)) (vals m))) (keys a'))
                        (= (table F q a) (table F q a'))
                        (= (table F q (p/mul F a b)) (table F q (p/mul F laws a' b')))
                        (= a' (p/under F laws further))
                        (= (= a' b') (= (table F q a) (table F q b)))))))]
      (is (:pass? res) (pr-str w res)))))

;; ---------------------------------------------------------------------------
;; the simplifier under laws

(defn- simp [opts t] (:result (core/simplify t (assoc opts :dev? true))))

(defn- form
  "The normal form of t's class, as a term."
  [opts t]
  (let [{g :egraph, root :root} (core/saturate t opts)]
    (p/->term (an/algebra-of g) (an/canonical g (eg/data g root :poly)) identity)))

(def circuit {:algebra F2 :exponent-laws boolean-atoms})

(deftest boolean-atoms-give-the-algebraic-normal-form
  (is (= :x (simp circuit [:* :x :x])))
  (is (= :x (simp circuit [:expt :x 5])))
  (is (= 0 (simp circuit [:* :x [:+ :x 1]])) "x and not x")
  (is (= [:+ [:* :x :y] :x :y] (simp circuit [:+ [:* [:+ :x 1] [:+ :y 1]] 1])) "x or y, by De Morgan")
  (is (= 0 (simp circuit [:+ [:+ [:* :x :y] 1]
                          [:+ [:+ :x 1] [:+ :y 1] [:* [:+ :x 1] [:+ :y 1]]]]))
      "not (x and y) is (not x) or (not y): equal circuits sum to 0")
  (is (= [:f :x] (simp circuit [:* [:f :x] [:f :x]])) "(constantly law) gives every value the law")
  (is (= [:expt [:f :x] 2] (simp {:algebra F2 :exponent-laws {:x ex/idempotent}} [:* [:f :x] [:f :x]]))
      "a map from variable to law leaves an opaque class free")
  (testing "over ℚ"
    (is (= 0 (simp {:exponent-laws boolean-atoms} [:* :x [:- 1 :x]])))
    (is (= [:+ [:* 2 :x :y] :x :y] (form {:exponent-laws boolean-atoms} [:expt [:+ :x :y] 2])))
    (is (= [:* :x [:expt :y 2]] (simp {:exponent-laws {:x ex/idempotent}} [:* :x :y :x :y])))))

(deftest atoms-ranging-over-a-field
  (let [opts {:algebra F4 :exponent-laws (constantly (ex/field-element 4))}]
    (is (= :x (simp opts [:expt :x 4])))
    (is (= :x (simp opts [:* [:expt :x 3] :x])))
    (is (= [:expt :x 3] (simp opts [:expt :x 3])) "x³ is 1 except at 0: it is not x⁰")
    (is (= [:expt :x 3] (form opts [:expt :x 6])))
    (is (= 0 (simp opts [:* :x [:+ [:expt :x 3] 1]])) "x³ + 1 is the indicator of x = 0")
    (is (= [:expt :x -1] (simp opts [:expt :x -1])) "no inverse: x may be 0")))

(deftest roots-of-unity
  (let [opts {:algebra F4 :exponent-laws {:w (ex/root-of-unity 3)}}]
    (is (= [:expt :w 2] (form opts [:expt :w -1])))
    (is (= :w (simp opts [:expt :w -2])))
    (is (= 1 (simp opts [:* [:expt :w 2] :w])))
    (is (= [:* [:expt :w 2] :x] (form opts [:/ :x :w])) "division by a unit")
    (is (= 1 (simp opts [:+ 1 [:expt :w 3] [:expt :w 6]])) "Σⱼ w^(3j) = 3 = 1: the term a degree filter keeps")
    (is (= [:/ :x :y] (simp opts [:/ :x :y])) "y has no law")))

(deftest differentiation-refuses-an-atom-with-a-law
  (is (thrown? clojure.lang.ExceptionInfo (core/differentiate [:* :x :x] :x {:exponent-laws boolean-atoms})))
  (is (= :x (:result (core/differentiate [:* :x :x :y] :y {:exponent-laws {:x ex/idempotent}})))))

(defn- value [t env]
  (cond (integer? t) t
        (keyword? t) (get env t)
        :else (let [[op & args] t
                    vs (map #(value % env) args)]
                (case op
                  :+ (reduce #(alg/add F2 %1 %2) vs)
                  :* (reduce #(alg/mul F2 %1 %2) vs)))))

(defn- truth-table [t]
  (for [x [0 1], y [0 1], z [0 1]] (value t {:x x :y y :z z})))

(def circuit-gen
  (gen/recursive-gen
   (fn [inner] (gen/one-of [(gen/fmap #(into [:+] %) (gen/vector inner 2 3))
                            (gen/fmap #(into [:*] %) (gen/vector inner 2 3))]))
   (gen/elements [:x :y :z 0 1])))

(deftest the-simplifier-decides-circuit-equality
  (let [res (tc/quick-check
             100
             (prop/for-all [a circuit-gen, b circuit-gen]
               (let [ra (simp circuit a)]
                 (and (= (truth-table a) (truth-table ra))
                      (= 0 (simp circuit [:+ a ra]))
                      (= (= (truth-table a) (truth-table b))
                         (= 0 (simp circuit [:+ a b])))))))]
    (is (:pass? res) (pr-str res))))
