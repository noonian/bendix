(ns bendix.algebra-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [bendix.algebra :as alg]
            [bendix.algebra64 :as alg64]
            [bendix.core :as core]
            [bendix.poly :as p]))

(defn- passes? [property] (:pass? (tc/quick-check 200 property)))

(defn- field-laws
  "Commutative-ring laws, characteristic 2, and an inverse for every
  non-zero element, over elements drawn by g."
  [F g]
  (prop/for-all [a g, b g, c g]
    (and (= (alg/add F a b) (alg/add F b a))
         (= (alg/mul F a b) (alg/mul F b a))
         (= (alg/mul F a (alg/mul F b c)) (alg/mul F (alg/mul F a b) c))
         (= (alg/mul F a (alg/add F b c)) (alg/add F (alg/mul F a b) (alg/mul F a c)))
         (= (alg/zero F) (alg/add F a a))
         (= a (alg/neg F a))
         (= a (alg/mul F a (alg/one F)))
         (if (alg/zero? F a)
           (nil? (alg/inv F a))
           (= (alg/one F) (alg/mul F a (alg/inv F a)))))))

(defn- elements [w] (gen/large-integer* {:min 0 :max (dec (bit-shift-left 1 w))}))

(deftest gf2-is-a-field
  (doseq [w [1 2 3 8 16 32]]
    (testing (str "GF(2^" w ")")
      (is (passes? (field-laws (alg/gf2 w) (elements w))))))
  (testing "GF(2^64)"
    (is (passes? (field-laws alg64/gf2-64 gen/large-integer)))))

(deftest moduli
  (is (= [0x1D 0x2D 0xAF] (map #(:tail (alg/gf2 %)) [8 16 32]))
      "the smallest primitive tails are catalytic.algebra's moduli")
  (is (every? #(alg/primitive? % (:tail (alg/gf2 %))) [2 3 4 5 8]))
  (is (= 1 (:tail (alg/gf2 1))) "GF(2) is GF(2)[x]/(x + 1)")
  (is (= 0x1D (alg/pow (alg/gf2 8) 2 8)) "x^8 = x^4 + x^3 + x^2 + 1")
  (is (= 0x1B (alg/pow alg64/gf2-64 2 64)) "x^64 = x^4 + x^3 + x + 1")
  (is (thrown? clojure.lang.ExceptionInfo (alg/gf2 33)))
  (is (thrown? clojure.lang.ExceptionInfo (alg/gf2 8 4)) "an even tail is reducible"))

(deftest literals
  (let [F (alg/gf2 8)]
    (is (= 255 (alg/read-literal F 255)))
    (is (nil? (alg/read-literal F 256)) "outside the field")
    (is (nil? (alg/read-literal F -1)))
    (is (nil? (alg/read-literal F 1/2)) "ratios are not literals")
    (is (= 1 (alg/from-integer F 3)) "3·1 is 1, not the bit pattern 3")
    (is (= 0 (alg/from-integer F 2))))
  (is (= -1 (alg/read-literal alg64/gf2-64 -1)) "the all-ones word")
  (is (nil? (alg/read-literal alg64/gf2-64 18446744073709551615N)) "words are signed longs")
  (is (neg? (alg/cmp alg64/gf2-64 1 -1)) "ordered as unsigned words")
  (is (= 1/2 (alg/read-literal alg/rational 1/2))))

(def F2 (alg/gf2 1))
(def F8 (alg/gf2 8))

(deftest polynomials-in-characteristic-2
  (let [x (p/variable F2 :x), one (p/constant F2 1)]
    (is (= p/zero (p/add F2 x x)) "x + x = 0")
    (is (= {{:x 2} 1, {} 1} (p/expt F2 (p/add F2 x one) 2 nil)) "(x + 1)² = x² + 1: the cross term is 2x")
    (is (= p/zero (p/derivative F2 (p/mul F2 x x) :x)) "d/dx x² = 2x = 0")
    (is (= [:+ [:expt :x 2] 1] (p/->term F2 (p/expt F2 (p/add F2 x one) 2 nil) identity))))
  (let [x (p/variable F8 :x)]
    (is (= [:* 6 :x] (p/->term F8 (p/scale F8 x 6) identity)))
    (is (= 6 (p/constant-value F8 (p/add F8 (p/constant F8 3) (p/constant F8 5)))) "3 + 5 = 3 xor 5")))

(defn- simp [algebra t] (:result (core/simplify t {:algebra algebra})))

(deftest simplify-over-a-field
  (is (= 0 (simp F2 [:+ :x :x])))
  (is (= :x (simp F2 [:+ :x :x :x])))
  (is (= :x (simp F2 [:- :x])) "−x = x")
  (is (= [:+ [:expt :x 2] 1] (simp F2 [:* [:+ :x 1] [:+ :x 1]])))
  (is (= 6 (simp F8 [:+ 3 5])))
  (is (= [:* 2 :x] (simp F8 [:* [:/ 1 3] [:* 6 :x]])) "6/3 = 6·3⁻¹ = 2: carry-less, 3·2 = 6")
  (testing "exponents are integers, not elements"
    (is (= [:expt :x 2] (simp F2 [:expt :x 2])) "2 is no element of GF(2), and still an exponent")
    (is (= 1 (simp F2 [:+ [:expt [:+ :x 1] 2] [:expt :x 2]])) "(x + 1)² + x² = 1")
    (is (= [:expt :x 4] (simp F8 [:* [:expt :x 2] [:expt :x 2]])))
    (is (= [:expt :x 2] (simp F2 [:+ [:expt :x [:+ 1 1]] 0])) "1 + 1 is 2 as an exponent, though 0 as an element")
    (is (= 0 (simp F8 [:+ [:expt :x [:+ 3 1]] [:expt :x 4]])) "3 + 1 is 4, not 3 xor 1")
    (is (= [:expt :x 6] (simp F8 [:expt :x [:* [:- 5 2] [:/ 4 2]]])))
    (is (= 1 (simp F8 [:* [:expt 3 [:- 1 2]] 3])) "3^(1−2) = 3⁻¹")
    (testing "symbolic and non-integer exponents are refused until they have a domain of their own"
      (is (thrown? clojure.lang.ExceptionInfo (simp F2 [:+ [:expt :x [:+ :n 1 1 1]] [:expt :x [:+ :n 1]]]))
          "would equate x^(n+3) with x^(n+1)")
      (is (thrown? clojure.lang.ExceptionInfo (simp F8 [:expt :x :n])))
      (is (thrown? clojure.lang.ExceptionInfo (simp F8 [:expt :x [:/ 1 2]])))
      (is (= [:+ [:expt :x [:+ :n 3]] [:expt :x [:+ :n 1]]]
             (simp alg/rational [:+ [:expt :x [:+ :n 1 1 1]] [:expt :x [:+ :n 1]]]))
          "over ℚ an exponent is a value like any other")))
  (testing "a constant that is not a literal of the field is opaque"
    (is (= [:+ :x 300] (simp F8 [:+ :x 300])))
    (is (= [:+ :x 1/2] (simp F8 [:+ :x 1/2]))))
  (is (= -27 (simp alg64/gf2-64 [:* -1 2]))
      "the all-ones word times x: shifted left, x^64 reduced to 0x1B"))
