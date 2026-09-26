(ns bendix.num-test
  (:require [clojure.test :refer [deftest is]]
            [bendix.num :as num]))

(deftest exact-arithmetic
  (is (= 5/6 (num/add 1/2 1/3)))
  (is (= 1/6 (num/sub 1/2 1/3)))
  (is (= 1/6 (num/mul 1/2 1/3)))
  (is (= 3/2 (num/div 1/2 1/3)))
  (is (= 1/2 (num/div 2 4)))
  (is (= 2 (num/div 4 2)) "an integer when the division is exact")
  (is (= -1/2 (num/neg 1/2)))
  (is (= 1/2 (num/abs -1/2)))
  (is (= 1/8 (num/expt 1/2 3)))
  (is (= 1 (num/expt 7 0)))
  (is (= 1/2 (num/ratio 3 6)))
  (is (= 4611686018427387904 (num/mul 2147483648 2147483648)) "promotes past a long's range on the JVM"))

(deftest predicates-and-parts
  (is (num/ratio? 1/2))
  (is (not (num/ratio? 2)))
  (is (num/rational? 1/2))
  (is (num/rational? -3))
  (is (not (num/rational? 0.5)) "floats are not exact")
  (is (not (num/rational? :x)))
  (is (= [1 2] [(num/numerator 1/2) (num/denominator 1/2)]))
  (is (= [7 1] [(num/numerator 7) (num/denominator 7)])))

(deftest ordering
  (is (neg? (num/cmp 1/3 1/2)))
  (is (pos? (num/cmp 1 1/2)))
  (is (zero? (num/cmp 2/4 1/2)))
  (is (= 0.5 (num/->double 1/2))))

(deftest reading
  (is (= [:* 1/2 :x] (num/read-string "[:* 1/2 :x]")))
  (is (= [:+ [:expt :x -1/2] 3] (num/read-string "[:+ [:expt :x -1/2] 3]")))
  (is (= "[:* 1/2 :x]" (pr-str (num/read-string "[:* 1/2 :x]"))) "prints as it was written")
  (is (nil? (num/read-string ""))))
