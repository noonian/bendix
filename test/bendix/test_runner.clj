(ns bendix.test-runner
  "Entry point for `jolt test` / `jolt -M:test` and `clojure -M:test`."
  (:require [clojure.test :as t]
            [bendix.num-test]
            [bendix.algebra-test]
            [bendix.exponent-test]
            [bendix.poly-test]
            [bendix.ratfun-test]
            [bendix.term-test]
            [bendix.analysis-test]
            [bendix.core-test]
            [bendix.rules-test]
            [bendix.derivative-test]
            [bendix.smoke-test]))

(defn -main [& _]
  ;; every required namespace whose name ends in -test, so one list
  ;; above is the whole suite
  (let [{:keys [fail error]} (apply t/run-tests
                                    (sort-by str (filter #(re-matches #"bendix\..*-test" (str %))
                                                         (map ns-name (all-ns)))))]
    (System/exit (if (pos? (+ fail error)) 1 0))))
