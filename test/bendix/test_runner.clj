(ns bendix.test-runner
  "Entry point for `jolt test` / `jolt -M:test` and `clojure -M:test`."
  (:require [clojure.test :as t]
            [bendix.poly-test]
            [bendix.term-test]
            [bendix.analysis-test]
            [bendix.core-test]
            [bendix.rules-test]
            [bendix.derivative-test]))

(defn -main [& _]
  (let [{:keys [fail error]} (t/run-tests 'bendix.poly-test
                                          'bendix.term-test
                                          'bendix.analysis-test
                                          'bendix.core-test
                                          'bendix.rules-test
                                          'bendix.derivative-test)]
    (System/exit (if (pos? (+ fail error)) 1 0))))
