(ns bendix.smoke-test
  "bendix.smoke under clojure.test: the facts the node build and the
  browser self-test also check, asserted here on the JVM and Jolt."
  (:require [clojure.test :refer [deftest is]]
            [bendix.smoke :as smoke]))

(deftest every-fact-holds-on-this-runtime
  (doseq [{:keys [name expected actual ok?]} (smoke/checks)]
    (is ok? (str name ": expected " (pr-str expected) ", got " (pr-str actual)))))
