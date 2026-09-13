(ns bendix.bench
  "Experiment 2 of ../design/ac-problem.md and simplifier timings, run
  the same way on both runtimes:

     clojure -M:bench        jolt -M:bench"
  (:require [bendix.core :as bx]
            [cromulent.core :as eg]))

(defn- now-ms [] (/ (double (System/nanoTime)) 1e6))

(defn- lcg
  "The same deterministic stream as cromulent's bench."
  [seed]
  (let [state (atom seed)]
    (fn [] (quot (swap! state #(mod (+ (* % 1103515245) 12345) 2147483648)) 65536))))

(defn- shuffle-with
  "Fisher–Yates with next!."
  [next! v]
  (loop [v (vec v), i (dec (count v))]
    (if (<= i 0)
      v
      (let [j (mod (next!) (inc i))]
        (recur (assoc v i (nth v j) j (nth v i)) (dec i))))))

(defn- nested-sum [xs]
  (reduce (fn [acc a] [:+ acc a]) (first xs) (rest xs)))

(defn- timed [f]
  (let [t0 (now-ms), r (f), t1 (now-ms)]
    [(- t1 t0) r]))

(defn arrangements
  "k random orderings of a sum of n atoms, added to one e-graph under
  the polynomial analysis and no rules. With approach C every ordering
  must land in one class, and the graph holds only the nodes that were
  written: n leaves plus k·(n−1) sums at most."
  [n k]
  (let [next! (lcg 42)
        atoms (mapv #(keyword (str "a" %)) (range n))
        sums (repeatedly k #(nested-sum (shuffle-with next! atoms)))
        [ms g] (timed #(eg/rebuild (reduce (fn [g t] (first (eg/add g t))) (bx/egraph) sums)))
        roots (into #{} (map #(eg/find g (second (eg/add g %)))) sums)]
    {:fixture (str "arrangements n=" n " k=" k) :n n :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g) :note (if (= 1 (count roots)) "one class" "NOT merged")}))

(defn simplify-row [label t]
  (let [[ms r] (timed #(bx/simplify t))]
    {:fixture (str "simplify " label) :n (:cost r) :ms ms :nodes 0 :classes 0 :note (pr-str (:result r))}))

(defn- row [{:keys [fixture n ms nodes classes note]}]
  (println (format "%-26s n=%-5d %8.1f ms   nodes=%-6d classes=%-6d %s" fixture n (double ms) nodes classes (or note ""))))

(defn -main [& _]
  (println "bendix bench")
  (row (arrangements 7 1))
  (row (arrangements 7 8))
  (row (arrangements 8 8))
  (row (arrangements 20 10))
  (row (arrangements 50 10))
  (row (arrangements 100 10))
  (row (simplify-row "2x+3x" [:+ [:* 2 :x] [:* 3 :x]]))
  (row (simplify-row "(x+1)(x-1)" [:* [:+ :x 1] [:- :x 1]]))
  (row (simplify-row "(x+y+z)^6" [:expt [:+ [:+ :x :y] :z] 6]))
  (System/exit 0))
