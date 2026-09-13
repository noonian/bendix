(ns bendix.bench
  "Experiments 2, 4 and 5 of ../design/ac-problem.md and simplifier
  timings, run the same way on both runtimes:

     clojure -M:bench        jolt -M:bench"
  (:require [bendix.core :as bx]
            [bendix.rules :as rules]
            [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.rewrite :as rw]))

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

;; ---------------------------------------------------------------------------
;; experiment 4: the pair buried in a sum of n atoms

(def s2 [:expt [:sin :x] 2])
(def c2 [:expt [:cos :x] 2])

(defn- buried [n]
  (let [next! (lcg 42)
        atoms (mapv #(keyword (str "a" %)) (range n))]
    [atoms (nested-sum (shuffle-with next! (conj atoms s2 c2)))]))

(defn- simplified
  "Saturate t under rules, materialize, extract: `simplify` with the
  e-graph and the iteration count kept."
  [t rules opts]
  (let [{:keys [egraph root stop-reason iterations]} (bx/saturate t (assoc opts :rules rules))
        g (bx/materialize-all egraph)
        {:keys [term]} (ex/extract g root bx/default-cost)]
    {:result term :egraph g :stop stop-reason :iterations iterations}))

(defn buried-trig
  "sin²x + cos²x buried at random positions in a sum of n atoms, under
  the polynomial analysis and the pythagoras normal-form rule
  (approach C + normal-form rules). Expect a0 + … + 1, atoms in the
  renderer's order, at O(n) nodes."
  [n]
  (let [[atoms t] (buried n)
        expected (into [:+] (conj (vec (sort-by str atoms)) 1))
        [ms r] (timed #(simplified t rules/trig {}))
        g (:egraph r)]
    {:fixture (str "buried-trig C+nf n=" n) :n (:iterations r) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)
     :note (if (= expected (:result r)) "reached" (str "NOT reached: " (pr-str (:result r))))}))

(def ac-rules
  "Approach A: binary AC rules plus the identity as a pattern, which
  can only fire once the pair is adjacent."
  [(rw/rule "comm" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "assoc" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])
   (rw/rule "pythagoras-pattern" '[:+ [:expt [:sin ?u] 2] [:expt [:cos ?u] 2]] 1)])

(defn- size [t] (if (vector? t) (reduce + 1 (map size (rest t))) 1))

(defn- mentions-trig? [t]
  (and (vector? t) (or (contains? #{:sin :cos} (nth t 0)) (some mentions-trig? (rest t)))))

(defn buried-trig-ac
  "The same input under approach A on a plain e-graph (no analysis):
  the :simple scheduler, no limits, extraction by AST size. Reached
  when the cheapest term is a binary sum of the n atoms and 1, so
  2n + 1 nodes and no sine or cosine."
  [n]
  (let [[_ t] (buried n)
        [g root] (eg/add (eg/egraph) t)
        [ms res] (timed #(rw/embiggen g ac-rules {:scheduler :simple :node-limit 1000000 :time-limit-ms 600000}))
        g (:egraph res)
        {:keys [term]} (ex/extract g root ex/ast-size)]
    {:fixture (str "buried-trig A n=" n) :n (:iterations res) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)
     :note (if (and (= (+ (* 2 n) 1) (size term)) (not (mentions-trig? term)))
             "reached"
             (str "NOT reached: " (pr-str term)))}))

;; ---------------------------------------------------------------------------
;; experiment 5: a textbook workload

(def workload
  "[label term expected] under C + trig; a set of expected terms
  where two canonical forms tie."
  [["2x+3x" [:+ [:* 2 :x] [:* 3 :x]] [:* 5 :x]]
   ["(x+y)-(y+x)" [:- [:+ :x :y] [:+ :y :x]] 0]
   ["(x+1)(x-1)" [:* [:+ :x 1] [:- :x 1]] [:+ [:expt :x 2] -1]]
   ["(x+y)^2" [:expt [:+ :x :y] 2] [:expt [:+ :x :y] 2]]
   ["sin2+cos2" [:+ s2 c2] 1]
   ["a+sin2+cos2+b" [:+ [:+ [:+ :a s2] c2] :b] [:+ :a :b 1]]
   ["y sin2 + y cos2" [:+ [:* :y s2] [:* :y c2]] :y]
   ["1-sin2" [:- 1 s2] c2]
   ["1-cos2" [:- 1 c2] s2]
   ["(sin2+cos2)^3" [:expt [:+ s2 c2] 3] 1]
   ["sin4-cos4" [:- [:expt [:sin :x] 4] [:expt [:cos :x] 4]] #{[:+ [:* -2 c2] 1] [:+ [:* 2 s2] -1]}]
   ["sin2(x+y)+cos2(y+x)" [:+ [:expt [:sin [:+ :x :y]] 2] [:expt [:cos [:+ :y :x]] 2]] 1]
   ["(2x+3x)sin2+5x cos2" [:+ [:* [:+ [:* 2 :x] [:* 3 :x]] s2] [:* [:* 5 :x] c2]] [:* 5 :x]]])

(defn workload-row [[label t expected]]
  (let [[ms r] (timed #(simplified t rules/trig {}))
        g (:egraph r)
        ok? (if (set? expected) (contains? expected (:result r)) (= expected (:result r)))]
    {:fixture (str "wl " label) :n (:iterations r) :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)
     :note (if ok? "reached" (str "NOT reached: " (pr-str (:result r))))}))

(defn- row [{:keys [fixture n ms nodes classes note]}]
  (println (format "%-28s n=%-5d %8.1f ms   nodes=%-6d classes=%-6d %s" fixture n (double ms) nodes classes (or note ""))))

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
  (println "experiment 4")
  (doseq [n [2 4 6]] (row (buried-trig-ac n)))
  (doseq [n [2 4 6 8 20 50 100]] (row (buried-trig n)))
  (println "experiment 5")
  (doseq [w workload] (row (workload-row w)))
  (System/exit 0))
