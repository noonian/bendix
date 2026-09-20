(ns bendix.bench
  "Experiments 2, 4, 5, 6 and 7 of ../design/ac-problem.md, simplifier
  timings and derivative timings, run the same way on both runtimes:

     clojure -M:bench        jolt -M:bench"
  (:require [bendix.analysis :as an]
            [bendix.core :as bx]
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
  e-graph and the iteration count kept. opts go to the analysis, so
  experiment 6 can set :prefer, which `simplify` does not take."
  [t rules opts]
  (let [[g0 root] (eg/add (bx/egraph opts) t)
        {:keys [egraph stop-reason iterations]} (rw/embiggen g0 rules {})
        g (bx/materialize-all egraph)
        {:keys [term cost]} (ex/extract g root bx/default-cost)]
    {:result term :cost cost :egraph g :stop stop-reason :iterations iterations}))

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

(defn- mentions? [op t]
  (and (vector? t) (or (= op (nth t 0)) (some #(mentions? op %) (rest t)))))

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
   ["(2x+3x)sin2+5x cos2" [:+ [:* [:+ [:* 2 :x] [:* 3 :x]] s2] [:* [:* 5 :x] c2]] [:* 5 :x]]
   ["x^n x^m" [:* [:expt :x :n] [:expt :x :m]] #{[:expt :x [:+ :n :m]] [:expt :x [:+ :m :n]]}]
   ["x^-2 x^3" [:* [:expt :x -2] [:expt :x 3]] :x]
   ["a + x^n x^m + b" [:+ [:+ :a [:* [:expt :x :n] [:expt :x :m]]] :b]
    #{[:+ :a :b [:expt :x [:+ :n :m]]] [:+ :a :b [:expt :x [:+ :m :n]]]}]
   ["(x^n)^2 sin2 + (x^n)^2 cos2" [:+ [:* [:expt [:expt :x :n] 2] s2] [:* [:expt [:expt :x :n] 2] c2]]
    #{[:expt :x [:* 2 :n]] [:expt :x [:* :n 2]]}]
   ["e^x e^y" [:* [:exp :x] [:exp :y]] [:exp [:+ :x :y]]]
   ["e^(x+y) e^-y" [:* [:exp [:+ :x :y]] [:exp [:* -1 :y]]] [:exp :x]]
   ["e^x (e^x)^-1" [:* [:exp :x] [:expt [:exp :x] -1]] 1]
   ["log(e^x e^y)" [:log [:* [:exp :x] [:exp :y]]] [:+ :x :y]]
   ["(e^x+1)(e^x-1)" [:* [:+ [:exp :x] 1] [:- [:exp :x] 1]]
    #{[:+ [:exp [:* 2 :x]] -1] [:+ [:expt [:exp :x] 2] -1]}]
   ["sin2 e^(x+y) + cos2 e^x e^y" [:+ [:* s2 [:exp [:+ :x :y]]] [:* c2 [:* [:exp :x] [:exp :y]]]]
    [:exp [:+ :x :y]]]
   ["sin2 x^(n+m) + cos2 x^n x^m" [:+ [:* s2 [:expt :x [:+ :n :m]]] [:* c2 [:* [:expt :x :n] [:expt :x :m]]]]
    #{[:expt :x [:+ :n :m]] [:expt :x [:+ :m :n]]}]])

(def all-rules (-> [] (into rules/trig) (into rules/powers) (into rules/exp-log)))

(defn- reached? [expected result]
  (if (set? expected) (contains? expected result) (= expected result)))

(defn workload-row
  ([w] (workload-row w {}))
  ([[label t expected] opts]
   (let [[ms r] (timed #(simplified t all-rules opts))
         g (:egraph r)]
     {:fixture (str "wl " label) :n (:iterations r) :ms ms
      :nodes (eg/node-count g) :classes (eg/class-count g)
      :note (if (reached? expected (:result r)) "reached" (str "NOT reached: " (pr-str (:result r))))})))

;; ---------------------------------------------------------------------------
;; experiment 6: the join preference

(defn preference-row
  "The whole workload under one :prefer measure: how many rows reach
  their target, and the iterations, nodes and time summed over the
  rows. Completeness should not depend on the measure; size and time
  may."
  [label prefer]
  (let [rows (map #(workload-row % (if prefer {:prefer prefer} {})) workload)
        reached (count (filter #(= "reached" (:note %)) rows))]
    {:fixture (str "prefer " label) :n (reduce + (map :n rows)) :ms (reduce + (map :ms rows))
     :nodes (reduce + (map :nodes rows)) :classes (reduce + (map :classes rows))
     :note (str reached "/" (count workload) " reached"
                (let [missed (remove #(= "reached" (:note %)) rows)]
                  (if (seq missed) (str "; " (pr-str (map :fixture missed))) "")))}))

;; ---------------------------------------------------------------------------
;; experiment 7: one canonical form of a power, or two

(def combine-only
  "combine-powers as it was before experiment 7: the one-power-per-base
  form alone."
  (rules/normal-form-rule "combine-only" (fn [g _ p] (some-> (rules/combined-form g p) vector))))

(defn- offset-sum
  "Σ aᵢ · y^(n+1) for i < k, nested: k monomials that each have a
  second form. Spelled combined, or split as aᵢ · y · y^n."
  [k split?]
  (nested-sum (map (fn [i]
                     (let [a (keyword (str "a" i))]
                       (if split? [:* a :y [:expt :y :n]] [:* a [:expt :y [:+ :n 1]]])))
                   (range k))))

(def power-workload
  "[label term]: spellings of one value side by side, the workload's
  powers rows, the term the suite's seed 1789597929120 shrinks to, and
  sums where every monomial has a second form."
  [["a y y^n" [:* :a :y [:expt :y :n]]]
   ["a y^(n+1)" [:* :a [:expt :y [:+ :n 1]]]]
   ["(a y) y^n" [:* [:* :a :y] [:expt :y :n]]]
   ["a y^2 y^n" [:* :a [:expt :y 2] [:expt :y :n]]]
   ["a y^(n+2)" [:* :a [:expt :y [:+ :n 2]]]]
   ["x^n x^m" [:* [:expt :x :n] [:expt :x :m]]]
   ["(x^n)^2 sin2 + (x^n)^2 cos2" [:+ [:* [:expt [:expt :x :n] 2] s2] [:* [:expt [:expt :x :n] 2] c2]]]
   ["sin2 x^(n+m) + cos2 x^n x^m" [:+ [:* s2 [:expt :x [:+ :n :m]]] [:* c2 [:* [:expt :x :n] [:expt :x :m]]]]]
   ["the seed's term" [:+ [:* :x :x [:* [:* :x [:* [:* :x :y :x] [:expt :y :n]] [:+ [:* :x :x] [:expt :y -1]]]
                                     [:+ :x [:* [:+ [:sin :x] :x] [:* [:sin :x] :y]]]]] :x]]
   ["sum of 10 a_i y^(n+1)" (offset-sum 10 false)]
   ["sum of 10 a_i y y^n" (offset-sum 10 true)]
   ["sum of 100 a_i y^(n+1)" (offset-sum 100 false)]
   ["sum of 100 a_i y y^n" (offset-sum 100 true)]])

(defn power-forms-rows
  "One row per rule set for a workload entry: the cost reached, and
  whether simplifying the result again reaches the same cost."
  [[label t]]
  (for [[forms power-rules] [["one form " [combine-only]] ["two forms" rules/powers]]]
    (let [rules (-> [] (into rules/trig) (into power-rules) (into rules/exp-log))
          [ms r] (timed #(simplified t rules {}))
          again (simplified (:result r) rules {})
          g (:egraph r)]
      {:fixture (str forms " " label) :n (:iterations r) :ms ms
       :nodes (eg/node-count g) :classes (eg/class-count g)
       :note (str "cost " (:cost r) (if (= (:cost r) (:cost again)) "" (str ", again " (:cost again))))})))

;; ---------------------------------------------------------------------------
;; derivatives: a wide sum and a deep nesting

(defn derivative-row
  "differentiate t with respect to x, with the e-graph and the
  iteration count kept. n is the iteration count; expected is a
  predicate on the result."
  [label t expected]
  (let [[ms {:keys [egraph root stop-reason iterations]}] (timed #(bx/saturate [:D t :x] {:rules rules/derivative}))
        g (bx/materialize-all egraph)
        {:keys [term]} (ex/extract g root bx/no-D)]
    {:fixture (str "d/dx " label) :n iterations :ms ms
     :nodes (eg/node-count g) :classes (eg/class-count g)
     :note (if (and (= :saturated stop-reason) (expected term)) "reached" (str "NOT reached: " (pr-str term)))}))

(defn wide-sum
  "Σ sin(i·x) for i = 1..n: n placeholders in one class in one step,
  then one chain rule each, at O(n) nodes and a fixed iteration count."
  [n]
  (derivative-row (str "sum of " n " sines")
                  (nested-sum (map (fn [i] [:sin [:* i :x]]) (range 1 (inc n))))
                  (fn [t] (and (= :+ (nth t 0)) (= n (dec (count t))) (not (mentions? :D t))))))

(defn deep-nesting
  "sin(sin(... sin x)) n deep: one iteration per level."
  [n]
  (derivative-row (str "sin nested " n " deep")
                  (nth (iterate (fn [t] [:sin t]) :x) n)
                  (fn [t] (and (= :* (nth t 0)) (= n (dec (count t))) (not (mentions? :D t))))))

(defn- row [{:keys [fixture n ms nodes classes note]}]
  (println (format "%-38s n=%-5d %8.1f ms   nodes=%-6d classes=%-6d %s" fixture n (double ms) nodes classes (or note ""))))

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
  (println "experiment 6")
  (row (preference-row "fewest-terms (default)" nil))
  (row (preference-row "lowest-degree" an/lowest-degree))
  (row (preference-row "fewest-atoms" an/fewest-atoms))
  (row (preference-row "most-terms" (an/most-terms 200)))
  (println "experiment 7")
  (doseq [w power-workload, r (power-forms-rows w)] (row r))
  (println "derivatives")
  (doseq [n [10 100]] (row (wide-sum n)))
  (doseq [n [5 20]] (row (deep-nesting n)))
  (System/exit 0))
