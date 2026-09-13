# bendix

A symbolic simplifier for Clojure built on
[cromulent](../cromulent) e-graphs, running on
[Jolt](https://github.com/jolt-lang/jolt) and the JVM from one source.
Named for Knuth–Bendix completion.

Terms are tagged vectors: keywords at the head are operators,
keywords elsewhere are variables, numbers are exact.

```clojure
(require '[bendix.core :refer [simplify]])

(simplify [:+ [:* 2 :x] [:* 3 :x]])
;; => {:result [:* 5 :x] :cost 3 :stop :saturated :assuming #{}}

(simplify [:* [:+ :x 1] [:- :x 1]])
;; => {:result [:+ [:expt :x 2] -1] ...}        ; the expansion is smaller

(simplify [:expt [:+ :x :y] 2])
;; => {:result [:expt [:+ :x :y] 2] ...}        ; the factored form is smaller

(simplify [:+ [:sin :x] [:sin :x]])
;; => {:result [:* 2 [:sin :x]] ...}            ; sin x is an opaque atom
```

The commutative-ring identities are not rewrite rules. A polynomial
normal-form analysis on every e-class merges classes with equal normal
forms, so every arrangement of a sum is one class and no associativity
or commutativity rule ever fires. An equation the ring cannot prove
but the e-graph asserts is used when it determines an atom (a = 2a + 1
makes a = −1), reported as a contradiction when it is one (x = x + 1),
and otherwise kept as an assumption. Everything outside the ring is a
rule: `(simplify t {:rules [...]})` takes cromulent rewrites, and
`:dev? true` checks the normal forms after every rule application and
throws naming the first unsound rule. `:cost` is a cromulent cost
function; the default is AST size, and what "simplest" means is yours
to decide.

## Running

```
clojure -M:test     jolt -M:test     jolt test      # the suite, either runtime
clojure -M:bench    jolt -M:bench                   # experiment 2 and simplifier timings
```

[IDEA.md](IDEA.md) is the design and status.
