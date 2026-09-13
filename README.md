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

(require '[bendix.rules :as rules])

(simplify [:+ [:+ [:+ :a [:expt [:sin :x] 2]] :b] [:expt [:cos :x] 2]] {:rules rules/trig})
;; => {:result [:+ :a :b 1] ...}                ; the pair is found inside any sum

(simplify [:- 1 [:expt [:cos :x] 2]] {:rules rules/trig})
;; => {:result [:expt [:sin :x] 2] ...}

(simplify [:* [:expt :x :n] [:* :x [:expt :x :m]]] {:rules rules/powers})
;; => {:result [:expt :x [:+ :m :n 1]] ...}      ; one power per base, however the product is arranged

(simplify [:log [:* [:exp :x] [:exp :y]]] {:rules rules/exp-log})
;; => {:result [:+ :x :y] ...}                   ; exponentials collect, log of exp cancels

(simplify [:* [:exp [:+ :x :y]] [:exp [:* -1 :y]]] {:rules rules/exp-log})
;; => {:result [:exp :x] ...}                    ; the arguments cancel in the ring
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
throws naming the first unsound rule. `bendix.rules/trig` holds the
first *normal-form rule*: `sin²u + cos²u = 1` applied as reduction of
a class's polynomial, so it finds the pair however the sum or product
is arranged; `bendix.rules/powers` combines the powers of one base
inside any product the same way, and `bendix.rules/exp-log` the
exponentials; `bendix.rules/normal-form-rule` builds more of them.
`:cost` is a cromulent cost function; the default is AST size, and
what "simplest" means is yours to decide. `:prefer` decides which of
two forms a class keeps inside the analysis, as a measure into
natural numbers so that termination is never in question
(`bendix.analysis/fewest-terms` is the default).

## Running

```
clojure -M:test     jolt -M:test     jolt test      # the suite, either runtime
clojure -M:bench    jolt -M:bench                   # experiments 2, 4, 5, 6 and simplifier timings
```

[IDEA.md](IDEA.md) is the design and status.
