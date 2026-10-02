# bendix — the CAS layer — design

Named for Knuth–Bendix completion (1970), where turning equations
into rewrite systems began; e-graphs are its descendant.

bendix is a Computer Algebra System. A CAS manipulates mathematical expressions
symbolically. This one starts as a **simplifier** on top of the
e-graph library, and everything else a CAS does (differentiation,
expansion, factoring, solving) is added as rule sets, analyses, and
cost functions on the same engine. It runs on Jolt and the JVM.

The thesis: *simplification is equality saturation plus taste*. The
e-graph finds every equal form the rules and analyses can reach; a
cost function says which one the user wanted.

## 1. Audience and term format

**Audience: Clojure programmers**, not scientists. That decides the
defaults: terms are plain data that print as they are written, the
API is REPL-first and data-in/data-out, rules and cost functions are
values, errors are `ex-info` with data, and nothing requires a reader
macro or a notebook. We are not bound by scmutils, and since Emmy
already serves the scmutils audience with the scmutils syntax, we
deliberately do not mirror it.

**Term format: tagged vectors** (decided 2026-09-13), the workspace
shape (../design/overview.md). Operators are keywords, variables are keywords in
leaf position, constants are exact numbers. Position disambiguates: a
keyword at the head of a vector is an operator, anywhere else it is a
variable. Named constants are nullary operators (`[:pi]`, `[:e]`) so
they cannot be mistaken for variables.

```clojure
[:+ [:* 2 :x] [:expt :y 2]]      ;; 2x + y²
[:D [:sin [:* 2 :x]] :x]          ;; d/dx sin(2x)
```

Floating-point input is rejected or rationalized explicitly; the
engine is exact. Pattern variables are `?x` symbols and appear only in
rules.

Other syntaxes are compilers to this one and come later, if at all: an
s-expression reader, an infix string parser (`"2*x + y"`),
pretty-printers to infix or TeX. None is on the critical path, and the
canonical form is what every API takes and returns. A term protocol in
the core means even the canonical form could change without touching
the engine.

## 2. Pipeline

```
term ──add──▶ e-graph ──saturate(rules, analyses, limits)──▶ e-graph ──extract(cost)──▶ term
```

`(simplify term)` and `(simplify term {:rules ... :cost ... :assume ...})`.
The result carries what the engine can say about it:

```clojure
{:result   [:* 2 [:cos [:* 2 :x]]]
 :cost     5
 :assuming #{}            ;; side conditions the result depends on (section 5)
 :stop     :saturated}    ;; or which limit was hit
```

`(differentiate t x)` is `simplify` of `[:D t x]` under the
derivative rules with a cost that refuses `:D` (section 3,
"Differentiation"); its result adds `:undifferentiated`, what no
rule could remove.

## 3. What is a rule and what is not

**Not rules:** the commutative-ring identities (AC of `+` and `*`,
distributivity, `x − x = 0`, `0·x = 0`, collecting like terms,
constant arithmetic). These are handled by the polynomial normal-form
analysis (../design/ac-problem.md, approach C) and are complete there. Writing
them as rules would reintroduce the 3ⁿ blowup.

**Rules**, in layered sets a caller can compose:

- `powers`: `[:expt ?x 0] = 1`, `[:expt [:expt ?x ?m] ?n] = [:expt ?x [:* ?m ?n]]`
  (integer exponents only, unconditionally), `[:* [:expt ?x ?m] [:expt ?x ?n]] = [:expt ?x [:+ ?m ?n]]`.
  Built as one normal-form rule over monomials (`combine-powers`,
  designed below under "Normal-form rules"): the analysis already
  folds non-negative integer exponents, so the rule handles the
  powers it holds as atoms, as one power per base.
- `exp-log`: `[:* [:exp ?a] [:exp ?b]] = [:exp [:+ ?a ?b]]` and
  `[:expt [:exp ?a] ?n] = [:exp [:* ?n ?a]]`, built as one normal-form
  rule over monomials (`combine-exp`, section 10 item 1, the mirror
  image of `combine-powers`); `[:log [:exp ?x]] = ?x` as a pattern
  rule. `[:exp [:log ?x]] = ?x` (needs `?x > 0`) and
  `[:log [:* ?a ?b]] = [:+ [:log ?a] [:log ?b]]` are conditional and
  wait for the sign lattice.
- `trig`: Pythagorean, double angle, sum/difference, parity.
- `abs-sign`: `[:abs [:* ?a ?b]] = [:* [:abs ?a] [:abs ?b]]`, `[:abs ?x] = ?x` when `?x ≥ 0`.
- `derivative`: the ring part of a derivative is computed from the
  class's normal form by one normal-form rule (linearity, the product
  rule and the power rule for folded exponents are polynomial
  calculus, not rules); the chain rule is one pattern rule per
  operator (`[:D [:sin ?u] ?x] = [:* [:cos ?u] [:D ?u ?x]]`); and
  `[:D ?u ?x] = 0` when `?u` cannot depend on `?x`. Designed below
  ("Differentiation").

Every rule is a value with a name; rule sets are vectors of rules;
tests run each set alone and in combination.

**The sub-sum problem.** If ring identities are not rules, the e-graph
holds `a + sin²x + cos²x + b` only as the binary tree the user wrote,
and the pattern `[:+ [:expt [:sin ?x] 2] [:expt [:cos ?x] 2]]` finds
nothing: there is no node for the inner pair. Three answers, to be
measured (../design/ac-problem.md experiments 4 and 5):

1. AC rules with backoff after all, only to *materialize* orderings
   for matching, with the polynomial analysis merging what they
   produce. The blowup returns, throttled.
2. **Normal-form rules.** A rule whose left-hand side is a function
   over the class's polynomial rather than a pattern: "a class whose
   normal form contains `k·sin(u)² + k·cos(u)²` for some `u`" binds
   `?u` and `?k`, and the right-hand side is the polynomial with that
   part replaced by `k`. Matching modulo AC becomes a walk over a
   sorted monomial map, which is cheap and complete for the ring
   fragment. This needs the core to accept a searcher function in
   place of a pattern (cromulent IDEA.md section 7); the runner does
   not otherwise change.
3. Bag-valued nodes (../design/ac-problem.md approach B), the heavier core change,
   if 2 turns out to need too many special cases.

Answer 2 is the thesis of approach C taken seriously and is the first
one to try.

### Normal-form rules

A normal-form rule rewrites a class's *polynomial*, not a node. Its
left-hand side is a searcher (cromulent IDEA.md section 7) that
visits every root whose `:poly` data is a polynomial, and every
opaque class as its unit polynomial `{{id 1} 1}`, and asks a
*polynomial rewrite* `(fn [g id p] [p' ...])` for the other forms the
class is worth. Its right-hand side is each `p'` rendered by
`bendix.poly/->term` as a **pattern** over the atoms: a variable
renders as itself, an opaque class id as the pattern variable `?<id>`
bound to that id, and a **placeholder**, a term over class ids for a
node the graph may not hold yet (the cosine of an argument that so
far has only a sine, `[:cos u]`), as that term with each class id
replaced by its variable, `[:cos ?u<id>]`. The match carries that pattern as
its own `:rhs`, a cromulent extension made for this (a match may
supply the right-hand side), so one rule says a different thing about
every class. The runner instantiates and unions as for any rule; the
analysis joins the new node's form into the class, keeps the
preferred one (section 4), and the index merges any other class that
already had it.

`(normal-form-rule name f)` is the constructor (`bendix.rules`). A
rule costs one pass over the roots per iteration and polynomial
arithmetic per class; no pattern is matched against any node, and
because `->term` writes normal forms n-ary the right-hand side is one
small tree.

**`pythagoras`**, the first one. For every argument class `u` such
that `[:sin u]` or `[:cos u]` is an atom of `p` (a missing partner
becomes a placeholder), the identity `sin²u + cos²u = 1` is the ideal
generated by `s² + c² − 1`. Reduction modulo it is
`bendix.poly/reduce-square`: every `s^e` becomes
`s^(e mod 2)·(1 − c²)^(e div 2)`. The rule proposes two forms of `p`:
the **sine-free** form (every `s_u²` reduced, all pairs at once) and
the **cosine-free** form (every `c_u²`), each only when it differs
from `p` and stays under the `:too-big` threshold. Both are canonical
forms modulo the ideal (the generators for different arguments have
coprime leading terms, so they are a Gröbner basis under either
elimination order), and that is the completeness argument: two
classes equal modulo the identity get the same term added and merge
through the hashcons or the index, whatever spelling and nesting they
came in. The classic `k·sin²u + k·cos²u → k` is the case where
reduction shrinks; `1 − sin²u → cos²u`, `1 − cos²u → sin²u`,
`sin⁴u − cos⁴u → 1 − 2cos²u` and `(sin²u + cos²u)³ → 1` are the same
rule. `sin²u` alone gets `1 − cos²u` added, a larger form extraction
never picks; that is the price of completeness, and it is bounded:
reduction is idempotent, so once a class holds a form the rule finds
nothing new for it, and class data only descends in the analysis's
well-founded order, so the rule set saturates.

Which spelling the result takes is the cost function's choice, as
always: `sin²x + cos²x` extracts as `1`, `1 − cos²x` as `sin²x`.

**Soundness and the oracle.** Under `pythagoras` a class legitimately
holds forms that differ, so the ring-only oracle of section 4 is
expected to report them and `:dev?` does not apply to this rule set.
Its oracle is the same idea one level up: `trig-inconsistency`
reports a class whose forms differ by something *outside* the ideal,
that is, whose difference has a non-zero sine-free reduction. Tests
run it after every simplification. The numeric oracle stays exact: a
random rational `t` puts `(sin, cos) = (2t/(1+t²), (1−t²)/(1+t²))` on
the unit circle, so every identity the rule uses holds exactly in the
model and the strict-equality test of section 7 carries over.
(Double-angle and sum rules will need a model that carries `t` through
the argument arithmetic; that is item 2's problem.)

**Limits.** A sine whose class has become a ring value (the user
asserted `sin x = 1/2`) is no longer an atom and the identity is not
consulted for it, so `cos²x = 3/4` is not derived. Arguments are
compared as classes, so `sin²(x + y) + cos²(y + x)` is one pair,
because the analysis already merged the arguments. Nested trig
(`sin(sin x)`) is fine: the inner sine is an opaque argument class.

Experiments 4 and 5 (../design/ac-problem.md) measure whether this
reaches the textbook results inside arbitrarily arranged sums at O(n)
nodes, so that bag nodes (answer 3) are not needed for the CAS
milestone.

**`combine-powers`**, the second one. In every monomial the factors
that are powers of one base are a group (`factor`: a bare atom is its
own base to the first power, an `[:expt B E]` atom is `B` to `E`),
and the rule proposes the group as **one power per base**,
`B^(k + S)`: the placeholder `[:expt B (k + Σ c·S)]`, whose exponent
the analysis normalizes. One rewrite, idempotent, so the rule set
saturates as `pythagoras` does.

One form is enough because the cost agrees with it. Under AST size
alone it did not: the spellings are within a node of each other and
the winner depends on what is already paid for (beside another
factor `y·yⁿ` is a node smaller than `y^(n+1)`; alone they tie; at an
offset of 2, a negative offset, a second symbol in the exponent or an
opaque base the combined power wins or ties), so the cheaper spelling
existed only when the input or another rule's rendering happened to
hold it. `[:* :a :y [:expt :y :n]]` stayed at 6 and
`[:* :a [:expt :y [:+ :n 1]]]` at 7, and `simplify` of a result could
be cheaper than the result (found by the suite on Jolt, 2026-09-16;
seed `1789597929120` on the JVM: on the second pass `pythagoras`
rendered the monomial `x⁵·y·yⁿ` while proposing a sine-free form,
`combine-powers` merged it into the class of `x⁵·y^(n+1)`, and
extraction found it). The defect was canonicity, equal inputs with
different answers, and the cost fixpoint was the part of it a test
could see. There are two ways out, and both were built on
2026-09-20:

- *make the cheapest spelling always exist*: a second canonical form,
  `B^k · B^S` with the positive integer part of the exponent returned
  to the ring, proposed beside the first as `pythagoras` proposes
  two. It closed the defect (experiment 7, ../design/ac-problem.md)
  at two to two and a half times the time on a sum of a hundred
  monomials with an offset each, and it printed `y·yⁿ` for
  `y^(n+1)`;
- *make the spelling that always exists the cheapest*: the default
  cost charges a product for a base it repeats (section 6, "The
  spelling of a power"). This is what ships: it is what the
  established systems print, it is one form and not two, and under it
  the second form bought nothing (experiment 8: the same costs, the
  same fixpoints, two to three times slower), so `split-form` was
  removed.

Considered and not built: a separate `split-powers` rule (two rules
to keep in step, and no completeness argument of its own); one form
tuned to the cost ("an offset of 1 out, any other in": the arithmetic
of AST size inside a rule); splitting at materialization (knowledge
of powers in `bendix.core`). Folding the power law into the analysis,
symbolic powers as Laurent monomials, so that no rule is needed and
the spelling is `->term`'s, is the larger alternative and belongs
with section 10 item 4.

**Limits.** A compound base is expanded by the ring before the rule
sees it: `(x + 1)·(x + 1)ⁿ` is `x·A + A`, no monomial holds two
powers of `x + 1`, and it stays at 9 where `(x + 1)^(n+1)` stays at
7. Closing that needs the base recognized inside a polynomial
(division by the base's form), which is not built. A numeric base
never meets its coefficient: the 2 of `2·2ⁿ` is the monomial's
coefficient, not a factor, so `2·2ⁿ − 2^(n+1)` is not 0 and
`a·2·2ⁿ` stays at 6 where `a·2^(n+1)` stays at 7. Maxima combines
these as it builds them (`2·a·2^k` is `a·2^(k+1)`, and `4ⁿ/2/2` is
`4^(n−1)`) and SymPy's `powsimp` does on request; the rule would
have to take from the coefficient the largest power of each numeric
base present.

**An open defect: a power of a sine written as a product, beside
`pythagoras`** (found by experiment 8's soak, 2026-09-20; it is older
than the charge and than the second form, and either arm of either
experiment has it). `x − sin²x + sin^(n+2) x` comes back as
`[:+ [:expt [:cos :x] 2] :x [:expt [:sin :x] [:+ :n 2]] -1]`, 417/32,
when the power is written as a power, and as
`[:+ [:+ [:expt [:cos :x] 2] :x -1] [:expt [:sin :x] [:+ 2 :n]]]`,
449/32, when it is written `sin²x · sinⁿx`: equal inputs, two costs.
The cause is in how forms are spelled, not in either rule. A product
in the input gives the power's class a polynomial, `s²·sⁿ`, and the
atom `s^(n+2)` yields to it (section 4, merge: a form that does not
mention an atom defines it), so every enclosing form is spelled over
`s²` and `sⁿ`; `pythagoras` sees only a class's canonical form, which
is then `x − s² + s²·sⁿ`, and its sine-free form is
`x − 1 + c² + sⁿ − c²·sⁿ`, never `x − 1 + c² + s^(n+2)`, which is
what it proposes when the input wrote the power and the atom was
never defined. Two rules compose only through the form a class
keeps, and which form that is depends here on what the input
spelled. It needs a base that `pythagoras` rewrites, so the
canonicity property draws a sine base only under `powers` alone, and
the suite's property of 100 trials failed in 3 runs of 60 before it
was so narrowed. Candidates, neither built: an atom that is a power
does not yield to a product of powers of its own base (the
convention now says the combined power is the spelling, but the
analysis would have to know what a base is); or the power law in the
analysis (section 10 item 4), where there is no such product to
yield to.

### Differentiation

`[:D u x]` is a term like any other (section 1; decided in section
9): the derivative of `u` with respect to the variable `x`.
Differentiating is equality saturation under the `derivative` rule
set followed by extraction under a cost that refuses `:D`. The result
is whatever D-free form the rules reached, simplified by the same
analysis and rule sets as everything else, and a `:D` no rule could
remove stays in the result and is reported, never guessed at.
Convention: variables are independent. `d/dx y` is zero unless the
graph has defined `y` in terms of `x`, in which case `canonical`
already spells `y` by its definition and the derivative follows it;
a dependence the user wants is written as a term (`[:+ :x 1]` where
`y` was) or, once `:assume` exists, asserted.

**The ring part is computed, not searched.** `ring-derivative` is a
normal-form rule over the pattern `[:D ?u ?x]`. For every match
where the class of `?x` is a variable the graph has not defined and
the canonical data of `?u` is a polynomial `p` over atoms, it
proposes one form, the total derivative

    Σ_a ∂p/∂a · D(a)

over the atoms `a` of `p`, with `D(x) = 1`; `D(y) = 0` for another
variable, since canonical forms are spelled over undefined atoms and
those are independent of `x` by the convention; and `D(c) = [:D c x]`
for an opaque atom `c`, a placeholder over `c` and the class of `x`.
`∂p/∂a` is `bendix.poly/derivative`, the partial derivative of a
polynomial with respect to one atom: every monomial holding `a^e`
becomes the monomial with `a^(e−1)` and its coefficient times `e`,
and a polynomial that does not mention `a` gives zero. The form is
rendered as every normal-form rule's is (the placeholder becomes the
node `[:D ?c ?x]` the graph does not hold yet), and the class of
`[:D u x]`, opaque until then, takes the polynomial as its
definition. Linearity, the product rule and the power rule for the
exponents the analysis folds are consequences of polynomial calculus
and never run as rules: the derivative of a sum of a hundred sines is
a hundred placeholders in one class, and the derivative of
`sin⁵x` is `5 sin⁴x · D(sin x)` in one step, whatever tree the user
wrote and whatever arity the nodes have. The rule declines when `?u`
is opaque (that is the chain rules' case), `:too-big` or `:conflict`,
and when `?x` is not an undefined variable.

`normal-form-rule` gains this second shape: given a pattern, it
visits the pattern's matches (`cromulent.pattern/ematch`) instead of
every root and hands `f` the bindings, `(fn [g bindings] polys)`; the
rendered pattern's variables are merged into the match's, and the
runner instantiates it as before. cromulent does not change for this.

**Atoms: the chain rule, one pattern rule per operator.** Each
rewrites `[:D [op ?u ...] ?x]` to the operator's derivative times
`[:D ?u ?x]`, which `ring-derivative` or another chain rule resolves
in the next iteration:

| rule | left | right |
|---|---|---|
| `d-sin` | `[:D [:sin ?u] ?x]` | `[:* [:cos ?u] [:D ?u ?x]]` |
| `d-cos` | `[:D [:cos ?u] ?x]` | `[:* -1 [:sin ?u] [:D ?u ?x]]` |
| `d-exp` | `[:D [:exp ?u] ?x]` | `[:* [:exp ?u] [:D ?u ?x]]` |
| `d-log` | `[:D [:log ?u] ?x]` | `[:* [:expt ?u -1] [:D ?u ?x]]` |
| `d-quotient` | `[:D [:/ ?a ?b] ?x]` | `[:* [:- [:* [:D ?a ?x] ?b] [:* ?a [:D ?b ?x]]] [:expt ?b -2]]` |
| `d-power` | `[:D [:expt ?u ?n] ?x]`, the data of `?n` a non-zero constant `n` | `[:* n [:expt ?u n−1] [:D ?u ?x]]`, computed |
| `d-power-symbolic` | `[:D [:expt ?u ?v] ?x]`, the data of `?v` not a constant | `[:+ [:* ?v [:expt ?u [:+ ?v -1]] [:D ?u ?x]] [:* [:expt ?u ?v] [:log ?u] [:D ?v ?x]]]` |

The spellings are the normal form's: negative powers rather than
division, so `powers` can combine them, and n-ary products the
analysis reads at once. `d-power` covers the powers the analysis
holds as atoms, negative and rational exponents; for a non-negative
integer exponent the analysis has already folded the power into the
polynomial of `?u`'s parent and `ring-derivative` differentiates it
there, but the factored spelling `n·u^(n−1)·u'` is one the class
would not otherwise hold and extraction may prefer it, so the rule
fires for any constant exponent, and when `u'` is a constant it
folds it in: `3(x+1)²`, not `3(x+1)²·1` beside `3x² + 6x + 3`.
`d-power-symbolic` is the general rule `u^v · (v·u'/u + log u · v')`;
when `v` cannot depend on `x` its second term is a product with a
class worth zero and the analysis drops it, so `x^n` gives
`n·x^(n−1)` and no `log` survives. `d-quotient` is a rule because
division by a non-constant is opaque to the analysis (section 4);
its result comes out in negative powers, and whether a user sees
`(a'b − ab')/b²` is the cost function's business (section 6) or a
rational-function normal form's (section 10). Domain: each rule
holds wherever its right-hand side is defined, which for `d-log` and
`d-power-symbolic` means `u > 0`; that is the convention `powers`
already follows (section 5), and the sign lattice (section 10 item 2)
is what will turn it into a reported assumption.

**Independence.** `independent` is `[:D ?u ?x] → 0` under the guard
that the class of `?u` cannot depend on `x`: its canonical polynomial
mentions no atom that depends on `x`, an undefined variable depending
on `x` only when it is `x`; or, for an opaque or `:too-big` class,
some compound node of the class has only children that cannot depend
on `x`, a nullary node (`[:pi]`) trivially. A `:conflict` class, a
variable leaf in a class with other data, and a class already on the
walk count as depending, so cycles are safe. Every node of a class is
a valid spelling of its value, so one `x`-free spelling is enough,
and definitions are respected because the walk reads class data and
never a variable leaf. This gives `d/dx π = 0`, `d/dx |y| = 0` and
`d/dx f(y) = 0` for any operator without a rule per operator; it is
not needed for variables, which `ring-derivative` handles inline, and
is redundant for anything a chain rule resolves.

**What stays.** An atom whose operator has no rule and whose
arguments may depend on `x`, `[:abs :x]` or a user's `[:f :x]`, keeps
its `:D`, and so does a `:too-big` class under a `:D`: the derivative
gives up where the analysis did. Both are visible in the result and
counted by its cost. The honest answer of section 5 applies to
derivatives too.

**Nesting and iterations.** A chain rule's output holds a `:D` its
successor resolves in the next iteration, and `ring-derivative`
creates one per opaque atom, so every `:D` along the deepest path
costs an iteration and one more sees nothing changed: at most the
depth of the input plus two. The runner's default iteration limit
covers what a person writes; the limits are options as for
`simplify`, and `:stop` reports which one was hit.

**The cost and the front door.** `no-D` is the first vector cost: a
term costs `[undifferentiated, size]`, the sizes of the arguments of
its `:D` nodes summed and then `default-cost`, compared
lexicographically, so a derivative pushed inward always beats the
same derivative left whole (`|x| + x·D|x|` beats `D(x·|x|)`, and
`f'g + fg'` beats `D(fg)` for unknown `f` and `g`), a D-free spelling
beats any other, and the cheapest of those wins. Counting `:D` nodes
instead was tried first and let `D(x·|x|)` stay whole, one `:D`
costing the same as another. The sketch that preceded this design
priced a `:D` at a large constant; a vector says what is left
outright and needs no magic number. It needs cromulent's extractor
to order costs with `compare` instead of `<`, a two-line change that
leaves numeric costs as they were.
`(differentiate t x)` and `(differentiate t x opts)`: `x` must be a
variable (else `ex-info`); the call is `simplify` of `[:D t x]` under
`rules/derivative` together with the caller's `:rules` (none by
default, as for `simplify`; `powers` is what turns `x·x^(x−1)` into
`x^x`), under `no-D`, and the result adds `:undifferentiated`, the
set of `:D` subterms left in it, empty when the derivative is
complete:

```clojure
(differentiate [:sin [:* 2 :x]] :x)
;; => {:result [:* 2 [:cos [:* 2 :x]]] :cost [0 ...] :stop :saturated
;;     :assuming #{} :undifferentiated #{}}

(differentiate [:* :x [:abs :x]] :x)
;; => {:result [:+ [:* :x [:D [:abs :x] :x]] [:abs :x]] :cost [129/64 ...]
;;     :undifferentiated #{[:D [:abs :x] :x]} ...}
```

A `:D` inside any term given to `simplify` with `rules/derivative` is
differentiated the same way, under whatever cost the caller chose.

**Soundness and the oracle.** Every form `ring-derivative` proposes
for a class is equal in the ring to every other after the same
substitutions, because the total derivative commutes with
substituting a definition for an atom, and a chain rule's product is
equal in the ring to whatever else its class holds once the `:D` in
it is resolved, so `derivative` is ring-consistent at saturation:
the polynomial oracle of section 4 finds nothing after the run,
unlike under `trig` and `powers`. It is not consistent after every
application, which is what `:dev?` checks: `independent` settles
`d/dx sin y` at 0 in the iteration a chain rule adds `cos y · D(y, x)`,
and the ring sees that product is 0 only an iteration later. Tests
run the oracle after saturation, and the other sets' oracles apply
as before.
`bendix.poly/derivative` is characterized by linearity, the Leibniz
rule `D(pq) = D(p)·q + p·D(q)`, `D(a) = 1`, `D(b) = 0` for another
atom, and the symmetry `∂²p/∂a∂b = ∂²p/∂b∂a`, so it is tested as
properties with no reference at all. The engine's oracle is a
reference differentiator over terms in the tests, a dozen lines of
textbook rules over the binary tree as written, spelling `log`'s
derivative as a negative power so the formal model of section 7
evaluates it; its result and `differentiate`'s must land in one class
when added to one e-graph under the same rules, and must agree
numerically at random rational points in the models of section 7.
Both are symbolic derivatives, so they differ only by identities the
rule sets used, which the models respect exactly; that the unit
circle does not differentiate like sine does not matter, and no rule
set is excluded from the numeric check. Further properties:
`:undifferentiated` is empty over the vocabulary the rules cover;
the derivative of the result is a cost fixpoint; the graph is
well-formed; saturation takes at most `d + 2` iterations.

**Limits, named.** `abs` waits for the `abs-sign` rule set; `|x|²`
therefore keeps a `:D` though `x²` would not, because the chain rule
sees the atom and not through it. A derivative whose root class
passes the `:too-big` threshold is extracted as the rendered total
derivative with its atoms' derivatives substituted in, and that
spelling can hold literal zero summands and monomials that became
equal only once those derivatives resolved; a second `simplify` of
the result, a smaller term that fits the threshold, collects them
and costs less, so the cost fixpoint of section 6 does not hold
across the threshold (found 2026-09-25 by the trig property's seed
1790343606336: a product of two sums holding `x/x` and `x⁻¹`,
48 summands with 6 zeros at the test's threshold of 50 and cost
4807/16, against 41 summands and 4567/16 at 100 or above; identical
on the engine before and after that day's cromulent change). The
honest fix is either a rendering that collects like terms and drops
zeros without a class polynomial, or a threshold that the derivative
front door raises for the root; neither is designed. A derivative with respect to
anything but an undefined variable is left alone by `ring-derivative`
and `independent`, while the chain rules, which are formal, still
peel operators off it. Integer-valued exponents that vary with `x`
(`2^n` differentiated in `n`) go through `d-power-symbolic` as if
real, the convention every CAS shares.

## 4. Analyses

- `const`: constant folding over exact numbers (the classic). The
  polynomial analysis already folds ring constants, `exp 0` and
  `log 1`; `const` is for what remains (`abs`, integer `gcd`).
- `poly`: the polynomial normal form (../design/ac-problem.md C), designed in
  detail below. In a dev mode over *ring-only* rule sets it is a
  soundness oracle: any two classes that merge with different
  polynomials expose a wrong rule, by name.
- `nonzero` / `sign` / `positive`: a small lattice
  (`unknown ⊑ nonneg, nonpos ⊑ zero, pos, neg`) computed from
  constants, squares, `exp`, `abs`, sums of positives, products, and
  from user assumptions. This is what makes conditional rules fire
  soundly.
- Later: `integer`, `real`/`complex` domain, interval bounds.

Analyses compose through the core's `compose`; the CAS ships a default
composition.

### The polynomial analysis

The data of a class is its **normal form**: a sparse polynomial with
exact rational coefficients over a set of *indeterminates*, as a
sorted map from monomial to coefficient, a monomial being a sorted map
from indeterminate to positive integer exponent. `{}` is zero; `{{} 1}`
is one; `{{:x 1} 2, {:x 2} 1}` is `2x + x²`. Sorted maps give a
canonical value with structural equality, which is all the merging
index needs.

**Indeterminates** are of two kinds. A *variable* is its keyword. An
*opaque class*, one none of whose nodes is a ring operation, is named
by its class id, as ../design/ac-problem.md specifies; its own data is
`{:atom id}`, and its parents read that as the variable `id`. Opaque
nodes are not interpreted, so the name is a placeholder for "whatever
that class is worth", and a polynomial over such names is a correct
statement about the graph.

**A canonical form is spelled over undefined atoms only.** An atom is
*defined* when its class is worth something other than itself: an
opaque class a rule proved is worth a product of other atoms
(`exp(x + y) = exp(x)·exp(y)`), or a variable the graph asserted or
solved to be a constant (`x = 2`). `canonical`, the one function
through which every form is read, maps every class id to its root and
replaces every defined atom by its class's form, recursively, under
the `:too-big` limit, with one guard: an atom whose chain of
definitions reaches itself stays an atom, so `sin y = a·sin y` and a
two-cycle of such assertions stay finite. Without this the analysis
was not canonical modulo the equalities the graph itself held: the
join keeps the smallest form and an atom is the smallest spelling of
anything, so classes that mentioned `exp(x + y)` before the proof kept
the one-atom spelling while classes built afterwards from the product
spelled it with two, and `sin²x·x^(n+m) + cos²x·xⁿ·xᵐ` stayed as
written under `trig` + `powers` because its two cofactors were one
class spelled two ways (found 2026-09-13 while designing `exp-log`;
likewise `x + y` and `y + 2` under `x = 2`, since `x + y` orders below
`y + 2` on coefficient size). Ids go stale when classes merge and
definitions arrive later; the core recomputes the data of every class
whose nodes or children changed, so neither survives a rebuild. A
variable is looked up only when the analysis state says some variable
is defined, so the common path costs what it did.

**make** on a node: a number is a constant; a variable is itself; `:+`,
`:*`, `:neg`, `:-`, `:/` by a constant and `:expt` with a non-negative
integer exponent, or a non-zero constant base with a negative integer
exponent, combine the children's polynomials; `:exp` of the
zero polynomial is 1 and `:log` of the constant 1 is 0, the two points
of that family where an exact value exists; any other node is opaque,
whatever its children's data (a `sin` of a `:too-big` class is an
atom, not too big). Negative exponents and division by a non-constant
are not ring operations and stay opaque for now (a rational-function
normal form is a later analysis).

**merge** is the semilattice join. Two equal polynomials join to
themselves. Two different ones mean this e-graph asserts they are
equal. In order: `:conflict` absorbs; a given-up class absorbs; an
atom `{:atom id}` is below `:too-big` and below any form that
*defines* it, one that neither mentions it nor holds an atom *built
from* it, while a form that mentions it (`sin y = a·sin y`) is an
equation the class records with the atom staying its representative,
and so is one with an atom built from it: reachable from that atom
through the children of opaque nodes, ring nodes being equations and
not structure. `exp(eˣ)⁻¹·D(exp(eˣ))` for `eˣ`, which `d-log`
proposes once `log(exp(eˣ))` has merged into `eˣ`'s class, would
spell the primitive over its own derivative; when the derivative was
then proved worth `exp(eˣ)·eˣ` that honest definition was refused as
cyclic, the bloated one stood, and `5eˣ` could never be rendered as
`[:* 5 [:exp :x]]`, so `simplify` was not a fixpoint (found by the
suite on Jolt, 2026-09-16); `:too-big` (a term count over
the threshold) absorbs polynomials; a difference that is a non-zero
constant (`x = x + 1`) is a contradiction in the ring itself and
becomes `:conflict`; otherwise the join is the *preferred* polynomial.
The unit polynomial of another class, "`sin x`" as `sin x · 1`
computes it, is an ordinary polynomial here and not an atom: it says
the class is worth that class, which `reconcile` and the index act
on. Reading it as an atom that yields to a definition let a class
holding `[:D c x]` beside `−(−sin x)` keep its own name, and a root
worth `e^y` keep `e^-u · D(e^u)` (found by the derivative's soak,
2026-09-13).
The equation is kept as an assumption the graph made, not a bug:
`sin²x + cos²x` joined with `1` is a true identity the ring cannot
see, and `x = y + 1` is a user assertion.

**Which form is preferred is fixed for the simplifier: the built-in
order.** A measure can be put in front of it, and the family of
measures keeps the analysis's guarantees, but that is an experiment's
knob and not an option of `simplify` (below). The built-in order is
the smaller under a total order
(fewer opaque atoms, then fewer terms, then lower degree, then smaller
coefficients by size, then term by term). Opaque atoms count first
because a form over variables alone is the class's value and one
over unknowns is not, whatever its term count: a root worth `2x + 2`
kept `e^-u · D(e^u)`, one term over two unknowns, and its parents
computed with it (the derivative's soak, 2026-09-13). `:prefer` puts a *measure* in front of it: a
function from a polynomial to a vector of natural numbers, the
smaller key winning, shorter keys first, ties to the built-in order.
`fewest-terms` (the default as a measure), `lowest-degree`,
`fewest-atoms` and `most-terms` (bounded by the threshold) ship. A
comparator could not be checked for well-foundedness; a measure into
naturals is well-founded by construction, and its lexicographic
product with a well-founded total order is well-founded and total, so
termination and cross-runtime determinism hold for any plug. The
measure sees the polynomial only, never the graph, so the order cannot
shift under the analysis. What the choice cannot affect: soundness,
since every form is valid; and completeness, since each rule proposes
every canonical form of its fragment and every form a class holds is
indexed, so a proposed form meets the class that has it whatever
representatives the joins kept. What it does affect: the representative parents
compute with, hence speed and how soon the threshold is hit, and the
materialized term. This is the pattern of Knuth–Bendix orders and
Gröbner monomial orders, a family proven once with pluggable
parameters, rather than egglog's user-written merge functions, which
are unchecked. Experiment 6 (../design/ac-problem.md) measures it: all
four measures reach every workload target, and `most-terms` costs
thirteen to fifteen times the time.

`:prefer` was an option of `simplify` until 2026-09-20 and is now an
option of `bendix.analysis/poly-analysis` only, where the bench
reaches it. Experiment 6 answered its question, nothing else used a
measure, and the kept form is not only a performance matter for
results: it is the form `materialize-all` renders, hence one of the
candidates extraction chooses among, so every guarantee about results
(section 6) would have to hold for every measure, and they are
tested under the built-in order alone. Soundness and completeness do
not depend on it, as above; what a user would have bought with the
option was a different representative and an untested promise.

The core joins what a class's nodes now say *into* what the class
had, so a class keeps the preferred form it has ever derived; every
such form is valid under the equalities asserted, so this is sound,
and the data descends in the order except when re-spelled. The order
is well-founded because term count, degree and coefficient size
(|numerator| + denominator), or a measure into naturals, come before
anything else: below any polynomial there are finitely many others. A
re-spelling happens only when some atom becomes defined, which each
class does at most once, so a class changes finitely often and no cap
is needed. A class asserting `a = a/2` simply keeps `a`.

The equation is then used. The core hands the analysis's `reconcile`
the forms that met in a class (the two sides of a union, or every
node's form at a recompute), so no second pass over the nodes is
needed. Two forms whose difference is `α·v + β` for a single atom `v`
determine it, and `reconcile` unions `v` with the constant `−β/α`: `a = a/2` and `a = −a` give `a = 0`,
`a = 2a + 1` gives `a = −1`. A form that is exactly another class's
atom identifies the class with it. A difference that is a non-zero
constant is `:conflict`. Anything else (`x = y + 1`,
`sin²x + cos²x = 1`) the ring cannot resolve; the class keeps its
smallest form, and the equation is what the `:assuming` bookkeeping
of section 5 will record.

**modify** is where the normal form does its work. The analysis keeps
an index from polynomial to class id in a key of the e-graph value
that belongs to it (the core allows analysis-owned state; cromulent
IDEA.md section 9). Every class is indexed under every canonical form
it holds, an opaque class under its own atom, so `sin x · 1` is the
class of `sin x` during saturation and not only at extraction:
`modify` indexes the form the class keeps when a node is added or
its data changes, and `reconcile` indexes every form at every
recompute, so two classes that share any form merge whatever
representatives their joins chose. Only the second catches a
proposed form whose placeholder atom is fresh when its node is
created and is spelled with the atom it merges with only later
(`combine-exp`'s `exp(y + (y + 2x))` beside a class already holding
that exponential; the derivative's soak, 2026-09-13). Modify looks
the form up: another class with the same normal form is unioned with
it.
That union is what replaces associativity, commutativity,
distributivity and like-term collection as rules: every arrangement
of a sum lands in one class without any of the 3ⁿ e-nodes existing.
Materializing the normal form as a node, so the expanded form is
extractable, is done only at the root on request (`:expand`) or never;
doing it everywhere would reintroduce the nodes the analysis exists to
avoid.

**What it does not do.** It cannot see `sin²x + cos²x = 1` on its
own; that is a rule (a normal-form rule, section 3). It does not
decide equality of rational functions, or of anything under a radical
or a transcendental function. It is the ring fragment, complete there
and honest about its edges.

### Coefficient algebras

Folding coefficients in ℚ is unsound for the time-and-space
projects: three-registers and dirty-work compile over
GF(2^w), where `x + x = 0`, and tree-evaluation's compiler wants the
algebraic normal form of a Boolean circuit as this analysis
(../../time-and-space/tree-evaluation/COMPILER.md, "Middle end").

`bendix.algebra` makes the coefficient ring a parameter: the
`Coefficients` protocol (ring operations, `from-integer`, a partial
`inv`, and `size` and `cmp` for the well-founded order on forms) and
`rational`, bendix.num's ℚ. Decided 2026-10-01:

- **bendix owns the protocol.** symbolics is upstream of
  time-and-space, so bendix does not depend on `catalytic.algebra`;
  time-and-space adapts and tests bit-exact agreement.
- **The algebra is an explicit argument.** Polynomials do not carry
  it. Each coefficient-touching `bendix.poly` function takes it first,
  with the existing ℚ arities unchanged (orrery depends on them); where
  an optional limit exists, the algebra arity takes it explicitly, so
  arities never collide. The polynomial analysis holds it as
  `:algebra`. A dynamic binding was rejected: its extent is unclear
  under saturation and laziness.
- **Division is partial.** `:/` by a constant and negative constant
  powers fold only for units; `linear-in-one-atom` solves only when
  the atom's coefficient is a unit.
- **`exp 0 = 1`, `log 1 = 0` fold over ℚ only.**

**The finite fields.** `(alg/gf2 w)` is GF(2^w) for w in 1..32 on
every runtime, `(gf2 1)` being GF(2); `bendix.algebra64/gf2-64` is
GF(2^64), JVM and Jolt only. Both are written as catalytic-buffer
writes them and use its moduli: the default tail at each width is the
smallest primitive one, which at 8, 16 and 32 is catalytic.algebra's
0x1D, 0x2D and 0xAF, and GF(2^64) is catalytic.gf64's
x⁶⁴ + x⁴ + x³ + x + 1 over signed longs. Literals belong to the
algebra (`read-literal`, `write-literal`): in GF(2^w) an integer is a
bit pattern, so `[:+ 3 5]` is 6, and a constant that is not an element
(a ratio, 300 in GF(2^8)) makes an opaque class. `from-integer` is
n·1, the parity of n, not its bit pattern. `simplify` takes
`:algebra`.

**Exponents are integers, not elements**, and bendix.core does not
yet give them a domain of their own. Over an algebra other than ℚ,
`saturate` evaluates every exponent to an integer literal before the
term is added, and refuses a symbolic one; `:expt` reads its exponent
from that literal. See *Exponents over other algebras* below.

Next, in this order:

1. **Boolean atoms**, a set or predicate of atoms satisfying
   `x² = x`, independent of the coefficients (three-registers: GF(2^64),
   none; tree evaluation: GF(2), all). Over GF(2) with every atom
   Boolean, the normal form is the ANF: canonical, so the analysis
   decides circuit equality and exact degree. `derivative` rejects
   Boolean atoms.
2. **Boolean operators** in `ring-op` under Boolean atoms: `:and` as
   `*`, `:xor` as `+`, `:not x` as `1 + x`, `:or x y` as `x + y + xy`.
3. **Rule sets by algebra.** `trig`, `exp-log`, `powers` and
   `derivative` are ℚ-only; elsewhere the default rule set is empty.
   Until then a caller passing `:algebra` passes no rules. Oracle for
   GF(2) with Boolean atoms: tree-evaluation's `treeval.compile.anf`
   on random circuits.

#### Exponents over other algebras

An open problem. Over ℚ an exponent is a value like any other. Over
GF(2^w) it is not: 1 + 1 is 0, but x^(1+1) is x². The e-graph shares
one class per subterm, so an exponent's subterms fold and merge as
elements: `[:+ :n 1 1 1]` merges with `[:+ :n 1]` in GF(2), and
congruence then equates x^(n+3) with x^(n+1). Closed exponents
(`[:+ 1 1]` merging with the literal 0) are the same failure. The
stopgap above keeps this sound by refusing what it cannot place.

**Why symbolic exponents are worth having.** The exponent domain
depends on what the power is of:

| power of | exponent domain |
|---|---|
| a formal polynomial | ℕ (ℤ with units) |
| an atom ranging over GF(2^w), x^(2^w) = x | 0, or ℤ/(2^w − 1) |
| a root of unity ω of order m | ℤ/m |

- *Field equations.* Boolean atoms (x² = x) are the w = 1 case of
  atoms ranging over the field; their exponents reduce the same way.
- *Frobenius and addition chains.* x^(2^k) is GF(2)-linear, so a power
  is a chain in which doubling the exponent is nearly free and adding
  two costs a multiplication: Itoh–Tsujii inversion,
  x^(2^w−2) in about log w multiplications; the AES S-box, inversion
  in `(gf2 8 0x1B)` and an affine map, which masked implementations
  (Rivain–Prouff, CHES 2010) compute with four multiplications. Ben-Or
  and Cleve's cost has the same shape — linear operations cheap,
  multiplication depth 4^d — which reopens ../../time-and-space/
  three-registers' declined field inversion beside its `:sq`
  primitive. Choosing the chain is an extraction over exponent terms.
- *Roots of unity.* Σⱼ ω^(jk) is 1 when m divides k and 0 otherwise
  (m odd, characteristic 2): the identity behind tree evaluation's
  degree filter, derivable rather than only computed.

**Options.**

- *Two algebras in the analysis.* `:algebra` folds values; an
  exponent algebra (a `Coefficients` instance: ℤ by default, later
  ℤ/(2^w − 1) or ℤ/m) folds everything below an exponent position.
  The leaves there are wrapped in a record (bendix.term, the one place
  leaf meanings are read), variables as well as constants, so that no
  exponent node is the node of a value; operators need no renaming,
  since a node built over different leaves is a different node. The
  exponent algebra reads and writes the wrapped literals, class data
  marks which algebra a polynomial is in, and the index keys on
  [algebra polynomial], since n as an exponent and n as a value are
  the same polynomial. The wrappers come off at extraction.
- *Domains in cromulent.* Classes carrying a domain, and union
  refusing to cross one. The guard is available as a bendix analysis
  whose merge rejects a mismatch, so this pays only with a second
  client or with matching that sort conditions dominate.

**Open questions.** The domain of an exponent's exponent (one wrapper
level per nesting, or nested powers opaque); how a rule that builds
exponent arithmetic (x^a · x^b → x^(a+b)) evaluates or wraps it; what
to call the concept, since "sort" reads as ordering and "kind" is
taken by class data ("domain" collides with nothing here).

## 5. Conditions, soundness, and honest answers

A merge is global and permanent within the value. Merging `[:/ :x :x]`
with `1` when `x` might be zero poisons everything downstream. The
rule is simple and unbreakable: **a conditional rewrite fires only
when an analysis proves its condition.** No analysis, no merge.

Users still want `x/x → 1`. Three ways to give it to them, all
explicit:

1. **Assumptions**: `(simplify t {:assume [[:not= :x 0] [:> :y 0]]})`
   seeds the `sign` analysis; the result's `:assuming` echoes what was
   used.
2. **Conditional results**: a mode where conditional rules fire
   speculatively on a *copy* of the e-graph (persistence makes this
   cheap) and the result reports the conditions it relied on:
   `{:result 1 :assuming #{[:not= :x 0]}}`. The user, not the engine,
   decides whether that is acceptable.
3. **Disequalities in the graph** (Zakhour 2025): a later upgrade so
   `x ≠ 0` can be *derived*, not only assumed.

This is a user-experience decision as much as a technical one. Users
of every mainstream CAS have been burned by a silent `x ≠ 0`; the
difference between "wrong" and "right, given this assumption you can
see" is the difference between a tool people trust and one they
double-check by hand. Option 2 is the one to get right.

One rule set is exempt by the convention every CAS shares, and the
exemption is named here so it is not silent: `powers` combines
exponents unconditionally (section 3), so `x · x⁻¹` becomes `1` and
`x⁻² · x³` becomes `x`, defined at `x = 0` where the input was not,
with `0⁰ = 1`. Division stays opaque (`[:/ :x :x]` is not `1`), so
the exemption reaches only what is written as a power. When option 2
exists, `x ≠ 0` from a power combination is the first assumption
`:assuming` reports. `exp-log` needs no exemption: `exp` is never
zero, so `exp(x)·exp(x)⁻¹ = 1` and `exp(x)^½ = exp(x/2)` hold wherever
the input is defined.

## 6. Cost functions: where "simplest" lives

A saturated e-graph contains the expanded form, the factored form, and
everything between. Extraction chooses, by a cost function: that is
cromulent's mechanism (`(fn [node child-costs])`, anything `compare`
orders), and extraction does not exist without one. bendix ships two
costs and makes its promises about those two:

- **For any cost function** a result is sound: it is a term of the
  root's class, and every rule and every form in the class preserves
  value.
- **For the costs that ship, under the rule sets that ship**, the
  result is canonical up to ties (equal spellings of a value reach
  one cost), its cost is a fixpoint (`simplify` of a result costs
  what the result did), and under `default-cost` a term never grows
  but by one node for each repeated base it combines (below).
  These are properties of rules and cost together, not of `simplify`
  alone: they hold when the cheapest spelling under the cost is among
  the forms the rules always propose, which can be arranged and
  tested for a cost we know (`default-cost` charges a repeated base
  so that `combine-powers`' one form is the cheapest, below) and
  cannot for one we do not. A tie goes to
  cromulent's node order, which is the same on both runtimes and not
  across input spellings, so canonical means the cost, not the term.

`:cost` stays an option of `simplify`: `differentiate` is `simplify`
under `no-D`, and a caller's own cost gets the first promise. The
option is a function of the saturated e-graph that returns a
cromulent cost, `(fn [g] (fn [node child-costs] …))`, because a
shipped cost reads the e-graph (below); a plain cost `f` is
`(constantly f)`. A cost
joins the second list by being tested against every rule set, the
way `no-D` was. Until 2026-09-20 this section called the cost "a
first-class, user-supplied value" and listed `prefer-factored`,
`prefer-expanded`, operator cost tables and a combinator set; none
was built, no caller asked, and the promise of canonicity for costs
nobody had written shaped decisions it should not have (the
`combine-powers` defect was first weighed against them). They come
back when something needs them.

- `default-cost`: fewest nodes (`size`: with a slight preference,
  1/64 of a node, for the operators normal forms are written in, so
  that of `x/2` and `(1/2)·x` the latter wins), and a product whose
  class is one monomial pays 2 for each base it repeats ("The
  spelling of a power", below). The
  default. Ties that remain go to cromulent's deterministic node
  order, so a result is the same on both runtimes.
- `no-D`: the cost of a term as the vector `[undifferentiated, size]`,
  the sizes of the arguments of its `:D` nodes summed and then
  `default-cost`, compared lexicographically, so a derivative pushed
  inward beats one left whole, any D-free spelling beats any other,
  and the cheapest D-free one wins. **Differentiation is
  simplification with a cost function that refuses derivatives**: the
  derivative rules make `[:D [:sin [:* 2 :x]] :x]` equal to
  `[:* 2 [:cos [:* 2 :x]]]`, and extraction with `no-D` picks the
  latter; a `:D` that survives is measured, not hidden. The same
  trick gives `integrate` for the rules we have, and "solve for x" as
  a cost that wants `:x` alone on one side; both are vector costs. A
  cost is anything `compare` orders (cromulent IDEA.md section 8): a
  number as before, or a vector, and a vector cost is monotone when
  no component decreases from a child to its parent and the last
  strictly increases.

### How the default's opinions are decided

"Simplest" has no definition free of context (Moses 1971, "Algebraic
Simplification: A Guide for the Perplexed"; Carette 2004,
"Understanding Expression Simplification", makes it description
length relative to a context), so every system chooses its opinions
and builds them in. None asks its user what simplest means:
Mathematica ranks by leaf count with a correction for long integers
(the default of `ComplexityFunction`), SymPy by operation count
with a bound on growth (`measure`, `ratio`), and Maxima, REDUCE,
GiNaC, FriCAS, SymbolicUtils and Emmy have no measure at all, only
fixed forms, switches and pipelines. Where what the user cares about
really varies they offer named verbs (`expand`, `factor`, `collect`,
`powsimp`, `combine`). bendix does the same, and settles what a
result looks like by an order of precedence, not case by case:

1. **Soundness.** A result is worth what the input was.
2. **Canonicity.** Equal spellings of a value get one answer.
3. **Convention.** What the established systems return for the
   equivalent request. A rule set the caller names is the equivalent
   of their `simplify` or their named transformer (`powsimp`,
   `combine`), not of their automatic layer.
4. **Fewest nodes.**

Where intent varies (expanded against factored) the answer is a named
verb, a rule set and a cost that ship and are tested together, as
`differentiate` is `derivative` with `no-D`; `simplify` does not grow
a knob.

Convention is the default answer and never the end of the inquiry. A
decision taken at step 3 is recorded with what was looked at beside
it: what the systems actually do, read from their documentation and
source on the day and not recalled (the first survey overturned a
recollection about SymPy); what the alternatives are; what recent
work says; and whether holding every form at once opens an answer a
system that holds one term could not have. The record ends in a
verdict. A question is a decision to deliberate only when two levels
conflict, when the systems disagree at the level that applies, or
when the exploration finds something better; what it finds that is
not for now goes to section 8, "Where bendix can differ".

### The spelling of a power

Decided and built 2026-09-20. Before it, fewest nodes with the two
forms of experiment 7 returned `a·y·yⁿ` for `a·y^(n+1)` and, by ties
that node order broke toward the product, `y·yⁿ` for `y^(n+1)` and
`y·y` where `y²` costs the same.

What the systems do, read 2026-09-20 from documentation (D) and from
source or upstream tests (S); none was run:

| | builds `y·yⁿ` as | `simplify`, or the named verb, returns |
|---|---|---|
| Mathematica | `y^(1+n)` (D) | the same |
| Maxima | `y^(n+1)`, for any base, and `2·a·2^k` as `a·2^(k+1)` (S) | the same |
| SymPy | as built; combines only when the summed exponent is not a sum, `x^y·x^(2y)` (S) | `y^(n+1)`, `2^(n+1)`, `exp(x+y)`: `simplify` runs `powsimp` (S) |
| SymbolicUtils | as built (S) | rules for `y^n·y` and `x^n·x^m` (S) |
| Maple, FriCAS | as built | `combine(…, power)`, `simplifyExp` combine (D) |
| GiNaC, Emmy | as built (S) | no verb combines a symbolic exponent (S) |
| REDUCE | split: `combineexpt` is off (D), `expandexpt` on (S) | |

The automatic layers disagree, in three camps: combine (Mathematica,
Maxima), leave as built (SymPy, which once combined and stopped, and
most others), split (REDUCE). bendix has no automatic layer in which
to take a side: a product as built and its combined power are one
class and the choice destroys nothing. At the level that applies, a
caller who names `powers` is calling `powsimp`, and there every
system that has the verb combines. All of them write `y·y` as `y²`.

So: **one power per base** under `powers`, and `y²` for `y·y` with
or without rules. It is also the safer direction to print. SymPy
guards the split since 1.12 (its issue 23952: at a zero base the
split of `0^e` is `nan`) and no system guards the combination: at
`y = 0`, `n = −1` the power `y^(n+1)` is 1 under section 5's
convention and `y·yⁿ` is undefined, so printing the combined power
never gives a result defined at fewer points than the input, and
printing the split can.

**The cost.** A `:*` node pays 2 for each base that appears in more
than one of its children. The bases of a child are read from its
class's canonical form when that is one monomial (the bases `factor`
gives its atoms, section 3), so the charge sees through nesting
(`y·(a·yⁿ)` pays as `a·y·yⁿ` does) and a child that is a sum has
none. Why 2: writing one power costs at most the exponent's `:+` and
its constant and saves at least the node of `B^k`, so the combined
spelling is never more than one node larger than a split one (exactly
one for a leaf base, an offset of 1 and a one-term exponent beside
another factor; a tie or a win everywhere else), and 2 makes it
cheaper by at least one, a margin the 1/64 preferences cannot reach.
The charge is a constant on a node, so the cost stays monotone; a
result under `powers` pays it only where the rule could not combine,
so the cost reported for a result is otherwise its size as before;
and a product that repeats a base where no rule can combine it pays
the same in every spelling and loses nothing. The charge is only for
a product whose class is one monomial: a product whose class is a sum
of monomials, `x²·sin x · (−sin x) · (sin x − 1)`, has no spelling
with one power per base, and its expansion is a different shape that
repeats nothing, so a charge there only paid the expansion to grow.
Until 2026-10-01 every product paid it, and that term, 16 nodes with
two repeats, became its 19-node expansion by the 1/64 preference
(the never-grows property, seed 1790827792477).

The cost needs the e-graph, which `(fn [node child-costs])` does not
see. egg's idiom for this is a cost function that closes over the
e-graph, and the narrowed contract above permits it: `:cost` is a
function of the e-graph that returns a cromulent cost,
`(fn [g] (fn [node child-costs] …))`; `default-cost` and `no-D` are
such functions and a caller's plain cost is `(constantly f)`.
cromulent did not change. The table of bases
(`bendix.rules/power-bases` of every class that is a child of a `:*`
node) is built once per extraction; `bendix.core/term-cost` is what
a term costs as it is written, which is how a test counts the
repeats an input pays for.

What it changed:

- `combine-powers` is one form again (section 3). The cheapest
  spelling under both shipped costs is the one the rule always
  proposes, which is the condition the second promise rests on, and
  `split-form` went. The canonicity tests stayed and were the judge:
  the three spellings of `a·y^(n+1)` reach 7, not 6.
- Never-grows is restated: a result is no larger than what was
  written but for one node for each repeated base it combines
  (`a·y·yⁿ`, 6, becomes `a·y^(n+1)`, 7; with no rules at all
  `y·y·z`, 4, becomes `y²·z`, 5), as Mathematica's is in leaf count;
  SymPy's `simplify` allows growth up to `ratio`, and no system we
  read promises anything in nodes. Tested as that bound, with the
  repeats counted by `term-cost`, for every rule set.
- Experiment 8 (../design/ac-problem.md): under the charge one form
  and two forms reach the same costs and the same fixpoints on
  experiment 7's workload, one form two to three times faster where
  monomials have offsets; the table costs well under a millisecond
  of extraction on a graph of 500 nodes, on both runtimes.

What else was looked at, and the verdict:

- *Fewest nodes*, what is built. Defensible in one sentence, and
  surprising in three places (above).
- *A DAG cost*, which the extraction literature scores by
  (github.com/egraphs-good/extraction-gym): a shared `y` is counted
  once, so `y·yⁿ` gets cheaper still. It moves away from the
  convention, not toward it.
- *Weights in the manner of Carette*: a constant addend in an
  exponent is nearly free. It can be made local, the `:+` reporting
  a discountable part in a vector cost and the `:expt` applying it,
  and is then a function of the term alone; but it is arithmetic
  tuned to one case, does nothing for `y·y`, and makes every cost a
  vector. The charge above states the convention itself.
- *REDUCE's choice*, the split as the canonical form: `x^a` and `x^b`
  are then independent kernels and polynomial arithmetic applies to
  them. That is the precedent for folding the power law into the
  analysis (section 10 item 4): split inside, combined in print.
- *Both forms to the caller*, which only a system holding all forms
  can offer: section 8, "several forms from one saturation".
  `split-form` would come back there as what a named verb
  guarantees, the equivalent of SymPy's `expand_power_exp`.

Verdict: the convention stands. Nothing found argues for printing a
power differently; what is ours is that the choice is one function
over a class that holds both.

Found on the way: a numeric base never meets its coefficient
(section 3, limit), and results that tie can differ as terms
(section 9).

## 7. Testing

- **Numeric oracle.** For a random expression, `simplify` it, then
  evaluate original and result at random exact rational points; they
  must agree wherever both are defined (skip points where a
  denominator is zero or a log argument is non-positive). Exact
  arithmetic makes this a strict equality, not a tolerance. For `exp`
  and `log` the model is formal: a value that mentions an exponential
  is a Laurent polynomial in one indeterminate `T` with `exp v = T^v`
  for an integer `v` and `log T^v = v`, so every identity the rule set
  uses holds exactly and no number ever grows (a base-2 model was
  tried first and failed on `exp(64)² = exp(128)`: bounding the
  argument made the domain not closed under the identity). This test
  catches unsound rules better than any curated example set; on the
  day `exp-log` landed it found two real defects in the analysis.
- **The polynomial oracle** in dev mode (section 4) catches unsound
  ring-fragment merges at the moment they happen, with the rule name.
- **Derivatives.** `bendix.poly/derivative` is characterized by
  linearity, the Leibniz rule and its values on atoms, so it is
  tested as properties with no reference. The engine's oracle is a
  reference differentiator over terms in the tests, textbook rules
  over the tree as written; its result and `differentiate`'s must
  land in one class under the same rules and agree in the models
  above, which respect every identity the rules use, so a symbolic
  derivative is compared with a symbolic derivative and the model
  need not differentiate like sine (section 3, "Differentiation").
- **Canonicity, the cost fixpoint and never-grows** (section 6), for
  the costs that ship against the rule sets that ship: over random
  terms, `simplify` of a result costs what the result did, and a
  result is no larger than what was written but for one node for
  each repeated base it combined (the repeats counted by
  `bendix.core/term-cost`); and where equal spellings of a value can
  be generated they are put in a random context and must reach one
  cost (`b^(s+k)` beside a cofactor written four ways, for
  `combine-powers`; with `pythagoras` beside it the base is not a
  sine, section 3, "Limits"). The fixpoint property is the one that
  found the defects of 2026-09-16; canonicity is what it was a
  symptom of, and is tested directly.
- **Textbook set.** A curated table of inputs and expected outputs per
  rule set, run alone and combined.
- **Emmy as a second oracle**, later: simplify with both and compare
  numerically. Not a dependency of the library.

## 8. Relationship to other systems

Emmy is the mature Clojure CAS (a port of scmutils) with a rule-based
directed simplifier and polynomial canonicalization. We are not
competing on breadth, and we deliberately do not share its syntax:
Emmy already serves people who want scmutils in Clojure. What an e-graph simplifier offers that Emmy's
design does not: no rule-ordering sensitivity, all equal forms
available for extraction under different costs, cheap "show your
work" once explanations land, and conditional results as values. An
Emmy adapter (their expression format to ours and back) is a later,
small, optional piece; Emmy's test corpus is a resource.

### Where bendix can differ

The default output follows the established systems (section 6, "How
the default's opinions are decided"), and every time it does, the
design looks at what else is possible. This is the running list of
what those explorations found that a system holding one term at a
time cannot do and a persistent e-graph can. Nothing here is built
or promised; each item names the milestone it would belong to.
Sources were read on the date given, not recalled.

- **Assumption contexts as layers over one saturated graph**, and
  answers that carry their condition ("`x`, provided `x ≥ 0`")
  instead of a refused rewrite. Colored e-graphs (Singher and
  Itzhaky 2023, arxiv.org/abs/2305.19203) keep several congruence
  relations in one structure at a tenth of the space of a graph per
  assumption; a persistent e-graph value already gives the cheap
  fork, so the question for the sign lattice (section 10 item 1) is
  whether contexts are forks or colours, and whether the lattice's
  own order (`x > 0` implies `x ≥ 0`) is the order of the contexts.
  Looked at 2026-09-20.
- **The sign of a class is the meet over all its spellings.** An
  abstraction refined by every member of the class is tighter than
  any one term's (Coward et al. 2022, arxiv.org/abs/2205.14989), and
  a tighter sign unlocks more conditional rewrites. Section 10
  item 1. Looked at 2026-09-20.
- **Several forms from one saturation.** Convention is one cost;
  fewest nodes, Horner and factored are others, and the saturated
  graph is a value that can be extracted from more than once. In our
  terms each form is a named verb with its own tested cost (section
  6), sharing one saturation. Herbie's authors want the same thing
  for accuracy against cost (Panchekha 2025,
  pavpanchekha.com/blog/e-herbie.html) and name unsound rules as
  what stops them. Looked at 2026-09-20.
- **Show the steps.** Proofs from congruence closure are small and
  cheap (Flatt et al. 2022, arxiv.org/abs/2209.03398); the research
  pass found no CAS that shows its work this way. A merge made by the
  analysis needs a synthesized step ("by ring normalization"), which
  is the open part. cromulent's explanations milestone.
- **A user's equation as theory.** `x² + y² = 1` asserted once and
  active in every class polynomial through reduction modulo a
  Gröbner basis (Zucker, "Gauss and Groebner Egraphs",
  philipzucker.com/linear_grobner_egraph). Today an asserted equation
  is used when it determines an atom (section 4). The design this
  document arrived at, a normal form per class and searchers over it,
  is what Zucker calls e-graphs modulo theories with semantic e-ids
  (arxiv.org/abs/2504.14340, 2025); its vocabulary and its open
  problems are ours.
- **A regression suite nobody passes.** Stoutemyer's 86 products of
  fractional powers of powers (arxiv.org/abs/1203.1350, 2012): five
  systems returned a result not equivalent to the input on 11% and
  failed to recognize a zero on 50%. A sound rule set under a sign
  lattice, with the numeric oracle of section 7, can be measured
  against it. Section 10 item 1, after `:assume`.

What the same pass says about the ground we stand on: the best-known
attempt to put equality saturation inside a CAS, Metatheory.jl in
Symbolics.jl, is not on that system's `simplify` path today (its
`simplify` is rule rewriting over forms canonical by construction,
and the current package lists no Metatheory dependency), so a
simplifier whose default path is saturation over a normal-form
analysis is not something that has shipped elsewhere.

## 9. Open questions

- Name.
- How assumptions should be expressed: the term vocabulary
  (`[:> :x 0]`) or a small predicate language.
- The `:too-big` threshold for the polynomial analysis, and whether the
  normal form is materialized into the e-graph as a node (so it can be
  extracted) always, never, or only at the root.
- Whether `:D` belongs in the term language (differentiation as
  equality) or is a separate operation that calls into the engine.
  Decided (section 3, "Differentiation"): the former; the oracle
  for it is a reference differentiator whose result must land in the
  same class.
- Results that tie can differ as terms. Canonical means the cost
  (section 6), and a tie goes to cromulent's node order, which
  follows the order of insertion: under `powers`
  `[:* :a [:expt :y [:+ :n :m 1]]]` comes back as itself and
  `[:* :a :y [:expt :y [:+ :n :m]]]` as
  `[:* :a [:expt :y [:+ :m :n 1]]]`, and under `exp-log`
  `[:exp [:+ :x 1]]` and `[:* [:exp 1] [:exp :x]]` differ the same
  way. Every system we read orders the arguments of a sum and a
  product, so by section 6's precedence the answer should be one
  term, and the open part is how: a tie broken by a total order on
  the terms the nodes head (`bendix.poly` has one for forms), which
  cromulent's extractor does not see today.

## Appendix: term format trade-offs

Three candidates were weighed before choosing. The core is agnostic
through its term protocol; this is about the CAS's canonical data.

**Tagged vectors** `[:+ [:* 2 :x] :y]`

- Self-evaluating: no quoting anywhere in code, EDN, REPL, or data
  files. Rule right-hand sides that compute a result are plain vector
  literals with ordinary interpolation, no `list`/syntax-quote dance.
- O(1) operator and positional child access; small vectors of
  keywords and integers hash and compare fast and cache their hash on
  the JVM.
- Identical shape to e-nodes (children replaced by ids), so terms and
  e-nodes share every helper.
- Namespaced keyword operators (`:trig/sin`) give rule-set authors a
  collision-free extension space.
- Same shape as catalytic-buffer's ops and tree-evaluation's trees.
- Costs: variables as keywords (`:x`) reads oddly to a Lisp
  mathematician; named constants need a convention (nullary operator
  `[:pi]` rather than a keyword, so it cannot be confused with a
  variable); a vector literal as a leaf must be wrapped.

**S-expressions** `'(+ (* 2 x) y)`

- The Lisp/Emmy/scmutils tradition; `x` reads as x; near-free Emmy
  interop; Clojure `eval` is a cheap evaluation oracle.
- Costs: quoting everywhere, and syntax-quote namespaces symbols
  (`` `(+ x y) `` reads as `(clojure.core/+ user/x user/y)`), a
  perennial gotcha in rule code; lists are not indexed; and
  `(= '(+ 1 2) [:+ 1 2])` is false but `(= '(+ 1 2) ['+ 1 2])` is true
  (sequential equality), so lists and vectors would silently share
  hashcons keys.

**Maps or records** `{:op :+ :args [...]}`

- Explicit and extensible with annotation slots.
- Costs: unbearable to write by hand in rules and at the REPL. Clojure
  metadata on vectors gives the same annotation ability without
  affecting equality, which is exactly right for hashconsing.

**Shared wart.** In every candidate an e-node `[:+ 4 7]` (classes 4
and 7) and a term `[:+ 4 7]` (the integers) look alike. Inside the
e-graph there is no ambiguity, because integer constants are leaf
e-nodes with their own class ids and compound e-node children are
always ids. The confusion is only for humans reading REPL output; the
fix is a printer for classes that renders ids distinctly.

**Patterns are a wash.** `?a` is a symbol in any representation, so a
pattern needs one quote per side (`'[:+ ?a ?b]`) or a `rule` macro
that quotes for you, as Emmy's does. Terms, not patterns, are where
vectors win.

**Decision.** The *data model* is an engineering choice and tagged
vectors win it; decided 2026-09-13. The *surface syntax* people type
is a UX choice and can be several, each a compiler to the canonical
form, none required: an s-expression reader, an infix string parser,
pretty-printers to infix or TeX. The audience being Clojure
programmers, the canonical form *is* the primary syntax.

## 10. Next: milestone 2

Milestone 1 built the ring fragment; the first steps of milestone 2
built normal-form rules, `pythagoras`, the term seam in the rules,
`powers`, `exp-log`, the canonical spelling of forms and
`differentiate` (section "Status" below). Next, in this order:

1. The sign lattice (section 4) and `:assume`, so conditional rules
   fire soundly; `:assuming` in results stops being empty. The
   conditional half of `exp-log` (`exp(log x) = x`,
   `log(ab) = log a + log b`) comes with it, and `log(xⁿ) = n·log x`,
   which is unconditional for odd `n`.
2. `const` for non-ring operators the analysis can evaluate exactly
   (`abs`, integer `gcd`); the polynomial analysis already folds ring
   constants, `exp 0`, `log 1` and a constant to a negative integer
   power.
3. More trig. Parity (`sin(−u) = −sin u`) needs the negated argument
   as a class; double angle and sum formulas need a numeric model
   that carries the half-angle parameter through argument arithmetic
   (section 3). The alternative to measure against: fold the
   Pythagorean identity into the analysis itself, so no node is ever
   added for it and the index does the merging.
4. Rational-function normal forms, or division under a nonzero
   analysis: open. The candidate first step is the division bridge,
   `[:/ ?a ?b] = [:* ?a [:expt ?b -1]]` in `powers`, considered and
   deferred while designing `derivative` (2026-09-13): it makes
   division a spelling of a negative power, so `combine-powers` and
   `d-power` cover quotients and `d-quotient` becomes redundant, at
   the price of extending the section 5 exemption to division
   (`x/x` becomes 1) and of `differentiate` always running `powers`.
   The larger candidate, from the `combine-powers` defect
   (2026-09-20): fold the power law into the analysis, negative and
   symbolic powers as Laurent monomials over atoms `B^S`, so that
   `combine-powers` and its two forms disappear, the index does the
   merging and the spelling of a power is `->term`'s decision. It
   needs negative degrees in `bendix.poly` and an atom for an
   exponent part that has no class. REDUCE is the precedent: its
   canonical form splits a power over a summed exponent so that the
   pieces are independent kernels of its polynomials, and a switch
   (`combineexpt`) combines them again; here the split would live in
   the analysis and the print would be section 6's. The
   compound-base and numeric-base limits of section 3
   (`(x + 1)·(x + 1)ⁿ`, `2·2ⁿ`) belong here too.

## Status

Milestone 1 implemented 2026-09-13, tests green on JVM (Clojure 1.12)
and Jolt v0.8.7 through `clojure -M:test` and `jolt -M:test` /
`jolt test`, cromulent as a `:local/root` dependency:

- `bendix.poly` — sparse multivariate polynomials over ℚ as plain
  maps: arithmetic (promoting to bignums), `expt` by squaring with a
  term-count limit, atom renaming, evaluation, a total order, and
  rendering to canonical n-ary `:+`/`:*`/`:expt` terms.
- `bendix.analysis` — the polynomial analysis of section 4 exactly as
  ../design/ac-problem.md approach C specifies, with the "atoms move"
  hard part resolved (ids canonicalized at every use, recompute in
  the core, a well-founded order on forms); the index from normal form to
  class in the analysis state; `inconsistency`, the dev-mode oracle.
- `bendix.core` — `simplify` and `saturate`: add, run rules under the
  analysis, materialize every class's normal form, extract under
  `default-cost`. No rules ship yet; the analysis alone collects like
  terms, folds constants, cancels, expands when that is smaller and
  keeps the factored form when it is not.
- Tests (23 tests, 106 assertions): polynomial arithmetic is a ring
  homomorphism under evaluation at random rational points, rendered
  terms evaluate to their polynomial, the order is total and
  compares coefficients by size, linear equations in one atom are
  recognized; like terms,
  cancellation, four spellings of a + b + c in one class with only the
  nodes that were written, opaque atoms, atoms moving under a union,
  `:too-big`, `:conflict`, assumptions settling on the smaller form,
  determining equations solved (a = a/2 and a = −a give a = 0, a = 2a + 1
  gives a = −1, x = y + 1 stays an assumption); experiment 3 (the
  oracle names the wrong rule);
  invariants hold with the analysis on random scripts; every
  arrangement of a sum is one class; `simplify` preserves value at
  random rational points, never grows a term, and its cost is a
  fixpoint; the graph behind it is well-formed.
- `bench/` — experiment 2 (table in ../design/ac-problem.md) and
  three simplifier timings, all under 10 ms.

Milestone 2, first step, implemented 2026-09-13, green on both
runtimes the same way:

- `bendix.rules` — `normal-form-rule` and `render` (section 3: a
  polynomial as a pattern over class ids, with placeholders for nodes
  the graph does not hold yet), `pythagoras` and the `trig` rule set,
  and `trig-inconsistency`, the oracle modulo the identity.
  `bendix.poly/reduce-square` is the reduction, and atoms may now be
  anything (a placeholder orders by its printed form).
  `bendix.analysis` exposes `forms` and `threshold`. cromulent gained
  matches that carry their own right-hand side for this.
- `materialize-all` builds one extractor and rebuilds once; it
  rebuilt per class, cubic in the graph, which experiment 4's
  n = 100 row exposed.
- Tests (the suite is 31 tests, 141 assertions): `reduce-square`;
  rendering, with a placeholder; fifteen textbook trig results (the
  pair in two arrangements of a sum, with a cofactor, after like-term
  collection, both directions of `1 − sin²`, the cube, `sin⁴ − cos⁴`,
  arguments merged by the analysis, one pair collapsing beside
  another argument's lone sine, a lone square staying put);
  saturation in three iterations with the oracle quiet; the oracle
  passing an identity and failing an equation outside it; experiment
  4 as a property (the pair anywhere in a sum of up to six atoms
  reaches the sum plus 1 at a linear node count); and the numeric
  oracle on the unit circle over random terms with sines and cosines:
  value preserved, never grows, cost a fixpoint, graph well-formed and
  consistent modulo the identity.
- `bench/` — experiments 4 and 5 (tables and verdict in
  ../design/ac-problem.md): the pair reached inside a sum of 100
  atoms at 327 nodes in three iterations, every workload row reached.

The term seam (2026-09-13, the former item 1 of section 10):
`bendix.term` is the CAS's vocabulary (`variable?`, `constant?`,
`class-id?`, `placeholder?`, `placeholder`, `class-ids`,
`map-class-ids`, `nodes-with`, `node-with`), used by the analysis, the
simplifier and the rules in place of type tests; the rules read nodes
only through `cromulent.term` (which gained `child`); a placeholder is
any node over class ids, nested allowed, rendered by walking it, and
one variable `?<id>` names a class id wherever it occurs.
`bendix.poly` only orders atoms. Tests: the vocabulary, placeholders
with several children, reading a merged class in node order, and a
nested placeholder through `render`.

`powers` (2026-09-13, the former item 1 of section 10):
`combine-powers` is a normal-form rule over monomials. For every
atom of a monomial it asks what power it is (`factor`: a variable or
opaque atom is its own base to the first power; an `[:expt B E]` atom
is `B` to `k + S`, `k` the constant part of `E`'s data and `S` the
class of a non-constant exponent), groups factors by base, and where
a base has two factors, or one power raised to an integer power,
replaces them by one placeholder `[:expt B (k + Σ c·S)]`; a
non-negative integer total is then folded by the analysis and the
class merges through the index. Placeholders gained explicit class
references (`bendix.term/class-ref`) so a constant can sit beside an
id, and cromulent gained `lookup` for the class of a variable leaf.
The domain convention is stated in section 5. Tests: fifteen
textbook results (symbolic, negative, rational and nested exponents,
opaque and compound bases, inside a sum, beside a folded square,
different bases untouched), with the engine as its own oracle where
the spelling of the exponent may vary (`same-class?`); saturation in
three iterations; and the numeric oracle over random terms with
symbolic and negative exponents under `trig` and `powers` together,
where a point outside the input's domain is skipped: value preserved
where defined, never grows, cost a fixpoint, graph well-formed. The
suite is 38 tests, 188 assertions. `bench/`: four powers rows in
experiment 5.

`exp-log`, the unconditional part, with the canonical spelling of
forms and the pluggable join preference (2026-09-13, green on both
runtimes): the design sketch had `exp` of a sum split into a product;
prototyping it found the analysis was not canonical modulo the
graph's own equalities (section 4, "spelled over undefined atoms"),
and the collecting direction is what merges. `bendix.analysis/canonical`
expands defined atoms, opaque and variable, with a cycle guard and
the threshold, and `bendix.poly/substitute` is its arithmetic; `make`
treats every non-ring node as opaque and folds `exp 0`, `log 1`;
`modify` indexes every class, an opaque class under its own atom, so
`sin x · 1` is `sin x` during saturation; the join lets an atom yield
to a form that defines it and not to one that mentions it, and takes
a `:prefer` measure
(`fewest-terms`, `lowest-degree`, `fewest-atoms`, `most-terms`),
plumbed through `simplify`. `combine-exp` is a normal-form rule over
monomials, the mirror image of `combine-powers`: the exponential
factors of a monomial (`factor` finds the base, and the base holds
`[:exp u]`) become one placeholder `[:exp Σ (k + S)·u]`; the analysis
normalizes the argument, the index merges it with any class worth
the same, the hashcons merges the exponential; `log-of-exp` is the
pattern rule `[:log [:exp ?x]] → ?x`; `exp-log` holds both.
`normal-form-rule` now visits an opaque class as its unit polynomial,
so a lone `exp(x)⁻¹` meets `exp(−x)`. Not included: the splitting
direction, and the conditional rules (section 10 item 2). Tests (the
suite is 52 tests, 269 assertions): `substitute` by example and as a
homomorphism; a defined atom and a solved variable spelled by their
forms so two products merge, a class worth one atom being that atom
and its own atom hiding nothing, cyclic assertions finite, `exp 0`
and `log 1` folded, `sin` of a too-big class opaque, `:prefer`
changing the representative and a bad key refused; twenty-six
textbook exp-log results, saturation in at most four iterations, the
two spelling cases (`sin²x·x^(n+m) + cos²x·xⁿ·xᵐ` and its `exp`
twin) and a non-pair left alone; and the numeric oracle in the
formal model (section 7) over random terms with exponentials and
logs under all three rule sets: value preserved where defined, never
grows, cost a fixpoint, graph well-formed. It found three defects on
the way: `exp(2x)·1` raised to −1 did not collect because `exp(2x)·1`
was not the class of `exp(2x)`; `log(exp(1 − x))¹` hid `1 − x` behind
the class's own atom; and the first fix for that let
`sin x · y⁻¹ · y` redefine `sin x` as a product mentioning itself,
which the definition/equation distinction above settles. Known and
older, found by soaking the trig property: `pythagoras` on a high
power of one sine or cosine (`sin³²x`) proposes a rendered form whose
every sub-class gets proposals of its own, and the node limit is hit
before saturation; the result is still right and the property is
rarely reached, but it is a real limit of answer 2 on powers, for the
trig item of section 10. `bench/`:
seven experiment 5 rows and experiment 6 (../design/ac-problem.md).
The spelling machinery costs about 1.3× on the 100-atom rows of
experiments 2 and 4; a benchmark, not a design, decides whether that
is worth chasing.

`differentiate` (2026-09-13, green on both runtimes), as section 3
("Differentiation") designs it: `bendix.poly/derivative`;
`normal-form-rule` over a pattern; `ring-derivative`, `independent`,
`d-sin`, `d-cos`, `d-exp`, `d-log`, `d-quotient`, `d-power` and
`d-power-symbolic` as `bendix.rules/derivative`; `no-D` and
`differentiate` in `bendix.core`; cromulent's extractor ordering
costs with `compare`. Building it changed the design in four places,
each found by a test. `no-D` counts what is under a `:D`, not the
`:D` nodes (section 3). `d-power` fires for any constant exponent
and folds a constant `u'` (section 3). `derivative` is
ring-consistent at saturation and not after every application
(section 3). And three defects in the analysis, none the derivative's
own: the join read the unit polynomial of another class as an atom
that yields to a definition, so `[:D c x]` beside `−(−sin x)` kept
its own name and a root worth `e^y` kept `e^-u · D(e^u)` (section 4,
merge); the built-in order preferred one term over two unknowns to
two terms over none, so a root worth `2x + 2` kept `e^-u · D(e^u)`
and its parents computed with it (section 4, opaque atoms first);
and the index held only the form a class keeps, so two classes
sharing a form whose exponential atom was a fresh placeholder when
its node was created stayed apart (section 4, every form indexed).
The analysis also folds a constant to a negative integer power, so
the reference's `2⁻²` is `1/4`. Tests (the suite is 66 tests, 344
assertions): `derivative` by example and as the properties that
characterize it (linearity, Leibniz, its values on atoms, symmetry of
mixed partials); the textbook table (polynomials, each chain rule, a
quotient, rational, negative and symbolic exponents, `x^x` under
`powers`, nesting, a second derivative and a mixed partial, `π`, an
unknown operator of another variable, a leftover `:D` pushed as far
as the rules go, `f'g + fg'` for unknown `f` and `g`, a `:D` inside
`simplify`); the result shape and the refused variable; saturation
in at most the depth plus two iterations; and the reference
differentiator over random terms with trig and with exponentials:
the result complete and saturated, in the reference's class under
the same rules, equal to it numerically in the models of section 7,
its cost a fixpoint; ring-consistent at saturation, and the
per-application check tripping on exactly the `sin y` transient; the
graph well-formed under every rule set. A soak of a thousand trials
per property on the way found the three analysis defects and a
division by zero the evaluator now reports as undefined; one
non-convergence of the analysis (the round limit, six classes
cycling) was seen once before every form was indexed and not again
in five suite runs and fifteen thousand soak trials after. `bench/`:
a sum of ten sines differentiates in 4 iterations at 100 nodes and
one of a hundred in 4 iterations at 1000 nodes; five nested sines in
7 iterations, twenty in 22, the depth plus two, all under 60 ms on
the JVM. cromulent: 49 tests, 172 assertions, one new for vector
costs.

The join's definitions (2026-09-16, green on both runtimes, Jolt
v0.8.8): the suite on Jolt found `simplify` not a fixpoint twice.
One was the analysis: an atom yielded to a form whose atom was built
from it (section 4, merge), so `eˣ` was spelled as
`exp(eˣ)⁻¹·D(exp(eˣ))` for the rest of the run; `defines?` now
refuses a form with an atom reachable from the defined atom through
the children of opaque nodes, and the derivative term that found it
is a test (the suite is 67 tests, 347 assertions). The other was
`combine-powers` against the size cost, closed below. The
seed of the powers failure reproduces on the JVM at trial 45
(`1789597929120`); the derivative's does not carry across runtimes,
the shrunk term does.

One power per base, and a narrower contract (2026-09-20, green on
both runtimes, Jolt v0.8.10). Tracing the powers failure showed a
canonicity defect, not only a fixpoint one: three spellings of
`a·y^(n+1)` gave costs 6, 7 and 7, because the rule proposed the
combined power alone and under fewest nodes the cheaper `a·y·yⁿ`
existed only when the input or another rule's rendering held it
(section 3, `combine-powers`). Two fixes were built the same day. The
first, a second canonical form (`split-form`, the positive integer
part of an exponent returned to the ring; experiment 7), closed the
defect and printed `y·yⁿ` for `y^(n+1)`. The second replaced it:
section 6 now says how the default's opinions are decided
(soundness, canonicity, the convention of the established systems
for the equivalent request, fewest nodes, and every use of convention
recorded with a survey read from their documentation and source, the
alternatives and a verdict), and its first use decided one power per
base. `default-cost` charges a `:*` node 2 for each base that
appears in more than one of its children, the bases read from the
children's class polynomials (`bendix.rules/power-bases`), so
`combine-powers`' one form is the cheapest spelling under both
shipped costs; the shipped costs are functions of the saturated
e-graph, `:cost` is `(fn [g] cost-fn)`, `bendix.core/size` is the
plain cost they build on and `bendix.core/term-cost` what a term
costs as written; `split-form` is removed. All the spellings of
`a·y^(n+1)` reach 7 and `[:* :a [:expt :y [:+ :n 1]]]`, `y^(n+1)`
comes back as itself, `y·y` is `y²` with or without rules, the
seed's term is a fixpoint at once, and never-grows is restated (a
result may be one node larger for each repeated base it combined;
section 6). The contract narrowed with it: section 6 promises
soundness for any cost, and canonicity, the cost fixpoint and
never-grows for the costs that ship against the rule sets that ship;
the unbuilt cost combinators are struck; `:prefer` is an option of
the analysis and no longer of `simplify` (section 4). Tests (the
suite is 70 tests, 366 assertions): the spellings by example with the
seed's term; canonicity as a property, `b^(s+k)` beside a cofactor
written four ways in a random context reaching one cost;
never-grows as the restated bound for every rule set; `term-cost`;
`the-preference-is-a-measure` no longer goes through `simplify`.
Soaks: two thousand fixpoint trials and a thousand canonicity trials
passed under the charge with one form. `bench/`: experiment 8
replaces experiment 7's rows (../design/ac-problem.md has both), and
experiment 6 builds its own e-graph to reach `:prefer`. Open, found
by experiment 8's soak and older than this work: a power of a sine
written as a product beside `pythagoras` reaches a different cost
from the same power written as a power (section 3, "Limits"); also
recorded there, a numeric base never meets its coefficient
(`2·2ⁿ`), and in section 9, results that tie can differ as terms.
Section 8 lists, with sources, where a system that holds every form
can differ from those that hold one.

Open, found 2026-09-25 by a random seed of the trig derivative
property and reproduced on the engine before and after that day's
cromulent change: the cost fixpoint fails for a derivative whose root
class passes the `:too-big` threshold (section 3, "Limits, named").
The property fails about once in eight runs of 200 trials.

Not yet: everything in section 10, other syntaxes, explanations.

The port to ClojureScript (2026-09-25, for ../orrery): the five
source namespaces renamed to `.cljc`, and `bendix.num` added as the
numeric seam (README, Portability). Everything else compiled
unchanged. The edits were the coefficient sites: `+'`, `*'`, `/`,
`ratio?`, `numerator`, `denominator`, `abs` and `compare` on
coefficients in `bendix.poly`, the two constant folds in
`bendix.analysis`, the exponent sums in `bendix.rules` and
`d-power`'s arithmetic, and `65/64` in `bendix.core/size` written as
a division, the ClojureScript compiler having no ratio constant.
Exponents stay plain integers. Tests: `bendix.num-test` on the JVM
and Jolt, and `bendix.smoke`, twenty-five facts (results, counts,
per-rule counts, costs as doubles, a ratio printed and read back)
asserted by `bendix.smoke-test` here and by orrery's node build and
browser self-test; all of them agree on the three runtimes. The
suite is 75 tests, 419 assertions.

The export (2026-09-26, for ../orrery; 76 tests, 428 assertions):
`bendix.core/class-data`, the class as the polynomial analysis sees
it for `cromulent.export`, its kind as the `type` (polynomial, atom,
too-big, conflict) and a polynomial's normal form as a term in the
native spelling with an opaque class written `#id`; and
`bendix.core/serialize`, the egraph-serialize data of a graph with
that class data and every node costed under `default-cost`.

The coefficient seam (2026-10-01, section 4, "Coefficient
algebras"): `bendix.algebra` (`Coefficients`, `rational`); every
coefficient site in `bendix.poly` and `bendix.analysis` goes through
it. No behaviour changed: the suite (77 tests, 430
assertions) passes on the JVM and Jolt, the bench gives identical
results on both (JVM 2802 ms before and 2807 ms after over every row,
Jolt 4501 ms and 4615 ms), and `bendix.smoke`'s 25 facts hold in
ClojureScript on Node.
