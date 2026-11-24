# Notes on the Bachmann development

Two design questions about `BachmannDefs.v` and `BachmannNormal.v`.

## 1. Why a type of large ordinals is not enough

One could try to use `Ord` at a higher universe, with nodes `ord A f`
where `A` may be a large type such as `Ord` itself. That type can
describe Ω, Ω+1, Ω^Ω and ε_{Ω+1} as order types. Bachmann's φ needs
two things it cannot express.

**The construction applies a branching to the values it computes.**
At a node of cofinality Ω, Bachmann's φ takes the least z with
φ_{α[z]}(0) ≤ z. Here z is a value of the hierarchy, a small ordinal,
and it is fed back in as the argument of the fundamental sequence.
This is the collapsing step.

That only typechecks if the branching type is literally the type of
values. Given a generic large node `ord A f`, `f z` makes sense for
`z : Ord` only if `A` is `Ord`, and type theory cannot test for that.
So `BOrd` records the distinction in its single constructor:

- small children `g : A → BOrd`, which get the Veblen-style
  "fix each child" treatment;
- Ω-families `h : C → Ord → BOrd`, branching over exactly the value
  type, which get diagonalized.

A large-ordinal type erases which branchings are over `Ord`, together
with the map needed to evaluate them.

**Regularity of Ω comes from the typing.** In set theory Ω must be
regular, so that the fixpoint z lands below Ω and α[z] makes sense.
Here z has type `Ord`, so `h z` is always well-typed. This is why Ω is
the type `Ord` and not `Countable.v`'s Ω, whose regularity would need
choice.

**φ depends on the tree, not just its order type.** φ is not monotone
in the order-type comparison `ble`, only in the structural order
`bsub`. Two trees with the same order type but different fundamental
sequences can give different values, so identifying them loses
information φ needs.

This also explains why the method stops at the Bachmann–Howard
ordinal. There is one level of value-typed branching. Going further
(Ω₂, …) would need trees whose families branch over `BOrd` itself,
the step toward Buchholz-style systems.

## 2. Completeness and goodness

A tree is good (`bgood`) when it is complete in the sense of
`Operators.v`, lifted from ordinals to index trees, with directedness
handled separately.

| `complete` (on `Ord`) | `bgood` (on `BOrd`) |
|---|---|
| decides `inhabited A ∨ ¬inhabited A` | decides whether the node has any components (`bdec`) |
| hereditary over all children | hereditary over small children, and over family members at complete arguments |
| children directed | not required for `bphi`; needed separately (`bsdirH`) for `bach` to agree with `bphi` |
| — | each Ω-family's diagonal ξ ↦ φ_{h ξ}(0) is normal |
| — | family members at positive arguments have a component |

**Same purpose, same decision.** The inhabitation decision in
`complete` exists to get strict monotonicity, by telling zero apart
from a positive ordinal. The decision in `bgood` does the same job:
a node with no components gives f, a node with components gives a
fixpoint enumeration. The shifted hierarchy (removed in d13521a)
avoided the decision only by always including f among the components,
at the cost of computing φ_{1+T} instead of φ_T.

**Directedness moves elsewhere.** For ordinals, directed children make
a sup behave like a limit. For `bphi`, the enumerator `cfe` builds
directedness in: any two compositions of components are dominated by
their concatenation. So goodness does not need it. Bachmann's φ takes
fixpoints one component at a time, and that agrees with taking them
jointly only when the components are directed under domination. That
is the separate `bsdirH` condition.

**Normal families are completeness for a branching over `Ord`.** A
complete node needs its children to cohere: directed, with every child
complete. An Ω-node branches over a type with its own order, so
coherence means the family respects that order. The family must be
monotone, strictly increasing, and continuous at limits
(h(sup) ⊑ ⨆ h). These are exactly the conditions that make the
diagonal normal. The "component at positive arguments" clause plays
the role of the nonzero field of a normal function.

**Everything happens at complete arguments.** Goodness of family
members is required only at complete ξ. That suffices because normal
functions take complete inputs to complete outputs, and the fixpoints
fed back into families are values. Completeness of values and goodness
of trees sustain each other in one loop:

- good trees give normal φ;
- normal φ produces complete values;
- families are only ever evaluated at complete values.

**A structural sufficient condition.** `bcd` (= `bcanon ∧ bdec`)
guarantees goodness from the shape of the tree alone: canonical
structure plus the decisions. It plays for `BOrd` the role
completeness plays for `Ord`, and it is what the tree arithmetic
(addition, multiplication, exponentiation, the tower, ε_{Ω+1})
preserves.
