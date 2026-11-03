# Proof simplifications found during the Lean port

These are places where the Lean proof turned out noticeably shorter or more
direct than the Rocq original, using only lemmas that also exist in Rocq. They
may be worth backporting.

None of them has been tried in Rocq yet. Each entry names the Rocq lemma, the
idea, and the Lean proof to look at. Lean names are in
`ConstructiveOrdinals.Ordinal` unless noted otherwise.

## Fixpoints.v

### `KnuthUp_epsilon` (about 45 lines → about 10)
Lean: `knuthUp_epsilon`.

- **`≤`:** apply `foldOrd_least` with the *constant* function `q := fun _ => ε 0`.
  - `hz` is `1 ≤ ε 0`, from `ε_fixpoint` and `expOrd_nonzero`.
  - `hsq` is `expOrd ω (ε 0) ≤ ε 0`, from `ε_fixpoint`.

  This needs no induction over the indices of `ω`.
- **`≥`:** unfold `ε 0` to `fixOrd powOmega _` and apply `fixOrd_least`. The
  prefixpoint condition `expOrd ω K ≤ K` is exactly
  `KnuthUp_omega_fix 1 ω`, because `KnuthUp 1 = expOrd`.

### `ε0_least_expOmega_closed`
Lean: same name.

This is one application of `fixOrd_least`, after unfolding `ε 0` to
`fixOrd powOmega _`. The manual induction over `iter_f` isn't needed.

## Arith.v

### `KnuthUp_one_eq`
Lean: `knuthUp_one_eq`.

For the `S n` case there's no need to `destruct n` again or use
`lub_continuous`. Write `s := KnuthUp n a`; then:
- `foldOrd 1 s 1 ≤ a`: the `sup` part is `s (foldOrd 1 s 0) ≤ s 1 ≈ a`, using
  `foldOrd_zero`, monotonicity and the induction hypothesis.
- `a ≤ foldOrd 1 s 1`: `a ≈ s 1 ≤ s (foldOrd 1 s 0) ≤ foldOrd 1 s 1`, using
  `foldOrd_unfold_le`.

### `mulOrd_monotone2`
Lean: `mul_le_mul_left`.

Don't destruct `x`. After `sup_least`, `le_subord` gives `q` with `g b ≤ z q`,
and the goal is `addOrd_monotone` (with the induction hypothesis) followed by
`sup_le` at `q` of `mulOrd_unfold x z`.

### `ordDistrib_left`, second direction
Lean: `mul_add`.

The `sup` index of `a * c` is a pair `(i, k)`, with
`k : ordCarrier (a * h i + a)`. Then the chain is:

```
a*b + (a*h i + a) k < a*b + (a*h i + a)       (addOrd_increasing, index_lt)
                   ≈ a*b + a*h i + a          (addOrd_assoc)
                   ≤ a*(b + h i) + a          (IH)
                   ≈ a * succ (b + h i)       (mulOrd_succ)
                   ≤ a * (b + c)              (mulOrd_monotone2, foldOrd_unfold_le)
```

This avoids rewriting with `sup_unfold` and reasoning about `supOrd _`
explicitly.

### `mulOrd_assoc`, `≥` direction
Lean: `mul_assoc`.

```
a*b*h x + a*b ≈ a*(b*h x) + a*b    (IH)
              ≈ a*(b*h x + b)      (ordDistrib_left)
              ≤ a*(b*c)            (mulOrd_monotone2, sup_le)
```

There's no need to unfold `mulOrd` at `a * supOrd _`.

## Operators.v

### `lub_complete1` and `lub_complete2`
Lean: same names, with the private helpers `lub_left_bound` and `lub_right_bound`.

First prove that, when `y ≤ x`, every index of `x ⊔ y` is bounded by an index
of `x`:
`forall a, exists a0, (x ⊔ y) a ≤ x a0`. For `inr`, this is `ord_le_subord`.

Directedness then takes one application of `x`'s directedness. The
decidable-inhabitation part takes one line. This replaces the four nested
`inl`/`inr` case splits. `lub_complete2` is symmetric.

## Cantor.v

### `expNatToOmega`, `≥` direction
Lean: `expNatToOmega`.

`ω ≤ expOrd n ω` is just
`increasing_inflationary (expOrd_increasing n Hn) ω`. The induction on `i`
isn't needed.

### `additively_closed_mul_omega`
Lean: same name.

No induction on `j` is needed. With `a < x * i + x` and `b < x * j + x`:

```
a + b < a + (x*j + x)
      ≤ (x*i + x) + (x*j + x)
      ≈ x * (S i) + x * (S j)           (mulOrd_succ)
      ≈ x * ((S i) + (S j))             (ordDistrib_left)
      ≈ x * natOrdSize (S j + S i)      (natOrdSize_add)
      ≤ x * ω
```

### `mul_omega_collapse`
Lean: same name.

No induction on `m` is needed. Let `N := 1 + n`, so that `a + b ≤ a * N`:

```
(a+b)*m + (a+b) ≤ (a*N)*m + a*N
                ≈ a*(N*m + N)                  (mulOrd_assoc, ordDistrib_left)
                ≈ a * natOrdSize (N + m*N)     (natOrdSize_mul, natOrdSize_add)
                ≤ a * ω
```

### `expToOmega_collapse`
Lean: same name.

The core fact is `forall i, (a+b)^i ≤ a^(2*i)`, by a plain induction on `i`
using `expOrd_succ`, `a+b ≤ a*a` and `mulOrd_assoc`. Each summand
`(a+b)^i * (a+b) ≈ (a+b)^(S i)` is then bounded by `a^(2*(S i)) ≤ a^ω`. This
replaces the index bookkeeping with `S (i*2)`.

### `cantor_decomposition_unique`
Lean: same name, with the private helper `cantorDenote_lt`.

The two symmetric contradiction branches each contain an identical inner
induction. Factor it out as one lemma:

```
cantor_sequence o ys -> o < a -> cantor_denote ys < expOrd ω a
```

Inside the main proof, a single local `contra` lemma then covers both
branches.

### `cantor_decomposition_is_classical_for_complete_ordinals`
Lean: same name, with the private helper `cantorDenote_lt_omega`.

Similarly, factor out:

```
cantor_sequence o ls -> o ≤ 0 -> cantor_denote ls < ω
```

In the `0 < o` branch, `ω ≤ expOrd ω o` (a small helper, `omega_le_pow_omega`)
replaces the chain of rewrites through `expOrd_unfold`, `sup_le` and
`zero_least`.

### `truth_ord'_expOmega`, `≥` direction
Lean: `truthOrd'_powOmega`.

Each summand `expOrd ω 0 * ω ≤ 1 * ω ≈ ω`, and for `H : P`,
`ω ≈ truth_ord' P` by `truth_ord'_true`. This avoids rebuilding the witness
by hand.

### Small shared helpers
Several proofs in `Cantor.v` re-derive the same two facts inline. They could
become lemmas:

- `0 < c -> ω ≤ expOrd ω c`
- `expOrd ω (c i) * ω ≤ expOrd ω c`

## VeblenCon.v

### `veblen_fixpoints_aux` (about 180 lines → about 50)
Lean: same name.

Prove it by well-founded induction on `α`, inside the given `β`.
- The `f` part of `veblen f α (veblen f β x)` is unchanged.
- In the `sup` part, apply `fixOrd_least` to `veblen f (α y)`. Its
  prefixpoint condition `veblen f (α y) (veblen f β x) ≤ veblen f β x` is
  exactly the induction hypothesis for `α y < α`.

This leaves only the base case,
`lim (fun z => veblen f α (veblen f β x z)) ≤ veblen f β x`. That follows from
`veblen_lt_lemma` plus one use of directedness, as in the original.

The original proves the `sup` part by induction on the iteration count, with
two nested Scott-continuity arguments, over `β` and over `nat`. None of that is
needed.

### Repeated completeness side conditions
Two facts are rebuilt inline about ten times. Each could be a lemma:

- `complete β -> complete x -> complete (limOrd (fun i => veblen f β (x i)))`
  (Lean: `lim_veblen_complete`)
- `complete x -> complete (ord x (fun b => enum_fixpoints f (x b)))`
  (Lean: `enumFixpoints_base_complete`)

The proofs of `veblen_continuous`, `enum_fixpoints_cont`,
`enum_fixpoints_func_mono` and others then become short. Similarly, a helper
`veblen_normal_of_cont`, stating that `veblen f β` is normal once it is
continuous, replaces the inline `constructor` blocks in `veblen_fixpoints_aux`
and `veblen_continuous`.

### `veblen_limit_zero`, `veblen_limit_succ`, `veblen_limit_limit`
Lean: same names.

In each, the bound on `fixOrd (veblen f (g b)) base` is a single
`fixOrd_least`, with prefixpoint `veblen_fixpoints (g b) (g b')`. A shared
helper (Lean: `fixOrd_le_veblen_of_lt`) replaces the inductions on `i`.

## VeblenClassical.v

### `veblen_fixpoints_aux`
Lean: same name.

The same induction-on-`α` restructuring applies.

### `veblen_unroll_nonzero`
Lean: same name.

`f y ≤ fixOrd (veblen f (g b)) L` holds directly:

```
f y ≤ f L ≤ veblen f (g b) L ≤ fixOrd …    (the last step is iteration 1)
```

This avoids going through `fixOrd_fixpoint` and `fixOrd_monotone_func`.

## VeblenFacts.v

### `veblen_onePlus`, `≥` direction
Lean: same name.

The core fact is `forall n, ω^(f i) * n ≤ iter_f (veblen (addOrd 1) (f i)) L n`,
by induction on `n` using the outer induction hypothesis together with
`b*n + b ≤ b + b*n` for finite `n`. That last fact is one `calc`:

```
b*n + b ≈ b*(n+1) ≤ b*(1+n) ≈ b*1 + b*n ≈ b + b*n
```

This replaces the nested induction and its `clear`.

### `veblen_enum_fixpoints`
Lean: same name.

The `≥` direction's first component, `enum_fixpoints f x ≤ veblen f (1+a) x`,
can be a local `have` proved by its own induction on `x`, without `clear`-ing
the outer induction hypotheses.

## NaturalArith.v

### A probable bug: `nmulOrd_eq_mor`
`nmulOrd_eq_mor` is declared with `Add Parametric Morphism : naddOrd …`, so it
states the congruence of `⊕` (natural addition), not `⊗` (natural
multiplication). It looks like a copy-paste slip. The Lean port keeps the
statement as written (Lean: `IncorrectNmul.nmul_eq_mor`).

### `naddOrd_increasing_both`
Lean: `nadd_increasing_both`.

This follows directly from `naddOrd_monotone` plus the two "index" facts
`x a ⊕ y < x ⊕ y` and `x ⊕ y b < x ⊕ y`. For example, if `x < y` there is
some `b` with `x ≤ y b`, and then

```
x ⊕ z1 ≤ y b ⊕ z2 < y ⊕ z2
```

No triple induction is needed. Proving `naddOrd_monotone` first, before
associativity, also simplifies `naddOrd_assoc1`.

### `naddOrd_assoc2`
Lean: `nadd_assoc2`.

This follows from `naddOrd_assoc1` and `naddOrd_comm_le`, used five times in
a chain:

```
(x⊕y)⊕z ≤ z⊕(x⊕y) ≤ (z⊕x)⊕y ≤ y⊕(z⊕x) ≤ (y⊕z)⊕x ≤ x⊕(y⊕z)
```

No second induction is needed.

### `naddOrd_cancel`
Lean: `nadd_cancel`.

Using the case split "`q < x ⊕ y` implies `q ≤ x a ⊕ y` or `q ≤ x ⊕ y b`"
(Lean: `nadd_lt_cases`) as a lemma makes this and several later proofs
shorter.

### `nadd_add_same_powers_step` (about 90 lines → about 10)
Lean: same name.

This is one application of `nadd_closed_technical2`, with `m := S m` and
`q := expOrd ω a * S n` (whose hypothesis holds by reflexivity):

```
expOrd ω a * S m ⊕ expOrd ω a * S n
  ≤ expOrd ω a * S m + expOrd ω a * S n
  ≈ expOrd ω a * (S m + S n)               (ordDistrib_left)
  ≈ expOrd ω a * natOrdSize (m + n + 2)    (natOrdSize_add)
```

The double induction is not needed.

### `nadd_closed_technical2`
Lean: same name.

Induction on `m` (and `q`) is enough. The induction on `n` is never used.

### `cantor_denote_nadd_add`
Lean: same name.

Ordinary induction on `xs` from the left works, so `rev_ind` isn't needed.
Rewrite `(ω^x + D xs) ⊕ q` with `add_nadd_assoc2`, whose side condition is
`ω^x ⊕ q0 ≤ ω^x + q0` for `q0 ≤ q`, then apply the induction hypothesis.
(`cantor_denote_nadd_eq` does still need `rev_ind`.)

### `leading_cantor_term`
Lean: same name.

The case `o < a` follows at once from `expOmega_additively_closed` and the
`Cantor.v` lemma bounding `cantor_denote ys` by `expOrd ω a`. That lemma is
inlined twice in `cantor_decomposition_unique`; see the `Cantor.v` notes. This
avoids the explicit computation with `length ls`.

## WellFounded.v

### `wf_lex_exp` and `wf_list_ext` are free

The Rocq proofs import well-foundedness of lexicographic exponentiation and of
list extension from the standard library, then compute their order types.
Both facts follow in one line from lemmas `WellFounded.v` proves anyway:
`list_interp` strictly decreases along `lex_exp` (`lex_exp_lt_interp`), and
`list_ext_interp` strictly decreases along `list_ext`. So each relation is
included in an inverse image of the ordinal `<`. That gives a self-contained
proof that does not use the standard library's long `Desc` combinatorics.

### `Desc_frontways`

Lean: same name.

This is just the equivalence between back-to-front and front-to-back `Desc`
(`desc_iff` in `Prelude/Relations.lean`), unfolded one step. With that
lemma available, the 40-line `rev` induction in Rocq is not needed.

## GoodsteinSequences.v

### `lt_equiv` (about 250 lines → about 50)

Only one direction needs an induction: if `hbn_lt a b` holds for proper
terms, then `interp a < interp b`. It follows by structural induction on `a`,
proved together with the bound

    hbn_proper (HBN_Term e n x) -> interp x < base ^ interp e

(equivalently, `hbn_smaller_exp e x -> interp x < base ^ interp e`). That
bound in turn needs only soundness on the subterms of `x`. The converse
directions of both `hbn_lt_equiv` and `hbn_smaller_exp_equiv` then follow from
`hbn_lt_total` and irreflexivity, with no size measure and no `sz` parameter.
`lt_equiv` itself is kept, with the same statement, as a corollary.

### `hbn_dec_correct`, `→` directions

These go by mutual induction on the `hbn_dec`/`hbn_exp_dec` derivations, with
properness of both sides as premises. Only the `←` directions need the strong
induction on `interp x`.

### `hbn_dec_shadow_dec`

This is also a mutual induction on derivations, using the `→` directions of
`hbn_dec_correct` for the properness side conditions. No well-founded
induction on the interpretation is needed.

## SchutteColumn.v

### `schutte_column_fixpoint'`

Both cases of the `schutte_column_ltE` split on `q < schutte_column f β α x`
end with the same argument: choose indices `bf`, `af` above everything in
sight with `q < fixOrd (...) bf af`, then apply `Hindβ3`. Proving that once,
as a lemma that takes `q < Φ b a` and returns such `bf`, `af`, removes about
half of the second bullet. In the second case Rocq destructs `q < Φ` into an
element `q'` and uses `q'` in `Hindβ3`. Using `q` itself works too, because
`q < Φ b' a' ≤ Φ bf af`.

The first case (`q < f (α + x)`) can likewise be reduced to the second, by a
lemma showing that anything below `f (α + x)` is below some `Φ b a`. The same
lemma serves the `j = 0` step of the first bullet. That step is also simpler
as `fixOrd_least` (base below and prefixpoint) than as an induction on the
iteration count.

### `veblen_gt0_column_complete`

The bound `1 ≤ fixOrd ...` follows from `succ_least` and nonzero-ness. The
Rocq proof unrolls `schutte_column` twice and goes through `1 + 0` and
`onePlus_least_normal`.

## SchutteColumnFacts.v

### `proper_fix_cases`

When the induction hypothesis returns the second disjunct with `b' < b`, the
case `b ≤ 0` is immediately contradictory (`b' < b ≤ 0`). The Rocq proof
destructs `m` and handles four impossible subcases.

### `schutte_matrix_lt2_aux` and `matrix_matrix_fixpoint`

Both repeatedly show `schutte_matrix f m x ≈ schutte_matrix f n x` when the
matrices differ only by a zero argument in the first column, or by equivalent
first columns. Two small lemmas, one for each situation, replace six copies of
the same pair of `schutte_matrix_monotone_func` calls.


## Notation/CantorNotation.v

### Shared "push" step in `normalize` and `cantorSum_add`

Both functions end with the same inline step: put `ω ^ x` in front of an
already-normal sum, dropping it if it is smaller than the leading term. Making
it a function `push x r`, with two lemmas (`push` preserves normality and
denotes `ω ^ x + r`), shortens `normalize_is_normal`, `normalize_is_equal`,
`cantorSum_add_normal` and `cantorSum_add_correct` to a few lines each. It
also removes the copies of the inner `fix` that the Rocq proofs paste into
`case_eq` and `destruct`.

### `CF_denote_shrink`

`ω ^ x + s < ω ^ (ω ^ x + s)` follows from additive closure of
`ω ^ (ω ^ x + s)`: `ω ^ x < ω ^ (ω ^ x + s)` by the induction hypothesis on
`x`, and `s < ω ^ s ≤ ω ^ (ω ^ x + s)` by the hypothesis on the tail. The Rocq
proof goes through `expOrd_add`, multiplication by `1` and
`mulOrd_monotone1/2`.

### `CNF_has_enough_notations`

To show `a < x` for the leading exponent `a` of `x`'s decomposition, the Rocq
proof derives `ε 0 ≤ x` from `x ≤ a` by induction on the iterates of
`fixOrd powOmega`. It is shorter to note that `x ≤ a` gives
`ω ^ x ≤ ω ^ a ≤ x`, and to apply `ε0_least_expOmega_closed`.

### `CF_discriminate`

Recursing on the list of terms (with patterns `[]`, `[c]` and `c :: b :: l`)
avoids `size_induction`, `CF_subterm_tail`, and the argument that a zero tail
must be `nil`.

### Structural mutual recursion instead of `size_induction`

Most lemmas about Cantor forms (`CF_below_epsilon`, `CNF_compare_correct`,
`CF_normal_forms_unique`, `normalize_is_*`) go through with plain structural
recursion over the nested inductive: one lemma for forms and one for lists of
forms. In Rocq this corresponds to a nested `fix` in the proof term, avoiding
the `◃` side conditions that `size_induction` generates.

## Notation/CantorDecomposition.v

### `has_interpolants_rec_eq_mor`

No ordinal induction is needed. Only the top level of `has_interpolants_rec`
mentions `x`; each witness `z` and its interpolant proof can be reused as is,
moving the recursive part to a different accessibility proof with
`has_interpolants_rec_H_irrelevant`. (In Lean the two accessibility proofs are
definitionally equal, so the witness is reused unchanged.)

### `fix_has_interpolants`

`fixOrd g b` is a `supOrd` of iterates, so this is `has_interpolants_sup`
applied to `iter_has_interpolants`. The Rocq proof unfolds the supremum by
hand.

### One reflection lemma for `cantor_add`, `cantor_mul` and `cantor_exp`

The three `*_reflects` proofs are the same argument: decompose both
arguments, apply the list operation, recompose. One lemma, parameterised by
the list operation, its congruence and its two correctness facts, covers all
three.

### `cantor_exp_single_prop_ordered` and `cantor_exp_single_correct`

Both follow the same seven-way case split. Proving them together in one lemma
(well-formedness, ordering and value) removes the duplicated case analysis and
the repeated `cantor_recompose_correct` calls.

### `cantor_add_ordered`

Generalising the loop invariant to "the head of `cantor_add_loop xs y ys` is
bounded by any common bound of `y` and the head of `xs`" turns the proof into
a short induction. It avoids the `case_eq` and `inversion` on the loop result.
The same strengthening (a head bound as a fourth conjunct) makes
`cantor_nadd_list_correct` a short induction.

### `nadd_add_same_powers_step`

The two halves of the `naddOrd_least3` split are symmetric. The interesting
case of each (below `ω^a * m + t` with `t < ω^a`) can be one auxiliary lemma,
applied once directly and once after `naddOrd_comm`. The case "below
`ω^a * m`" is the induction hypothesis in both halves.

## Notation/VNotation.v

### `VF_has_enough_notations'`

The statement is `VF_has_enough_notations` with `≈` reversed, so it follows
from that theorem by symmetry. The Rocq proof instead repeats the work through
`ordinal_discriminate` and `veblen_decompose`. That proof is a useful
illustration and could be kept, but it is not needed.

### `VF_has_all_interpolants`

Structural induction on the form suffices; `size_induction` with
`VF_denote_shrink1`/`VF_denote_shrink2` is not needed.

### `VF_compare_correct`

All six cases follow the same pattern. When the first arguments compare `LT`
or `GT`, the result follows from `veblen_fixpoints` together with
`veblen_increasing` or `veblen_inflationary`; when they are `EQ`, from
monotonicity in each argument. The `change` that restates the goal in the
`GT` case is not needed when the inner `fix` is a separate function.

## Notation/VWNotation.v

### `VW_has_enough_notations'`

Its statement is identical to `VW_has_enough_notations` (both conclude
`exists v:VF, v ≈ x`), so it can be proved by that lemma. Perhaps the prime
was meant to reverse `≈`, as in `VNotation.v`.

### `W_epsilon`

Both cases reduce to the remark that `veblen ε x y ≈ ε s` for some `s`
(`s = y` when `x ≈ 0`, and `s = veblen ε x y` otherwise, by
`veblen_fixpoints` at `0`). Then `ε_fixpoint` finishes. Proving `W_epsilon`
first also shortens `VW_collapse` and `VW_collapse2`, which re-derive it
inline through `enum_are_fixpoints`.

### `VF_normal_forms_unique`

The `V`/`V` and `W`/`W` cases are the same argument for the two normal
functions, `1 + ·` and `ε`. One lemma, generic in the normal function, covers
both. The mixed cases share another lemma: a normal `V` form never equals a `W`
form.

## Notation/ATowerFinNotation.v

### The repeated "tower fixpoint" argument

The Rocq file repeats one argument a dozen times, in `Vmn_collapse`,
`Vmn_collapse2`, `normal_subterm_shrink`, `VF_compare_correct` and
`veblen_tower_epsilon`. It shows `veblen (T m) (veblen (T n) b c) 0 ≤ veblen (T n) b c`
for `m < n` by a case split on `VF_isZero b`, `veblen_zero`,
`veblen_fixpoints` and `ackermann_tower_fin_fixpoints`.

It is cleaner as two lemmas:

- every value `veblen (T n) x y` equals `T n s` for some complete `s` (`s = y`
  when `x ≈ 0`, otherwise `s` is the value itself, by `veblen_fixpoints` at
  `0`);
- the statement follows from that and `ackermann_tower_fin_fixpoints`.

`veblen_tower_epsilon` is then the instance `m = 0`.

### `nat_compare` in `VF_isNormal`

The proofs repeatedly destruct `nat_compare m n` inside the normality
condition. One lemma, stating the condition on `V n x y` as "if `m < n` then
`V n x y ≤ a`, and if `m = n` then `x ≤ a`", lets the rest of the file avoid
`nat_compare` entirely.

### `VF_has_all_interpolants`

The interpolation property of the tower levels (`T n` preserves interpolants)
is a separate induction on `n`. It does not need the outer `size_induction` on
forms. The outer induction is then structural.

## Notation/ATowerNotation.v

The notes for `ATowerFinNotation.v` apply here too. In particular, one lemma
proves that every value of `veblen (T n)` is a fixpoint of the lower levels,
and one lemma rephrases `NormalTail` without `VF_compare`. Two further points:

- In `ackermann_tower_has_interpolants`, the witness `Vnorm (VF_normalize n) Z z'`
  can be `Vnorm n Z z'`, because `n` is already normal. That removes the
  `VF_normalize_equal` steps.
- In `VF_onePlus_equal`, the case `V (V k l o) a x'` needs no split on
  `VF_isZero a`. The value is a fixpoint of `veblen (T 0) · 0` because
  `0 < V k l o`, so
  `1 + v ≤ 1 + veblen (T 0) v 0 ≈ veblen (T 0) v 0 ≤ v`
  by `onePlus_veblen`.

## Notation/SchutteStack.v

### Size bounds in `check_lt` and `sparse_compare`

The Rocq comparison threads explicit size budgets
(`sparse_term_size xs + VF_termSize ytop < n`, …) through `check_lt` and
`sparse_compare`. Each recursive call then needs its own `lia` obligation.

A simpler invariant suffices: every entry of a stack is smaller than the stack
itself (`termSize a < termSize (N l)` for `a ∈ l`). The correctness lemmas then
take only "the comparison function is correct on these pairs" as hypotheses.
Separating the computation (plain functions over fuel) from the correctness
proof also lets comparison compute by `reflexivity` without the
`Acc_intro_generator` machinery.

### `VF_has_enough_notations'`-style duplication

`VF_decompose_correct` and `VF_recompose_correct` repeat the same
`schutte_column0`, `schutte_column_veblen` and `veblen_onePlus` rewrites many
times. Two lemmas, `N [x] ≈ 1 + x` and `N [x, y] ≈ ω^x + y`, shorten both
proofs considerably. A third, `N [a, Z, c] ≈ schutte_column (addOrd 1) 2 a c`,
does the same for the ε, Γ and Ackermann reflection theorems.

### `schutte_column_sparse_matrix_interpolants`

The fixpoint iterates in both halves are handled by one pattern: the
induction hypothesis for column `n - 1`, applied to the matrix extended by
`(n, aq)`. Stating once that the extended matrix's function is pointwise equal
to `schutte_column f n aq` removes four copies of the
`schutte_column_monotone_func` bookkeeping.
