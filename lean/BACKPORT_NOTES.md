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
