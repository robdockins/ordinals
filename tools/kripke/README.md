# Kripke search for the natural product

These scripts search for constructive counterexamples to laws of the
natural product and natural sum (`Ordinal/NaturalProduct.v`,
`Ordinal/NaturalArith.v`). They work in a two-world Kripke model: at w0 a
proposition P is undecided, and at w1 it holds.

An ordinal of the model is a tree with two parts:
- the children that exist at w0;
- a classical value `T` below ω^ω, which is the ordinal at w1.

The question "is `L ≤ R` forced at w0?" is a game. Every w0 move in `L`
must be answered by a w0 move in `R`, and every position reached must
satisfy the inequality at w1. An instance that is *not forced* is a
candidate witness that the law is not constructive. Such a witness then
has to be turned into a Rocq proof of a reverse result.

Requires Python 3, with no other dependencies. Run the scripts from this
directory.

## Models

| file | model | exact? |
|---|---|---|
| `search.py` | pairs (value at w0, value at w1) | exact, but too weak: every move is a standard ordinal |
| `nested.py` | finitely branching trees | exact |
| `limits.py` | trees whose children may be increasing sequences | heuristic (see its docstring and the caveats below) |
| `transfinite.py` | `limits.py` with regions of transfinite height, and Kripke ω^, +, ⊕ | heuristic |

`ordinals.py` implements Cantor normal forms below ω^ω, with natural
sum, natural product and fundamental sequences. `test_ordinals.py`
checks it; it is slow. `staircase.py` gives the classical rank of a
staircase region in closed form, which `transfinite.py` uses at w1.

## Reproducing the formalized results

Each search below found, or checked, a witness that was then proved in
Rocq. The times are for a laptop.

| Rocq result | command | what to look for |
|---|---|---|
| `row_lower_EM` (`NaturalProduct.v`) | `python3 calibrate.py` | in the pairs model: the `row_lower_EM` instance is not forced, but is forced once P is decided |
| | `python3 nested_runs.py` | first calibration line: `row_lower_EM instance forced: False` |
| `succ_lower_WEM` (`NaturalProduct.v`), and its corollary `distrib_lower_WEM` | `python3 nested_runs.py` (under a second) | "random nested Kripke widths": the successor law fails only for non-directed widths (`succ-dir` and `[S]-dir` report 0 not forced) |
| | `python3 minimal.py` | the smallest failing widths, all non-directed |
| | `python3 refute.py` | the formalized witness `a`, `forced: False`, and the opponent's refutation as a tree |
| `succ_lower_complete_WEM` (`NaturalProduct.v`), and its corollary `distrib_lower_complete_WEM` | `python3 run_h.py 1` (about 2 minutes) | after the calibration, the successor law is `[False]` for each of the limits of directed ordinals A–G in `limwidths.py` |
| | `python3 complete_witness.py` | the formalized witness (c_n has the child n and the value ω+1 at w1; a is their limit): `forced: False (expect False)` |
| | `python3 explain_lim.py A 3` | the opponent's refutation for width A, to depth 3 |
| `nadd_complete_WEM`, `tree_selection_complete_WEM` (`NaturalArith.v`) | `python3 nadd_complete.py 1` (under a second) | complete `u`, `v` whose natural sum is incomplete; the formalized pattern is u = ⟨0\|4⟩, v = ⟨1\|ω⟩ |

`run_h.py` also accepts larger heights (`run_h.py 1 2`).
`nested_runs.py` and `run_h.py` start by checking known results:
standard instances must be forced, and the `succ_lower_WEM` witness must
not be. The transfinite scripts run the same checks with
`python3 transfinite_runs.py cal`.

## Searches that found no counterexample

These are recorded so that the negative and inconclusive results can be
checked.

- `directed_strategies.py`, `tiebreak.py`: finite trees with directed
  children. Every instance is forced, and a fixed "top" strategy wins.
- `pdep_widths.py`: the successor law at widths whose value depends on
  P only through an exponent (ω^c with c = 1, or 2 if P, and ω^c + 1,
  ω^c · 2). These are the Kripke analogue of a notation system with a
  P-dependent atom. Every instance checked is forced.
- `sens.py [instance numbers]`: the transfinite-height instances of the
  exponent law, the successor law and superdistributivity, at ω^xP
  (xP = 1, or 2 if P) and ω^cP (cP = xP + 1, whose children have
  P-dependent values). `transfinite_runs.py [cal|pdep|danger]` runs the
  same instances in groups.
- `nadd_power.py [instance numbers]`: is ω^γ ⊕ ω^γ ≤ ω^γ·K forced for a
  non-directed γ (two children incomparable at w0)? This asks whether
  `nadd_closed_con` needs completeness of the children of its exponent.

Settings (environment variables) for `transfinite.py`:
- `KRIPKE_PROGRESS=<seconds>`: a periodic progress line on stderr.
- `KRIPKE_OPP=left`: the opponent's sequence index goes one beyond the
  left side's coefficients only, rather than all of the position's.
  This keeps plays short but weakens the opponent, so "forced" becomes
  weaker evidence and "not forced" stronger.
- `KRIPKE_RESP=small`: the responder's index is twice the left side's
  largest coefficient plus 2, rather than the running total of
  coefficients. A "not forced" verdict under it must be rechecked
  without it.

Status (`sens_results.log`, `optB_results.log`, `optC_results.log`,
`nadd_power_results.log`):

| instance | verdict |
|---|---|
| exp lower xP,1 and xP,xP; exp upper xP,1 | forced |
| exp upper xP,xP; exp lower cP,1 | forced with `KRIPKE_OPP=left` |
| ω^γ ⊕ ω^γ ≤ ω^γ·K, K = 2, 3 | forced with `KRIPKE_OPP=left`; for K = 2 only with a generous responder (under `KRIPKE_RESP=small` the verdict is a spurious "not forced") |
| successor law and superdistributivity at ω^xP and ω^cP; exp upper cP,1 | time out (50 minutes, and 5 minutes with all the speed-ups below) |

None of these found a counterexample. The instances that time out now
search several thousand positions a second in a few hundred MB. What
remains is the size of the games themselves, with plays thousands of
moves deep.

## How `transfinite.py` is made fast enough

Every reduction below is exact in the model. Only the sampling of
sequence indices is heuristic. The sampling bounds depend on the
coefficients, so a reduction can still shift a heuristic verdict.

- Trees are hash-consed (`limits.K`) and ordered by serial ids, not by
  their printed forms.
- Positions are reduced to equivalent ones. Standard components merge
  into one rectangle std(α)×1. A region whose corners above the bottom
  row are finite, standard and narrower than the bottom row splits as
  the bottom row ⊕ a natural number (the argument is in the comment
  above `split_region`).
- For a fixed non-standard part A of the left side and a fixed right
  side, the standard α with A ⊕ α ≤ R forced form an initial segment,
  and known bounds are reused (`thresholds`).
- `rank0` gives a tree's rank at w0 from how it was built. Trees are
  consistent: that rank is at most the value at w1. So a standard α is
  below R exactly when α ≤ ρ(R) and α ≤ T(R), and a tree is below a
  standard β exactly when its w1 value is.
- Comparisons (`kle`): sequences are increasing, so only their last
  sampled index is checked. Exact rules settle most comparisons before
  recursing:
  - the rank bounds above;
  - a tree whose children are standard is equivalent to the pair (ρ, T);
  - left cancellation, h + a ≤ h + b iff a ≤ b, on sums kept as run
    lists (part, count).
- `kadd` drops the children of x from x + y when y has children, since
  they lie below every x + y'. `kadd` and `std` give a single child as a
  lazily built family, so a standard tail never builds its whole
  successor chain.

A complete normal form for this model, which would remove the sampling
altogether, is out of reach. A tree whose children are standard is
equivalent to its pair (ρ, T), and one level up only the children's
pairs matter, but ω^xP + m already has P-dependent children nested m
deep.

## Caveats

The limits and transfinite models approximate their quantifiers over
sequences:
- A verdict of **not forced** can be trusted when the refutation does
  not depend on the responder's index bound. Check this by hand with
  `explain_lim.py`, or by rerunning with a more generous responder.
- A verdict of **forced** is weak evidence.

An earlier version of `limits.py` had two problems:
- its opponent drew from a fixed, small range of sequence indices;
- its comparison of a single child against a sequence searched too few
  indices.

That version reported every directed width as forced. Both problems are
fixed, and the witness it missed is the one proved in Rocq as
`succ_lower_complete_WEM`.
