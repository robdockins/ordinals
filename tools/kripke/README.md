# Kripke search for the natural product

These scripts search for constructive counterexamples to laws of the
natural product (`Ordinal/NaturalProduct.v`). They work in a two-world
Kripke model: at w0 a proposition P is undecided, and at w1 it holds.

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
| `limits.py` | trees whose children may be increasing sequences | heuristic (see its docstring) |

`ordinals.py` implements Cantor normal forms below ω^ω, with natural
sum, natural product and fundamental sequences. `test_ordinals.py`
checks it; it is slow.

## Results and the scripts that reproduce them

- `nested_runs.py`, `minimal.py`, `refute.py` find and check the
  non-directed witness of `succ_lower_WEM`.
- `directed_strategies.py`, `tiebreak.py` cover finite trees with
  directed children. Here every instance is forced, and a fixed "top"
  strategy wins.
- `run_h.py [heights]` runs the limits model on the widths in
  `limwidths.py`, after a calibration against known results.
- `complete_witness.py` is the witness of `succ_lower_complete_WEM`: a
  limit of directed ordinals for which the successor law is not forced.
  `explain_lim.py <width> <depth>` prints the opponent's refutation for
  one of the widths.

## Caveats

The limits model approximates its quantifiers over sequences:
- A verdict of **not forced** can be trusted when the refutation does
  not depend on the responder's index bound. Check this by hand with
  `explain_lim.py`.
- A verdict of **forced** is weak evidence.

An earlier version of `limits.py` had two problems:
- its opponent drew from a fixed, small range of sequence indices;
- its comparison of a single child against a sequence searched too few
  indices.

That version reported every directed width as forced. Both problems are
fixed here, and the witness it missed is the one proved in Rocq.
