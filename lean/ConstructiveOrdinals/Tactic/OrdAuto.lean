import Lean.LabelAttribute

/-!
# Hint database for ordinal automation

This replaces the Rocq hint database `ord` (`Global Hint Resolve ... : ord`
and `auto with ord`). Lemmas tagged `@[ord_hint]` are tried by the `ord_auto`
tactic, which is a depth-bounded `solve_by_elim` over the local context and
the tagged lemmas.

`solve_by_elim` only applies the given lemmas and hypotheses, so the proofs it
builds add no axioms of their own.
-/

/-- Lemmas used by `ord_auto`; the analogue of the Rocq hint database `ord`. -/
register_label_attr ord_hint

/-- Congruence and monotonicity lemmas used by `ord_rw` and `ord_mono`; the
analogue of Rocq's `Add Parametric Morphism` and `Proper` instances.

A tagged lemma should conclude `f x₁ … xₙ ρ f y₁ … yₙ` with `ρ` one of `≤`,
`<` or `≈`, from hypotheses relating `xᵢ` and `yᵢ`. Those hypotheses may be
universally quantified (pointwise), as for `sup`. Any other hypotheses are
side conditions, which are tried with `ord_auto` or left to the user. -/
register_label_attr ord_mono

/-- Depth-bounded proof search over hypotheses and `@[ord_hint]` lemmas;
the analogue of Rocq's `auto with ord`. `ord_auto [h₁, h₂]` adds extra
lemmas, like `auto with ord h₁ h₂`. -/
syntax (name := ordAuto) "ord_auto" (" [" Lean.Parser.Tactic.SolveByElim.arg,* "]")? : tactic

-- `hygiene false` keeps the label name `ord_hint` from being renamed by the
-- macro, which would make `solve_by_elim` look up a nonexistent attribute.
set_option hygiene false in
macro_rules
  | `(tactic| ord_auto) => `(tactic| solve_by_elim (maxDepth := 8) using ord_hint)
  | `(tactic| ord_auto [$ts,*]) =>
      `(tactic| solve_by_elim (maxDepth := 8) [$ts,*] using ord_hint)
