import Lean
import ConstructiveOrdinals.Defs

/-!
# Generalized rewriting for ordinal relations

Lean core has no counterpart to Rocq's setoid rewriting (`Setoid`,
`Morphisms`, `Proper`), which the Rocq development uses for thousands of
rewrites with `≤`, `<` and `≈`. This file provides a small replacement.

* `ord_mono` proves a goal `s ρ t` (with `ρ` one of `≤`, `<`, `≈`) where `s`
  and `t` differ only in arguments that `@[ord_mono]` lemmas can relate. It
  works like Mathlib's `gcongr`: it applies a congruence lemma, then recurses
  on the hypotheses that relate arguments, handling pointwise hypotheses
  (`∀ a, f a ≤ g a`) by introducing the bound variables.

* `ord_rw [h₁, ← h₂, …]` rewrites the goal with hypotheses
  `h : a ρ b`. For a goal `L σ R`, rewriting `a` to `b` changes the goal to
  `L' σ R'` and proves the original with transitivity and the side goals
  `L ≤ L'` and `R' ≤ R` (or `≈` variants), which are discharged by `ord_mono`
  using `h`. This is only sound when every occurrence of `a` is in a position
  with the right polarity. When it isn't, `ord_mono` fails, just as Rocq's
  `rewrite` fails to find a `Proper` instance.

  `h` may also be an equation `a = b`, in which case `ord_rw` behaves like
  `rw`, or a proof of `P ↔ Q`, in which case the goal must be exactly `P`
  (or `Q`) and is replaced using `Iff.mpr`, avoiding the `propext` that `rw`
  would introduce.

  `ord_rw [h] at h'` rewrites in a hypothesis in the same way.

All proofs are built only from the given hypotheses and the tagged lemmas, so
these tactics add no axioms.
-/

namespace ConstructiveOrdinals.Tactic

open Lean Meta Elab Tactic

/-- The relations that `ord_rw` and `ord_mono` understand. -/
inductive Rel where
  | le | lt | equiv
  deriving BEq, Inhabited, Repr

/-- Recognize `s ρ t` between ordinals, returning `(ρ, s, t)`. -/
def matchRel? (e : Expr) : MetaM (Option (Rel × Expr × Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  let isOrd (ty : Expr) : MetaM Bool := do
    return (← whnfR ty).isAppOf ``ConstructiveOrdinals.Ordinal
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``LE.le, #[ty, _, s, t] => if ← isOrd ty then return some (.le, s, t) else return none
  | some ``LT.lt, #[ty, _, s, t] => if ← isOrd ty then return some (.lt, s, t) else return none
  | some ``HasEquiv.Equiv, #[ty, _, s, t] =>
    if ← isOrd ty then return some (.equiv, s, t) else return none
  | some ``ConstructiveOrdinals.Ordinal.Le, #[s, t] => return some (.le, s, t)
  | some ``ConstructiveOrdinals.Ordinal.Lt, #[s, t] => return some (.lt, s, t)
  | some ``ConstructiveOrdinals.Ordinal.Equiv, #[s, t] => return some (.equiv, s, t)
  | _, _ => return none

/-- Facts available to `ord_mono`, as proofs whose types are relations. -/
abbrev Facts := Array Expr

/-- Close `g` with one of the facts, or a hypothesis, if one has exactly the
right type. -/
def closeWithFacts (g : MVarId) (facts : Facts) : MetaM Bool := do
  let ty ← g.getType
  for f in facts do
    let s ← saveState
    if ← isDefEq (← inferType f) ty then
      g.assign f
      return true
    s.restore
  return false

/-- Run the tactic `ord_auto` on a side goal; return whether it succeeded. -/
def tryOrdAuto (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    let rest ← Tactic.run g (evalTactic (← `(tactic| ord_auto)))
    if rest.isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

mutual

/-- Prove a relational goal `s ρ t` by congruence, using `facts` at the
leaves. Returns the side goals that could not be discharged.

If `leaves` is false (as in `ord_rw`), every relational leaf must be closed by
a fact, a hypothesis or reflexivity, and the tactic fails otherwise. If it is
true (as in `ord_mono`), relational leaves that no congruence lemma decomposes
are returned as goals, as `gcongr` does. -/
partial def solveMono (g : MVarId) (facts : Facts) (depth : Nat) (leaves := false) :
    TacticM (List MVarId) := do
  if depth == 0 then throwError "ord_mono: depth limit reached"
  g.withContext do
  let some (rel, s, t) ← matchRel? (← g.getType)
    | throwError "ord_mono: goal is not a relation between ordinals:{indentExpr (← g.getType)}"
  -- Identical sides: reflexivity.
  if rel != .lt then
    let st ← saveState
    if ← withReducible (isDefEq s t) then
      let pf ← match rel with
        | .le => mkAppM ``ConstructiveOrdinals.Ordinal.le_refl #[s]
        | _ => mkAppM ``ConstructiveOrdinals.Ordinal.equiv_refl #[s]
      g.assign pf
      return []
    st.restore
  -- A given fact or hypothesis.
  if ← closeWithFacts g facts then return []
  if (← observing? g.assumption).isSome then return []
  -- `≈` splits into two `≤` goals.
  if rel == .equiv then
    let [g₁, g₂] ← g.apply (← mkConstWithFreshMVarLevels
        ``ConstructiveOrdinals.Ordinal.equiv_intro)
      | throwError "ord_mono: unexpected result applying equiv_intro"
    return (← solveMono g₁ facts (depth - 1) leaves) ++ (← solveMono g₂ facts (depth - 1) leaves)
  -- Otherwise try each congruence lemma, matching up to reducible unfolding.
  for lem in ← labelled `ord_mono do
    let st ← saveState
    try
      let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels lem)
      let side ← solveSubgoals gs facts depth leaves
      return side
    catch _ =>
      st.restore
  if leaves then return [g]
  throwError "ord_mono: no congruence lemma applies to{indentExpr (← g.getType)}"

/-- Solve the goals produced by applying a congruence lemma. Relational goals
(possibly under binders) are solved recursively; other goals are side
conditions, tried with `ord_auto` and otherwise returned. -/
partial def solveSubgoals (gs : List MVarId) (facts : Facts) (depth : Nat) (leaves : Bool) :
    TacticM (List MVarId) := do
  let mut side := []
  for g in gs do
    if ← g.isAssigned then continue
    let (_, g') ← g.intros
    let g' ← g'.withContext do
      let ty ← instantiateMVars (← g'.getType)
      g'.change (← Core.betaReduce ty)
    if (← matchRel? (← g'.getType)).isSome then
      side := side ++ (← solveMono g' facts (depth - 1) leaves)
    else if ← tryOrdAuto g' then
      pure ()
    else
      side := side ++ [g']
  return side

end

/-- Expand a rewriting hypothesis into the facts it supplies to `ord_mono`. -/
def factsOf (h : Expr) (rel : Rel) : MetaM Facts := do
  match rel with
  | .le => return #[h]
  | .lt => return #[h, ← mkAppM ``ConstructiveOrdinals.Ordinal.le_of_lt #[h]]
  | .equiv =>
    return #[h, ← mkAppM ``ConstructiveOrdinals.Ordinal.Equiv.le #[h],
      ← mkAppM ``ConstructiveOrdinals.Ordinal.Equiv.ge #[h],
      ← mkAppM ``ConstructiveOrdinals.Ordinal.equiv_symm #[h]]

/-- Prove `tgt` from `srcPf : src`, where `src` and `tgt` are relations of the
same kind whose sides are related by `ord_mono` using `facts`. -/
def transport (src tgt srcPf : Expr) (facts : Facts) (depth : Nat) :
    TacticM (Expr × List MVarId) := do
  let some (rel, l, r) ← matchRel? tgt
    | throwError "ord_rw: the target is not a relation between ordinals:{indentExpr tgt}"
  let some (rel', l', r') ← matchRel? src
    | throwError "ord_rw: not a relation between ordinals:{indentExpr src}"
  unless rel == rel' do throwError "ord_rw: relation changed unexpectedly"
  -- Side relation: `≤` for `≤` and `<` goals, `≈` for `≈` goals.
  let sideRel (x y : Expr) : MetaM Expr :=
    if rel == .equiv then mkAppM ``HasEquiv.Equiv #[x, y] else mkAppM ``LE.le #[x, y]
  let m₁ ← mkFreshExprMVar (← sideRel l l')
  let m₂ ← mkFreshExprMVar (← sideRel r' r)
  let side₁ ← solveMono m₁.mvarId! facts depth
  let side₂ ← solveMono m₂.mvarId! facts depth
  let pf ← match rel with
    | .le =>
      mkAppM ``ConstructiveOrdinals.Ordinal.le_trans
        #[← mkAppM ``ConstructiveOrdinals.Ordinal.le_trans #[m₁, srcPf], m₂]
    | .lt => mkAppM ``ConstructiveOrdinals.Ordinal.lt_mono #[m₁, m₂, srcPf]
    | .equiv =>
      mkAppM ``ConstructiveOrdinals.Ordinal.equiv_trans
        #[← mkAppM ``ConstructiveOrdinals.Ordinal.equiv_trans #[m₁, srcPf], m₂]
  return (pf, side₁ ++ side₂)

/-- Elaborate a rewrite rule, instantiating its leading quantifiers with fresh
metavariables. Returns the proof and its (instantiated) type. -/
def elabRule (stx : Term) : TacticM (Expr × Expr) := do
  let h ← elabTerm stx none (mayPostpone := true)
  let hTy ← inferType h
  let (args, _, body) ← forallMetaTelescopeReducing hTy
  return (mkAppN h args, body)

/-- One rewriting step on the main goal. -/
def rewriteGoal (stx : Term) (symm : Bool) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let (h, hTy) ← elabRule stx
  let hTy ← instantiateMVars hTy
  -- Equations: defer to `rw`.
  if hTy.isAppOfArity ``Eq 3 then
    if symm then evalTactic (← `(tactic| rw [← $stx:term])) else evalTactic (← `(tactic| rw [$stx:term]))
    return
  -- Equivalences of propositions: the goal must be one side.
  if hTy.isAppOfArity ``Iff 2 then
    let p := hTy.getArg! 0
    let q := hTy.getArg! 1
    let (from_, to_, mp) := if symm then (q, p, ``Iff.mp) else (p, q, ``Iff.mpr)
    unless ← isDefEq (← g.getType) from_ do
      throwError "ord_rw: rewriting with `↔` needs the goal to be exactly{indentExpr from_}"
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars to_) (← g.getTag)
    g.assign (← mkAppM mp #[h, g'])
    replaceMainGoal [g'.mvarId!]
    return
  let some (rel, a, b) ← matchRel? hTy
    | throwError "ord_rw: the rule is not `≤`, `<`, `≈`, `=` or `↔`:{indentExpr hTy}"
  -- Rewriting right-to-left only makes sense for `≈`, but `← h` with `h : a ≤ b`
  -- is also accepted: it replaces `b` by `a`, which is valid in positions of
  -- the opposite polarity.
  let (pat, rep) := if symm then (b, a) else (a, b)
  let tgt ← instantiateMVars (← g.getType)
  let abst ← kabstract tgt pat
  unless abst.hasLooseBVars do
    throwError "ord_rw: did not find an instance of the pattern{indentExpr pat}\nin the goal{indentExpr tgt}"
  let newTgt := abst.instantiate1 rep
  let g' ← mkFreshExprSyntheticOpaqueMVar newTgt (← g.getTag)
  let (pf, side) ← transport newTgt tgt g' (← factsOf h rel) 32
  g.assign pf
  replaceMainGoal (g'.mvarId! :: side)

/-- One rewriting step on a hypothesis. -/
def rewriteHyp (stx : Term) (symm : Bool) (fvar : FVarId) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let (h, hTy) ← elabRule stx
  let hTy ← instantiateMVars hTy
  let src ← instantiateMVars (← fvar.getType)
  if hTy.isAppOfArity ``Iff 2 then
    let p := hTy.getArg! 0
    let q := hTy.getArg! 1
    let (from_, to_, mp) := if symm then (q, p, ``Iff.mpr) else (p, q, ``Iff.mp)
    unless ← isDefEq src from_ do
      throwError "ord_rw: rewriting with `↔` needs the hypothesis to be exactly{indentExpr from_}"
    let pf ← mkAppM mp #[h, mkFVar fvar]
    let (_, g') ← (← g.assert (← fvar.getUserName) (← instantiateMVars to_) pf).intro1P
    replaceMainGoal [← g'.tryClear fvar]
    return
  let some (rel, a, b) ← matchRel? hTy
    | throwError "ord_rw: the rule is not `≤`, `<`, `≈` or `↔`:{indentExpr hTy}"
  let (pat, rep) := if symm then (b, a) else (a, b)
  let abst ← kabstract src pat
  unless abst.hasLooseBVars do
    throwError "ord_rw: did not find an instance of the pattern{indentExpr pat}\nin{indentExpr src}"
  let newTy := abst.instantiate1 rep
  -- Transport the hypothesis (mentioning `a`) to the new type (mentioning `b`).
  let (pf, side) ← g.withContext <| transport src newTy (mkFVar fvar) (← factsOf h rel) 32
  let (_, g') ← (← g.assert (← fvar.getUserName) newTy pf).intro1P
  replaceMainGoal ((← g'.tryClear fvar) :: side)

/-- `ord_mono` proves `s ρ t` by congruence with `@[ord_mono]` lemmas and the
hypotheses in context; side conditions it cannot discharge with `ord_auto`
remain as goals. -/
elab "ord_mono" : tactic => withMainContext do
  let g ← getMainGoal
  let side ← solveMono g #[] 32 (leaves := true)
  replaceMainGoal side

/-- A rewrite rule for `ord_rw`: a term, optionally preceded by `←`. -/
syntax ordRwRule := ("← " <|> "<- ")? term

/-- `ord_rw [h₁, ← h₂]` rewrites with ordinal relations `≤`, `<`, `≈`, as
well as `=` and `↔`; see the module documentation. -/
syntax (name := ordRw) "ord_rw " "[" ordRwRule,* "]" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| ord_rw [$rules,*] $[at $h?]?) => do
    for rule in rules.getElems do
      let symm := !rule.raw[0].isNone
      let stx : Term := ⟨rule.raw[1]⟩
      match h? with
      | none => rewriteGoal stx symm
      | some h =>
        let fvar ← withMainContext do return (← getLocalDeclFromUserName h.getId).fvarId
        rewriteHyp stx symm fvar
    -- Close trivial goals, as `rewrite` does with `reflexivity`.
    let gs ← getGoals
    let mut rest := []
    for g in gs do
      let closed ← g.withContext do
        match ← matchRel? (← g.getType) with
        | some (.le, s, t) | some (.equiv, s, t) =>
          let st ← saveState
          if ← withReducible (isDefEq s t) then
            let pf ← if (← matchRel? (← g.getType)).get!.1 == .le then
                mkAppM ``ConstructiveOrdinals.Ordinal.le_refl #[s]
              else mkAppM ``ConstructiveOrdinals.Ordinal.equiv_refl #[s]
            g.assign pf; pure true
          else st.restore; pure false
        | _ => pure false
      unless closed do rest := rest ++ [g]
    setGoals rest

end ConstructiveOrdinals.Tactic
