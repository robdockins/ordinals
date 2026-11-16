import Lean
import ConstructiveOrdinals.Prelude.NatRing

/-!
# A commutative-semiring normaliser for `Nat`

`nat_ring` proves an equation `s = t` between natural-number expressions
built from `+`, `*`, numerals and atoms (any other subterm) that holds in every
commutative semiring. It reifies both sides as `NatRing.PExpr`s and closes the
goal with `NatRing.PExpr.eq_of_norm` and a computation of the normal forms, so
it adds no axioms (unlike `omega` and `simp`-based tactics, which use
`propext`).
-/

namespace ConstructiveOrdinals.Tactic

open Lean Meta Elab Tactic ConstructiveOrdinals.NatRing

def pexprToExpr : PExpr → Expr
  | .atom i => mkApp (mkConst ``PExpr.atom) (mkRawNatLit i)
  | .const n => mkApp (mkConst ``PExpr.const) (mkRawNatLit n)
  | .add a b => mkApp2 (mkConst ``PExpr.add) (pexprToExpr a) (pexprToExpr b)
  | .mul a b => mkApp2 (mkConst ``PExpr.mul) (pexprToExpr a) (pexprToExpr b)

/-- Reify a `Nat` expression, collecting atoms up to definitional equality. -/
partial def reifyNat (atoms : IO.Ref (Array Expr)) (e : Expr) : MetaM PExpr := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``HAdd.hAdd, #[_, _, _, _, a, b] => return .add (← reifyNat atoms a) (← reifyNat atoms b)
  | some ``HMul.hMul, #[_, _, _, _, a, b] => return .mul (← reifyNat atoms a) (← reifyNat atoms b)
  | some ``Nat.add, #[a, b] => return .add (← reifyNat atoms a) (← reifyNat atoms b)
  | some ``Nat.mul, #[a, b] => return .mul (← reifyNat atoms a) (← reifyNat atoms b)
  | some ``Nat.succ, #[a] => return .add (← reifyNat atoms a) (.const 1)
  | _, _ =>
    if let some n := e.rawNatLit? then
      return .const n
    if let some n ← (Meta.evalNat e).run then
      return .const n
    let as ← atoms.get
    for i in [0:as.size] do
      if ← isDefEq as[i]! e then
        return .atom i
    atoms.set (as.push e)
    return .atom as.size

/-- Prove an equation between `Nat` expressions that holds in every
commutative semiring. The normal forms are compared here, and again by the
kernel when it checks the proof. -/
elab "nat_ring" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, lhs, rhs) := ty.eq? | throwError "nat_ring: goal is not an equation"
  let atoms ← IO.mkRef #[]
  let a ← reifyNat atoms lhs
  let b ← reifyNat atoms rhs
  unless norm a == norm b do
    throwError "nat_ring: the two sides have different normal forms"
  let as ← atoms.get
  let lst ← mkListLit (mkConst ``Nat) as.toList
  let env ← withLocalDeclD `i (mkConst ``Nat) fun i => mkLambdaFVars #[i] (mkApp2 (mkConst ``lookup) lst i)
  let hnorm ← mkEqRefl (mkApp (mkConst ``norm) (pexprToExpr a))
  let pf := mkApp4 (mkConst ``PExpr.eq_of_norm) env (pexprToExpr a) (pexprToExpr b) hnorm
  let pfTy := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat)
    (mkApp2 (mkConst ``PExpr.eval) env (pexprToExpr a)) (mkApp2 (mkConst ``PExpr.eval) env (pexprToExpr b))
  unless ← isDefEq pfTy (← goal.getType) do
    throwError "nat_ring: the reified equation does not match the goal"
  goal.assign pf

end ConstructiveOrdinals.Tactic
