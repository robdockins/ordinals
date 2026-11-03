import ConstructiveOrdinals

/-!
# Axiom audit

Checks that no declaration in a `ConstructiveOrdinals.*` module depends on any
axiom: not `propext`, `Quot.sound` or `Classical.choice`, and not `sorryAx` or
`Lean.ofReduceBool`. This is the Lean counterpart of requiring every Rocq
theorem to be "Closed under the global context".

Run from `lean/` with `lake env lean scripts/AxiomAudit.lean`. It exits with an
error, listing the offending declarations, if any axiom is found.

Two kinds of declaration are skipped:
* Modules under `ConstructiveOrdinals.Tactic` hold metaprograms. They run
  during elaboration and never appear in proof terms.
* `injEq` lemmas, which Lean generates automatically for every constructor and
  proves using `propext`.

Skipping these is sound: if any audited declaration used one of them, the
axiom would show up in that declaration's own audit result.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let audited (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      (`ConstructiveOrdinals).isPrefixOf mod &&
        !(`ConstructiveOrdinals.Tactic).isPrefixOf mod &&
        !(n matches .str _ "injEq")
    | none => false
  let names := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    if audited n then acc.push n else acc
  let mut bad : Array (Name × Array Name) := #[]
  for n in names do
    let axs ← collectAxioms n
    unless axs.isEmpty do
      bad := bad.push (n, axs)
  if bad.isEmpty then
    logInfo m!"Axiom audit passed: {names.size} declarations, no axioms."
  else
    let lines := bad.qsort (fun a b => a.1.toString < b.1.toString) |>.map fun (n, axs) =>
      m!"  {n}: {axs.toList}"
    throwError m!"Axiom audit FAILED: {bad.size} of {names.size} declarations use axioms:\n{MessageData.joinSep lines.toList "\n"}"
