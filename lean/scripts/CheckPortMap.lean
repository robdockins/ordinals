import ConstructiveOrdinals

/-!
# Porting map name check

Checks that every Lean name in `PORTING_MAP.csv` names a declaration of the
development, so that a stale or mistyped name in the map is caught.
`scripts/port_map.py` writes the names to `.lake/port_map_names.txt`; run it
first, then `lake env lean scripts/CheckPortMap.lean` from `lean/`.

Private declarations are matched by their user-facing name.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let known : Std.HashSet Name := env.constants.map₁.fold (init := {}) fun acc n _ =>
    acc.insert ((privateToUserName? n).getD n)
  let text ← IO.FS.readFile ".lake/port_map_names.txt"
  let names := (text.splitOn "\n").filter (· ≠ "")
  let missing := names.filter fun s => !known.contains (s.toName)
  if missing.isEmpty then
    logInfo m!"Porting map check passed: {names.length} Lean names resolve."
  else
    throwError m!"Porting map check FAILED: {missing.length} Lean names do not resolve:\n{"\n".intercalate (missing.map ("  " ++ ·))}"
