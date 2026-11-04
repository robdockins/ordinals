#!/usr/bin/env python3
"""Generate STATEMENT_REVIEW.md: headline statements, Rocq beside Lean.

The headline statements are every Rocq `Theorem`, together with the
declarations named in the porting plan: the reflection theorems, the
`*_has_enough_notations` theorems, the order-type theorems (`VF_ε₀`, …,
`VF_LVO`), the reverse-mathematics lemmas of `Classical.v`, and so on.

For each one the script asks Rocq for its closed statement (`Check`, so that
section hypotheses appear exactly as Rocq discharges them) and asks Lean for
the statement of the declaration the porting map names (`#check`).

Requirements: the Rocq development is built (`make` in the repository root,
so that `Ordinal/*.vo` exist), `coqc` is on the path, and the Lean project is
built. Run from lean/ after `python3 scripts/port_map.py`:

    python3 scripts/statement_review.py
"""

import csv
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import port_map as pm  # noqa: E402

LEAN = pm.LEAN_DIR
ROOT = LEAN.parent
ROCQ = pm.ROCQ_DIR
WORK = LEAN / ".lake" / "statement_review"
OUTPUT = LEAN / "STATEMENT_REVIEW.md"

EXTRA = re.compile(
    r"(wf_ord_lt_nat_omega|cantor_decomposition_is_classical|KnuthUp_epsilon|Γ₀_least|"
    r"Γ_enumerates|^VF_ε₀$|^VF_Γ₀$|^VF_SAO$|^VF_LAO$|^VF_SVO$|^VF_LVO$|EM_iff|reflects|"
    r"has_enough_notations|goodstein4_correct_initial_sequence|goodstein_zero|_EM$|_WEM$|"
    r"SmallVeblenOrdinal$|LargeAckermannOrdinal$|SmallAckermannOrdinal$)")
KIND = re.compile(r"^\s*(?:Global\s+|Local\s+|Program\s+)*(Lemma|Theorem|Corollary|Definition|Fixpoint)\s+"
                  r"([^\s:(]+)", re.M)


def rocq_kinds(mod):
    text = pm.strip_comments((ROCQ / (mod.replace(".", "/") + ".v")).read_text())
    return {m.group(2): m.group(1) for m in KIND.finditer(text)}


def rocq_qualified(mod, name):
    """The name qualified by any enclosing Rocq `Module` (sections add nothing)."""
    glob = (ROCQ / (mod.replace(".", "/") + ".glob")).read_text()
    src = (ROCQ / (mod.replace(".", "/") + ".v")).read_text()
    for line in glob.splitlines():
        parts = line.split(" ")
        if len(parts) == 4 and parts[0] in ("prf", "def", "ind", "thm") and parts[3] == name:
            comps = [c for c in parts[2].split(".") if parts[2] != "<>" and
                     re.search(r"^\s*Module\s+" + re.escape(c) + r"\b", src, re.M)]
            return ".".join([mod] + comps + [name])
    return f"{mod}.{name}"


def select():
    rows = list(csv.DictReader(open(LEAN / "PORTING_MAP.csv")))
    kinds = {}
    out = []
    for r in rows:
        if r["status"] != "ported":
            continue
        mod, name = r["rocq_module"], r["rocq_name"]
        if mod not in kinds:
            kinds[mod] = rocq_kinds(mod)
        if kinds[mod].get(name) == "Theorem" or (name in kinds[mod] and EXTRA.search(name)):
            out.append((mod, name, r["lean_name"].split(";")[0].strip()))
    return out


def split_numbered(text, rocq):
    pat = r"^(\d+)\n\s+: nat\n" if rocq else r"^(\d+)\n"
    parts = re.split(pat, text, flags=re.M)
    return {int(parts[i]): parts[i + 1].strip() for i in range(1, len(parts), 2)}


def main():
    items = select()
    WORK.mkdir(parents=True, exist_ok=True)
    mods = sorted({m for m, _, _ in items})
    v = [f"From Ordinal Require {m}." for m in mods] + ["Set Printing Width 100."]
    lean = ["import ConstructiveOrdinals", "set_option format.width 100",
            "open ConstructiveOrdinals Ordinal"]
    for i, (mod, name, lname) in enumerate(items):
        v += [f"Check {i}.", f"Check @{rocq_qualified(mod, name)}."]
        lean += [f"#eval ({i} : Nat)", f"#check @{lname}"]
    (WORK / "check.v").write_text("\n".join(v) + "\n")
    (WORK / "check.lean").write_text("\n".join(lean) + "\n")
    r = subprocess.run(["coqc", "-Q", "Ordinal", "Ordinal", str(WORK / "check.v")],
                       cwd=ROOT, capture_output=True, text=True)
    if r.returncode:
        sys.exit("coqc failed:\n" + r.stdout + r.stderr)
    l = subprocess.run(["lake", "env", "lean", str(WORK / "check.lean")],
                       cwd=LEAN, capture_output=True, text=True)
    if l.returncode:
        sys.exit("lean failed:\n" + l.stdout + l.stderr)
    rmap, lmap = split_numbered(r.stdout, True), split_numbered(l.stdout, False)

    preamble = (LEAN / "scripts" / "statement_review_preamble.md").read_text()
    out = [preamble.rstrip("\n"), "", f"{len(items)} statements.", ""]
    current = None
    for i, (mod, name, lname) in enumerate(items):
        if mod != current:
            out += [f"## {mod}", ""]
            current = mod
        out += [f"### `{name}`", "", "Rocq:", "```", rmap[i], "```", "Lean:", "```", lmap[i], "```", ""]
    OUTPUT.write_text("\n".join(out))
    print(f"Wrote {OUTPUT.name}: {len(items)} statements.")


if __name__ == "__main__":
    main()
