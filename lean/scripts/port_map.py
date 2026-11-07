#!/usr/bin/env python3
"""Generate and check the Rocq-to-Lean porting map.

Every named Rocq declaration in ../Ordinal must be accounted for in Lean. A
Rocq declaration counts as ported when a Lean docstring cites it as
``Rocq: `File.name` `` (any backticked `File.name` in a docstring, where `File`
is a Rocq module). Declarations that are intentionally not ported one-to-one
are listed in scripts/port_overrides.csv with a status and a note.

The script writes PORTING_MAP.csv and checks that:
  * every Lean citation names a real Rocq declaration (catches typos);
  * every declaration of a Rocq file whose Lean module exists is accounted for;
  * every override names a real Rocq declaration and a known status.

It also writes the map's Lean names to .lake/port_map_names.txt, which
scripts/CheckPortMap.lean checks against the built environment.

Usage (from lean/):  python3 scripts/port_map.py [--strict]
With --strict, Rocq files that have no Lean module yet are also errors.
"""

import csv
import re
import sys
from pathlib import Path

LEAN_DIR = Path(__file__).resolve().parent.parent
ROCQ_DIR = LEAN_DIR.parent / "Ordinal"
LEAN_SRC = LEAN_DIR / "ConstructiveOrdinals"
OVERRIDES = LEAN_DIR / "scripts" / "port_overrides.csv"
OUTPUT = LEAN_DIR / "PORTING_MAP.csv"
# Lean names in the map, one per line, for scripts/CheckPortMap.lean.
NAMES_OUT = LEAN_DIR / ".lake" / "port_map_names.txt"

# Rocq module -> Lean module path (relative to ConstructiveOrdinals/).
MODULES = {
    "Defs": "Defs.lean",
    "Operators": "Operators.lean",
    "Arith": "Arith.lean",
    "Enumerate": "Enumerate.lean",
    "Fixpoints": "Fixpoints.lean",
    "Cantor": "Cantor.lean",
    "NaturalArith": "NaturalArith.lean",
    "NaturalProduct": "NaturalProduct.lean",
    "Classical": "Classical.lean",
    "Reflection": "Reflection.lean",
    "WellFounded": "WellFounded.lean",
    "Examples": "Examples.lean",
    "GoodsteinSequences": "GoodsteinSequences.lean",
    "Countable": None,  # not ported (experimental)
    "VeblenDefs": "Veblen/Defs.lean",
    "VeblenCon": "Veblen/Constructive.lean",
    "VeblenClassical": "Veblen/Classical.lean",
    "VeblenFacts": "Veblen/Facts.lean",
    "AckermannTower": "AckermannTower.lean",
    "SchutteColumn": "Schutte/Column.lean",
    "SchutteColumnFacts": "Schutte/ColumnFacts.lean",
    "Notation.CantorNotation": "Notation/Cantor.lean",
    "Notation.Interpolants": "Notation/Interpolants.lean",
    "Notation.CantorProduct": "Notation/CantorProduct.lean",
    "Notation.CantorDecomposition": "Notation/CantorDecomposition.lean",
    "Notation.VNotation": "Notation/V.lean",
    "Notation.VWNotation": "Notation/VW.lean",
    "Notation.ATowerFinNotation": "Notation/ATowerFin.lean",
    "Notation.ATowerNotation": "Notation/ATower.lean",
    "Notation.SchutteStack": "Notation/SchutteStack.lean",
    "Notation.SchutteMatrix": "Notation/SchutteMatrix.lean",
}

STATUSES = {"ported", "merged", "dropped"}

DECL_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)?(?:Global\s+|Local\s+|Program\s+)*"
    r"(Lemma|Theorem|Corollary|Fact|Proposition|Remark|Definition|Fixpoint|"
    r"CoFixpoint|Inductive|Record|Class|Instance|Canonical\s+Structure|Let)\s+"
    r"([A-Za-z_\u0080-￿][\w'\u0080-￿]*)"
)
# Later members of a mutual `Inductive`/`Fixpoint` block: `with name ...`
# starting a line (the name may be on the next line).
WITH_RE = re.compile(r"^[ \t]*with\s+([A-Za-z_\u0080-\uffff][\w'\u0080-\uffff]*)(?![\w'])(?!\s*=>)(?<!signature)", re.M)
# `Add Parametric Morphism ... as name.` / `Add Parametric Relation ... as name.`
ADD_RE = re.compile(r"Add\s+Parametric\s+(?:Morphism|Relation)\b(.*?)\bas\s+([\w']+)\s*\.", re.S)


def strip_comments(text):
    """Remove (nested) Rocq comments."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def rocq_decls():
    """Map Rocq module name -> ordered list of declaration names."""
    decls = {}
    for mod in MODULES:
        path = ROCQ_DIR / (mod.replace(".", "/") + ".v")
        text = strip_comments(path.read_text())
        names = []
        for line in text.splitlines():
            m = DECL_RE.match(line)
            if m:
                names.append(m.group(2))
        names += [m.group(1) for m in WITH_RE.finditer(text)]
        names += [m.group(2) for m in ADD_RE.finditer(text)]
        seen = set()
        decls[mod] = [n for n in names if not (n in seen or seen.add(n))]
    return decls


LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+([^\s:({\[]+)?"
)
NS_RE = re.compile(r"^\s*(namespace|section|mutual)(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
CITE_RE = re.compile(r"`((?:Notation\.)?[A-Z][A-Za-z]*)\.([^`\s]+)`")


def lean_citations():
    """Map (rocq module, name) -> list of Lean names citing it."""
    cites = {}
    for path in sorted(LEAN_SRC.rglob("*.lean")):
        ns, pending, in_doc, doc = [], [], False, []
        module_doc = False
        for line in path.read_text().splitlines():
            if not in_doc and ("/--" in line or "/-!" in line):
                in_doc, doc = True, []
                module_doc = "/-!" in line
            if in_doc:
                doc.append(line)
                if "-/" in line:
                    in_doc = False
                    text = "\n".join(doc)
                    text = text[text.index("Rocq:"):] if "Rocq:" in text else ""
                    refs = [(m.group(1), m.group(2)) for m in CITE_RE.finditer(text)
                            if m.group(1) in MODULES]
                    if module_doc:
                        rel = path.relative_to(LEAN_SRC)
                        for r in refs:
                            cites.setdefault(r, []).append(f"({rel} module doc)")
                    else:
                        pending = refs
                continue
            # `ns` is a stack of (kind, components); sections add no components.
            if (m := NS_RE.match(line)):
                comps = m.group(2).split(".") if m.group(1) == "namespace" and m.group(2) else []
                ns.append(comps)
                continue
            if END_RE.match(line) and ns:
                ns.pop()
                continue
            if pending and (m := LEAN_DECL_RE.match(line)):
                name = ".".join([c for comps in ns for c in comps] + [m.group(2) or "(anonymous)"])
                for r in pending:
                    cites.setdefault(r, []).append(name)
                pending = []
    return cites


def load_overrides():
    rows = {}
    if OVERRIDES.exists():
        with OVERRIDES.open() as f:
            for row in csv.DictReader(f):
                rows[(row["rocq_module"], row["rocq_name"])] = row
    return rows


def main():
    strict = "--strict" in sys.argv
    decls = rocq_decls()
    cites = lean_citations()
    overrides = load_overrides()
    errors = []

    known = {(mod, n) for mod, ns in decls.items() for n in ns}
    for (mod, name), where in sorted(cites.items()):
        if (mod, name) not in known:
            errors.append(f"Lean cites unknown Rocq declaration {mod}.{name} (in {where[0]})")
    for (mod, name), row in sorted(overrides.items()):
        if name != "*" and (mod, name) not in known:
            errors.append(f"override names unknown Rocq declaration {mod}.{name}")
        if row["status"] not in STATUSES:
            errors.append(f"override {mod}.{name}: unknown status {row['status']!r}")

    out_rows, summary = [], []
    for mod, names in decls.items():
        lean_mod = MODULES[mod]
        exists = lean_mod is not None and (LEAN_SRC / lean_mod).exists()
        counts = {"ported": 0, "merged": 0, "dropped": 0, "todo": 0}
        for name in names:
            ov = overrides.get((mod, name)) or overrides.get((mod, "*"))
            if (mod, name) in cites:
                status, lean, note = "ported", "; ".join(cites[(mod, name)]), ""
                if ov:
                    status, note = ov["status"], ov["note"]
            elif ov:
                status, lean, note = ov["status"], ov.get("lean_name", ""), ov["note"]
            else:
                status, lean, note = "todo", "", ""
                if exists or strict:
                    errors.append(f"{mod}.{name} is not accounted for in Lean")
            counts[status] += 1
            out_rows.append([mod, name, lean, status, note])
        total = len(names)
        done = total - counts["todo"]
        state = "n/a" if lean_mod is None else ("in progress" if exists else "not started")
        summary.append(f"  {mod:30} {done:4}/{total:<4} {state}")

    with OUTPUT.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["rocq_module", "rocq_name", "lean_name", "status", "note"])
        w.writerows(out_rows)

    lean_names = sorted({n.strip() for r in out_rows for n in r[2].split(";")
                         if n.strip() and not n.strip().startswith("(")})
    NAMES_OUT.parent.mkdir(exist_ok=True)
    NAMES_OUT.write_text("\n".join(lean_names) + "\n")

    print("Porting progress (accounted / total declarations):")
    print("\n".join(summary))
    total = len(out_rows)
    done = sum(1 for r in out_rows if r[3] != "todo")
    print(f"  {'TOTAL':30} {done:4}/{total:<4}")
    if errors:
        print(f"\n{len(errors)} error(s):")
        print("\n".join("  " + e for e in errors))
        sys.exit(1)


if __name__ == "__main__":
    main()
