"""Search for P-independent strategies in a two-world Kripke model.

Worlds: w0 (P undecided) ≤ w1 (P true; classical).  A Kripke ordinal is
represented up to equivalence by a pair (B, T) of classical ordinals with
B ≤ T: its w0-children are the standard ordinals below B, and its value at
w1 is T.  This covers base ⊔ (sup over P of top), its glbs with standard
ordinals, and sums like 1 + that.

For trees x, y, "x ≤ y is forced at w0" means
    x ≤ y classically at w1, and every w0-child of x is below some
    w0-child of y, again forced at w0.
For game ranks, children are moves, so this asks for a strategy that only
uses moves available at w0 but is still correct at w1.

Regions are lists of rectangles ((Bx, Tx), (By, Ty)) at the origin.  All
heights are finite, so the classical rank at w1 is the natural sum, over
rows, of the row widths (by the classical row lemma), which is exact.

Moves at limit ordinals are sampled from the fundamental sequence, so a
"False" may be an artifact of the sample sizes; failures should be
re-checked with larger samples.
"""
import sys
from functools import lru_cache, cmp_to_key
from ordinals import (ZERO, ONE, OMEGA, nat, omega_mul, cmp, le, lt, omin,
                      nadd, is_succ, pred, fund, show, finite_part)

sys.setrecursionlimit(1000000)

KA = 3   # attacker samples from a fundamental sequence
KR = 5   # responder samples


def std(a):
    return (a, a)


def kmin(p, q):
    return (omin(p[0], q[0]), omin(p[1], q[1]))


def kle(p, q):
    return le(p[0], q[0]) and le(p[1], q[1])


def children(a, k):
    """standard children of a classical ordinal (canonical tree)"""
    if not a:
        return []
    if is_succ(a):
        return [pred(a)]
    return [fund(a, n) for n in range(k)]


def finite(a):
    assert not a or (len(a) == 1 and a[0][0] == 0), ("height not finite", show(a))
    return finite_part(a)


# --------------------------------------------------------------------------
# regions

def normalize(rects):
    rs = list(set(r for r in rects if r[0][1] and r[1][1]))
    out = [r for r in rs
           if not any(s != r and kle(r[0], s[0]) and kle(r[1], s[1]) for s in rs)]
    return tuple(sorted(out, key=repr))


def cut(region, p):
    u, v = p                       # standard point
    out = []
    for x, y in region:
        out.append((kmin(x, std(u)), y))
        out.append((x, kmin(y, std(v))))
    return normalize(out)


def rank1(region):
    """classical rank at w1: natural sum of row widths"""
    h = max((finite(y[1]) for _, y in region), default=0)
    total = ZERO
    for v in range(h):
        w = ZERO
        for x, y in region:
            if finite(y[1]) > v and lt(w, x[1]):
                w = x[1]
        total = nadd(total, w)
    return total


def moves(region, k):
    """w0-available moves: (point, residual region)"""
    out = []
    for x, y in region:
        for u in children(x[0], k):
            for v in children(y[0], k):
                out.append(((u, v), cut(region, (u, v))))
    return out


def rank1_sum(regions):
    t = ZERO
    for r in regions:
        t = nadd(t, rank1(r))
    return t


def canon(regions):
    return tuple(sorted((r for r in regions if r), key=repr))


# --------------------------------------------------------------------------
# forcing at w0 of  ⊕ rank(L) ≤ ⊕ rank(R)

stats = {"calls": 0}
witness = {}


@lru_cache(maxsize=None)
def forced(L, R):
    stats["calls"] += 1
    if not le(rank1_sum(L), rank1_sum(R)):
        return False
    for i, comp in enumerate(L):
        for p, comp2 in moves(comp, KA):
            L2 = canon(L[:i] + (comp2,) + L[i + 1:])
            ok = False
            for j, rcomp in enumerate(R):
                for q, rcomp2 in moves(rcomp, KR):
                    R2 = canon(R[:j] + (rcomp2,) + R[j + 1:])
                    if forced(L2, R2):
                        ok = True
                        break
                if ok:
                    break
            if not ok:
                witness[(L, R)] = (i, p, L2)
                return False
    return True


def explain(L, R, depth=0, maxdepth=8):
    """follow the attacker's winning line"""
    pad = "  " * depth
    print(pad + "L =", fmt(L), " R =", fmt(R),
          " ranks@w1:", show(rank1_sum(L)), "vs", show(rank1_sum(R)))
    if not le(rank1_sum(L), rank1_sum(R)):
        print(pad + "  -> fails already at w1")
        return
    if (L, R) in witness and depth < maxdepth:
        i, p, L2 = witness[(L, R)]
        print(pad + f"  attacker moves in component {i} at {fmt_pt(p)}; no w0 answer works")


def fmt_k(p):
    return show(p[0]) if p[0] == p[1] else f"[{show(p[0])}|{show(p[1])}]"


def fmt_pt(p):
    return f"({show(p[0])},{show(p[1])})"


def fmt_region(r):
    return "{" + ", ".join(f"{fmt_k(x)}×{fmt_k(y)}" for x, y in r) + "}"


def fmt(regions):
    return " ⊕ ".join(fmt_region(r) for r in regions) or "0"


def rect(x, y):
    return normalize(((x, y),))


def check(name, L, R, expect=None):
    L, R = canon(L), canon(R)
    forced.cache_clear(); witness.clear(); stats["calls"] = 0
    res = forced(L, R)
    tag = "" if expect is None else ("  (as expected)" if res == expect else "  <-- UNEXPECTED")
    print(f"{name}: forced={res}  [{stats['calls']} positions]{tag}")
    if not res:
        explain(L, R)
    return res
