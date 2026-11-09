"""Two-world Kripke search with nested Kripke ordinals (exact, no sampling).

A Kripke ordinal is a finitely branching tree: its children are the
children available at w0 (themselves Kripke ordinals), and it carries its
value T at w1 (a classical ordinal below ω^ω, at least the successor of
each child's T).  Children that exist only at w1 need not be listed: at w1
everything is classical, so only T matters there.

    x ≤ y forced at w0  iff  T(x) ≤ T(y) and every child of x is ≤ (forced)
                             some child of y.

Regions have finite heights (T of every height is finite), so the rank at w1
is the natural sum of the row widths (classical row lemma), which is exact.
"""
import sys
from functools import lru_cache
from ordinals import ZERO, ONE, OMEGA, nat, omega_mul, le, lt, omin, omax, nadd, succ, show

sys.setrecursionlimit(1000000)


class K:
    __slots__ = ("ch", "T", "_h")

    def __init__(self, ch, T):
        self.ch = ch          # tuple of K, canonical
        self.T = T
        self._h = hash((ch, T))

    def __eq__(self, o):
        return isinstance(o, K) and self.T == o.T and self.ch == o.ch

    def __hash__(self):
        return self._h

    def __repr__(self):
        return fmt(self)


@lru_cache(maxsize=None)
def kle(x, y):
    if not le(x.T, y.T):
        return False
    return all(any(kle(c, d) for d in y.ch) for c in x.ch)


def keq(x, y):
    return kle(x, y) and kle(y, x)


def mk(children, T):
    """canonical node: drop dominated children, sort"""
    cs = list(set(children))
    keep = [c for c in cs if not any(d != c and kle(c, d) and not (kle(d, c) and repr(d) > repr(c)) for d in cs)]
    keep = sorted(keep, key=repr)
    for c in keep:
        assert lt(c.T, T) or le(succ(c.T), T), "T too small"
    return K(tuple(keep), T)


@lru_cache(maxsize=None)
def stdn(n):
    """standard finite ordinal"""
    return mk((), ZERO) if n == 0 else mk((stdn(n - 1),), nat(n))


def B(x):
    """value at w0"""
    v = ZERO
    for c in x.ch:
        v = omax(v, succ(B(c)))
    return v


@lru_cache(maxsize=None)
def glb(x, y):
    if kle(x, y):
        return x
    if kle(y, x):
        return y
    return mk(tuple(glb(c, d) for c in x.ch for d in y.ch), omin(x.T, y.T))


def is_standard(x):
    return B(x) == x.T


def fmt(x):
    if is_standard(x):
        return show(x.T)
    if not x.ch:
        return f"⟨|{show(x.T)}⟩"
    return "⟨" + ",".join(fmt(c) for c in x.ch) + "|" + show(x.T) + "⟩"


# --------------------------------------------------------------------------
# regions: tuples of rectangles (width, height), heights with finite T

def finite(a):
    assert not a or (len(a) == 1 and a[0][0] == 0), "height must be finite"
    return a[0][1] if a else 0


def normalize(rects):
    rs = list(set(r for r in rects if r[0].T and r[1].T))
    out = [r for r in rs
           if not any(s != r and kle(r[0], s[0]) and kle(r[1], s[1])
                      and not (kle(s[0], r[0]) and kle(s[1], r[1]) and repr(s) > repr(r))
                      for s in rs)]
    return tuple(sorted(out, key=repr))


def rect(x, y):
    return normalize(((x, y),))


def cut(region, p):
    u, v = p
    out = []
    for x, y in region:
        out.append((glb(x, u), y))
        out.append((x, glb(y, v)))
    return normalize(out)


@lru_cache(maxsize=None)
def rank1(region):
    h = max((finite(y.T) for _, y in region), default=0)
    total = ZERO
    for v in range(h):
        w = ZERO
        for x, y in region:
            if finite(y.T) > v:
                w = omax(w, x.T)
        total = nadd(total, w)
    return total


@lru_cache(maxsize=None)
def moves(region):
    out = []
    for x, y in region:
        for u in x.ch:
            for v in y.ch:
                out.append(((u, v), cut(region, (u, v))))
    return tuple(out)


def canon(regions):
    return tuple(sorted((r for r in regions if r), key=repr))


def rank1_sum(regions):
    t = ZERO
    for r in regions:
        t = nadd(t, rank1(r))
    return t


witness = {}


@lru_cache(maxsize=None)
def forced(L, R):
    if not le(rank1_sum(L), rank1_sum(R)):
        return False
    for i, comp in enumerate(L):
        for p, comp2 in moves(comp):
            L2 = canon(L[:i] + (comp2,) + L[i + 1:])
            if not any(forced(L2, canon(R[:j] + (rc2,) + R[j + 1:]))
                       for j, rc in enumerate(R) for _, rc2 in moves(rc)):
                witness[(L, R)] = (i, p, L2)
                return False
    return True


def fmt_region(r):
    return "{" + ", ".join(f"{fmt(x)}×{fmt(y)}" for x, y in r) + "}"


def fmt_pos(regions):
    return " ⊕ ".join(fmt_region(r) for r in regions) or "0"


def explain(L, R, depth=0, maxdepth=6):
    pad = "  " * depth
    print(f"{pad}L = {fmt_pos(L)}   R = {fmt_pos(R)}   [w1: {show(rank1_sum(L))} vs {show(rank1_sum(R))}]")
    if not le(rank1_sum(L), rank1_sum(R)):
        print(pad + "  fails at w1")
        return
    if (L, R) in witness:
        i, p, L2 = witness[(L, R)]
        print(f"{pad}  opponent moves in component {i} at ({fmt(p[0])},{fmt(p[1])}); "
              f"every w0 answer then fails")


def directed(x):
    """complete-ordinal analogue: children directed (forced at w0), recursively"""
    for c in x.ch:
        if not directed(c):
            return False
    for c in x.ch:
        for d in x.ch:
            if not any(kle(c, e) and kle(d, e) for e in x.ch):
                return False
    return True
