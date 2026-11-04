"""Two-world Kripke search with nested Kripke ordinals that may have limits.

A Kripke ordinal has a value T at w1 and a set of w0-children given by
*families*: either a single child, or an increasing sequence n ↦ c(n)
(no largest element), such as the fundamental sequence of ω.  Sequences
are infinite, so quantifiers over them are approximated:
  - the opponent plays one index beyond everything in the position
    (opp_indices): larger points cut less, so these dominate;
  - the responder searches every index up to a few beyond that
    (resp_indices);
  - in comparisons, "for all n" is checked for n < NCHECK, and the ∃
    searches indices up to max(n, coefficients of the child) + KR.
Results are therefore heuristic.  A "not forced" verdict is reliable when
the refutation does not depend on the responder's index bound (check with
explain_lim.py); a "forced" verdict is weak evidence, since the opponent
may need larger indices.  An earlier version sampled the opponent from a
fixed small range and bounded the ∃ in comparisons by KR only, and
reported every directed width as forced; both were wrong.
"""
import sys
from functools import lru_cache
from ordinals import (ZERO, ONE, OMEGA, nat, omega_mul, le, lt, omin, omax,
                      nadd, succ, show, is_succ, pred, fund)

sys.setrecursionlimit(1000000)

KR = 3                 # responder slack
NCHECK = 5


class Seq:
    """an increasing sequence of Kripke ordinals, identified by a key"""
    __slots__ = ("key", "fn", "_cache")
    registry = {}

    def __new__(cls, key, fn):
        if key in Seq.registry:
            return Seq.registry[key]
        s = object.__new__(cls)
        s.key, s.fn, s._cache = key, fn, {}
        Seq.registry[key] = s
        return s

    def at(self, n):
        if n not in self._cache:
            self._cache[n] = self.fn(n)
        return self._cache[n]

    def __hash__(self):
        return hash(self.key)

    def __eq__(self, o):
        return self is o

    def __repr__(self):
        return f"seq{self.key!r}"


class K:
    __slots__ = ("fams", "T", "_h")

    def __init__(self, fams, T):
        self.fams = fams      # tuple of ("one", K) or ("seq", Seq)
        self.T = T
        self._h = hash((fams, T))

    def __eq__(self, o):
        return isinstance(o, K) and self.T == o.T and self.fams == o.fams

    def __hash__(self):
        return self._h

    def __repr__(self):
        return fmt(self)


def mk(fams, T):
    return K(tuple(sorted(set(fams), key=repr)), T)


@lru_cache(maxsize=None)
def std(a):
    """standard ordinal with its canonical tree"""
    if not a:
        return K((), ZERO)
    if is_succ(a):
        return K((("one", std(pred(a))),), a)
    return K((("seq", Seq(("std", a), lambda n, a=a: std(fund(a, n)))),), a)


def stdn(n):
    return std(nat(n))


def opp_indices(S):
    # sequences are increasing and a larger point removes less, so the
    # largest choice dominates; play beyond the responder's last index
    return (S + 5,)


def resp_indices(S):
    return tuple(range(0, S + 4))


def sample(fam, role, S):
    kind, v = fam
    if kind == "one":
        return [v]
    idx = opp_indices(S) if role == "opp" else resp_indices(S)
    return [v.at(n) for n in idx]


def children(x, role, S):
    out = []
    for f in x.fams:
        out.extend(sample(f, role, S))
    return out


def coef(x):
    """largest finite coefficient in T(x)"""
    return max((c for _, c in x.T), default=0)


def size_of(regions):
    """largest finite coefficient in the position: grows with the indices used"""
    m = 0
    for r in regions:
        for x, y in r:
            for z in (x, y):
                for _, c in z.T:
                    m = max(m, c)
    return m


@lru_cache(maxsize=None)
def kle(x, y):
    """x ≤ y forced at w0 (approximate on sequences)"""
    if not le(x.T, y.T):
        return False
    for f in x.fams:
        idxs = [None] if f[0] == "one" else range(NCHECK)
        for n in idxs:
            c = f[1] if f[0] == "one" else f[1].at(n)
            ok = False
            for g in y.fams:
                # a sequence index needed to dominate c grows with c's coefficients
                reach = max(n or 0, coef(c)) + KR + 1
                cands = [g[1]] if g[0] == "one" else [g[1].at(m) for m in range(0, reach)]
                if any(kle(c, d) for d in cands):
                    ok = True
                    break
            if not ok:
                return False
    return True


@lru_cache(maxsize=None)
def glb(x, y):
    if kle(x, y):
        return x
    if kle(y, x):
        return y
    fams = []
    for f in x.fams:
        for g in y.fams:
            if f[0] == "one" and g[0] == "one":
                fams.append(("one", glb(f[1], g[1])))
            elif f[0] == "seq" and g[0] == "seq":
                fams.append(("seq", Seq(("glb", f[1].key, g[1].key),
                                        lambda n, a=f[1], b=g[1]: glb(a.at(n), b.at(n)))))
            else:
                s, o = (f[1], g[1]) if f[0] == "seq" else (g[1], f[1])
                fams.append(("seq", Seq(("glb1", s.key, o),
                                        lambda n, s=s, o=o: glb(s.at(n), o))))
    return mk(fams, omin(x.T, y.T))


def is_standard_T(x):
    return x == std(x.T)


def fmt(x):
    if x == std(x.T):
        return show(x.T)
    parts = []
    for kind, v in x.fams:
        parts.append(fmt(v) if kind == "one" else f"lim{v.key[0]}")
    return "⟨" + ",".join(parts) + "|" + show(x.T) + "⟩"


# ---- regions (finite heights) ---------------------------------------------

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
        wdt = ZERO
        for x, y in region:
            if finite(y.T) > v:
                wdt = omax(wdt, x.T)
        total = nadd(total, wdt)
    return total


@lru_cache(maxsize=None)
def moves(region, role, S):
    out = []
    for x, y in region:
        for u in children(x, role, S):
            for v in children(y, role, S):
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
    S = size_of(L + R)
    for i, comp in enumerate(L):
        for p, comp2 in moves(comp, "opp", S):
            L2 = canon(L[:i] + (comp2,) + L[i + 1:])
            S2 = max(S, size_of((comp2,)))
            if not any(forced(L2, canon(R[:j] + (rc2,) + R[j + 1:]))
                       for j, rc in enumerate(R) for _, rc2 in moves(rc, "resp", S2)):
                witness[(L, R)] = (i, p, L2)
                return False
    return True


def fmt_region(r):
    return "{" + ", ".join(f"{fmt(x)}×{fmt(y)}" for x, y in r) + "}"


def fmt_pos(regions):
    return " ⊕ ".join(fmt_region(r) for r in regions) or "0"
