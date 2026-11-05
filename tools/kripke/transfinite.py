"""The limits model with regions of transfinite height.

limits.py computes the w1 rank of a region row by row, so heights must be
finite.  Here the w1 rank is the closed form of staircase.py, and Kripke
ordinals can be built with ω-powers, ordinary sums, natural multiples and
natural sums, so that widths and heights such as ω^c (c depending on P)
are available.  All constructors produce increasing sequence families.
"""
import limits
from limits import K, Seq, mk, std, stdn, kle, glb, forced, canon, rect, normalize, fmt
from ordinals import ZERO, ONE, nat, oadd, nadd, succ, show, le
from staircase import srank
from functools import lru_cache


@lru_cache(maxsize=None)
def rank1(region):
    return srank(tuple((x.T, y.T) for x, y in region))


limits.rank1 = rank1

# ---- standardness: P-free trees with the same value in both worlds.
# Positions built only from standard corners are decided by their classical
# rank, which keeps the search from replaying finite descents.
STD = set()


def is_std(x):
    return x in STD or x == std(x.T)


def mark(x, *parts):
    """a tree built from standard parts is replaced by the canonical one"""
    if all(is_std(p) for p in parts):
        return std(x.T)
    return x


_fmt = limits.fmt
_fmt_cache = {}


def fmt_cached(x):
    if x not in _fmt_cache:
        _fmt_cache[x] = _fmt(x)
    return _fmt_cache[x]


limits.fmt = fmt_cached


_glb = limits.glb


@lru_cache(maxsize=None)
def glb_std(x, y):
    return mark(_glb(x, y), x, y)


limits.glb = glb_std

_forced = limits.forced


witness = {}


@lru_cache(maxsize=None)
def forced(L, R):
    """L ≤ R forced at w0 (heuristic on sequences; see limits.py)"""
    if all(is_std(z) for reg in L + R for r in reg for z in r):
        return le(limits.rank1_sum(L), limits.rank1_sum(R))
    if not le(limits.rank1_sum(L), limits.rank1_sum(R)):
        return False
    S = limits.size_of(L + R) + 1
    for i, comp in enumerate(L):
        for p, comp2 in limits.moves(comp, "opp", S):
            L2 = canon(L[:i] + (comp2,) + L[i + 1:])
            idx = coef_total(L2) + limits.size_of(L2 + R) + 1
            if not any(forced(L2, canon(R[:j] + (rc2,) + R[j + 1:]))
                       for j, rc in enumerate(R) for _, rc2 in limits.moves(rc, "resp", idx)):
                witness[(L, R)] = (i, p, L2)
                return False
    return True


limits.forced = forced

# Moving at a larger point removes less, and forcing is monotone in both
# sides, so within an increasing sequence only the largest sampled index
# matters, for either player.  The responder's bound adapts to the
# coefficients the opponent introduces.
# Sampling.  The opponent plays one beyond every coefficient in the
# position, so beyond all of the responder's commitments.  The responder's
# answers may need sums of coefficients, so its index is bounded by the
# total of the left side's coefficients; larger indices only help it.
limits.opp_indices = lambda S: (S,)
limits.resp_indices = lambda S: (S,)


def coef_total(regions):
    return sum(c for r in regions for x, y in r for z in (x, y) for _, c in z.T)


_moves = limits.moves


@lru_cache(maxsize=None)
def moves_max(region, role, S):
    """moves at points not dominated by another point of the same region"""
    ms = _moves.__wrapped__(region, role, S)
    def dom(p, q):
        return kle(p[0], q[0]) and kle(p[1], q[1])
    out = []
    for i, (p, r) in enumerate(ms):
        if any(dom(p, q) and (not dom(q, p) or j < i) for j, (q, _) in enumerate(ms) if j != i):
            continue
        out.append((p, r))
    return tuple(out)


limits.moves = moves_max

K0 = std(ZERO)


def fam_map(fam, fn, tag):
    """apply fn to every child described by a family"""
    kind, v = fam
    if kind == "one":
        return ("one", fn(v))
    return ("seq", Seq((tag, v.key), lambda n, v=v: fn(v.at(n))))


@lru_cache(maxsize=None)
def ksucc(x):
    if is_std(x):
        return std(succ(x.T))
    return mk((("one", x),), succ(x.T))


@lru_cache(maxsize=None)
def kadd(x, y):
    """ordinary sum: the children of x, and x + y' for children y' of y"""
    if not y.T:
        return x
    if is_std(x) and is_std(y):
        return std(oadd(x.T, y.T))
    fams = list(x.fams) + [fam_map(g, lambda c: kadd(x, c), ("add", x)) for g in y.fams]
    return mark(mk(fams, oadd(x.T, y.T)), x, y)


@lru_cache(maxsize=None)
def kmul(x, n):
    return K0 if n == 0 else kadd(kmul(x, n - 1), x)


@lru_cache(maxsize=None)
def knadd(x, y):
    if not x.T:
        return y
    if not y.T:
        return x
    if is_std(x) and is_std(y):
        return std(nadd(x.T, y.T))
    fams = ([fam_map(f, lambda c: knadd(c, y), ("naddl", y)) for f in x.fams] +
            [fam_map(g, lambda c: knadd(x, c), ("naddr", x)) for g in y.fams])
    return mark(mk(fams, nadd(x.T, y.T)), x, y)


def finite_value(T):
    assert not T or (len(T) == 1 and T[0][0] == 0), "exponent must be finite"
    return T[0][1] if T else 0


@lru_cache(maxsize=None)
def kexp(c):
    """ω^c: the child 0, and ω^c' · (n+1) for children c' of c"""
    if is_std(c):
        return std(((finite_value(c.T), 1),))
    fams = [("one", K0)]
    for f in c.fams:
        kind, v = f
        if kind == "one":
            fams.append(("seq", Seq(("exp1", v), lambda n, v=v: kmul(kexp(v), n + 1))))
        else:
            fams.append(("seq", Seq(("expS", v.key), lambda n, v=v: kmul(kexp(v.at(n)), n + 1))))
    return mark(mk(fams, ((finite_value(c.T), 1),)), c)


def kfinite(n):
    return stdn(n)


# P-dependent exponents
xP = mk((("one", K0),), nat(2))          # 1, or 2 if P
cP = ksucc(xP)                           # 2, or 3 if P


def run(L, R):
    return forced(canon(L), canon(R))


def superdist(a, b, c):
    return [rect(a, b), rect(a, c)], [rect(a, knadd(b, c))]


def succ_law(a, b):
    return [rect(a, b), rect(a, stdn(1))], [rect(a, ksucc(b))]


def exp_lower(c, d):
    return [rect(kexp(knadd(c, d)), stdn(1))], [rect(kexp(c), kexp(d))]


def exp_upper(c, d):
    return [rect(kexp(c), kexp(d))], [rect(kexp(knadd(c, d)), stdn(1))]
