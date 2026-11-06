"""The limits model with regions of transfinite height.

limits.py computes the w1 rank of a region row by row, so heights must be
finite.  Here the w1 rank is the closed form of staircase.py, and Kripke
ordinals can be built with ω-powers, ordinary sums, natural multiples and
natural sums, so that widths and heights such as ω^c (c depending on P)
are available.  All constructors produce increasing sequence families.
"""
import limits
from limits import K, Seq, mk, std, stdn, kle, glb, forced, canon, rect, normalize, fmt
from ordinals import ZERO, ONE, nat, oadd, nadd, nmul, omax, succ, show, le
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


@lru_cache(maxsize=None)
def is_std(x):
    return x in STD or x == std(x.T)


def mark(x, *parts):
    """a tree built from standard parts is replaced by the canonical one"""
    if all(is_std(p) for p in parts):
        return std(x.T)
    return x


_glb = limits.glb


@lru_cache(maxsize=None)
def glb_std(x, y):
    return mark(_glb(x, y), x, y)


limits.glb = glb_std

_forced = limits.forced


witness = {}


def all_std(side):
    return all(is_std(z) for reg in side for r in reg for z in r)


def is_finite_T(a):
    return not a or (len(a) == 1 and a[0][0] == 0)


# ---- reduction of positions.  Both rules replace a component by an
# equivalent one (in the exact model; sampling bounds shift slightly since
# they depend on the coefficients):
#  - standard components are merged into one rectangle std(α)×1;
#  - a region D = B ∪ T, B its corners of height 1 and T the rest, with T
#    finite and standard and every width of T below some width of B, is
#    split as B ⊕ N, N the rank of the rows of T above the bottom one.
#    The bottom row absorbs the row-0 cells of T.  B ⊕ N ≤ D: a move in N
#    is answered by removing the top cell of T, and so is a move B → B',
#    since B' + 1 ≤ B and N is finite.  D ≤ B ⊕ N: a cut above row 0 is a
#    move in T (the new height-1 corner is absorbed by B), and a cut in
#    row 0 at u leaves B' ∪ T' with T' ⊆ T, again of this form.

def split_region(r):
    B = tuple(c for c in r if c[1] is stdn(1))
    T = tuple(c for c in r if c[1] is not stdn(1))
    if not B or not T:
        return None
    if not all(is_std(x) and is_std(y) and is_finite_T(x.T) and is_finite_T(y.T) for x, y in T):
        return None
    if not all(any(kle(x, xb) for xb, _ in B) for x, _ in T):
        return None
    N = srank(tuple((x.T, nat(limits.finite(y.T) - 1)) for x, y in T))
    return normalize(B), N


@lru_cache(maxsize=None)
def reduce_side(regions):
    out, a = [], ZERO
    for r in regions:
        if all_std((r,)):
            a = nadd(a, rank1(r))
            continue
        sp = split_region(r)
        if sp is None:
            out.append(r)
        else:
            out.append(sp[0])
            a = nadd(a, sp[1])
    if a:
        out.append(rect(std(a), stdn(1)))
    return canon(out)


def split_std(side):
    """the non-standard components, and the rank of the standard ones"""
    A = tuple(r for r in side if not all_std((r,)))
    a = limits.rank1_sum(tuple(r for r in side if all_std((r,))))
    return A, a


# Forcing is antitone in L, so for a fixed non-standard part A of L and a
# fixed R, the standard ordinals α with A ⊕ α ≤ R forced form an initial
# segment.  thresholds[(A, R)] = (largest α seen forced, smallest α seen
# not forced).  A bound found at a larger α was computed with a larger
# responder index bound (it grows with α), which only moves the sampled
# game closer to the unbounded one.
thresholds = {}

# progress readout: set to a number of seconds (or KRIPKE_PROGRESS)
import os, sys, time, resource
progress = float(os.environ.get("KRIPKE_PROGRESS", 0)) or None
_stats = {"calls": 0, "t0": None, "last": 0.0, "depth": 0, "maxd": 0}


def report():
    st = _stats
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    rss = rss / 2 ** 20 if sys.platform == "darwin" else rss / 2 ** 10
    print(f"    [{time.time() - st['t0']:.0f}s] calls {st['calls']}  depth {st['depth']}"
          f" (max {st['maxd']})  game cache {forced_game.cache_info().currsize}"
          f"  kle cache {kle.cache_info().currsize}  thresholds {len(thresholds)}"
          f"  rss {rss:.0f}MB", file=sys.stderr, flush=True)


def forced(L, R):
    """L ≤ R forced at w0 (heuristic on sequences; see limits.py)"""
    st = _stats
    st["calls"] += 1
    if progress and st["calls"] % 4096 == 0:
        now = time.time()
        if st["t0"] is None:
            st["t0"] = st["last"] = now
        if now - st["last"] >= progress:
            st["last"] = now
            report()
    L, R = reduce_side(L), reduce_side(R)
    A, a = split_std(L)
    # One side standard.  Trees are consistent (the rank at w0 is at most
    # the value at w1), so against a standard R the responder can always
    # answer while the w1 values allow, and a standard α is below R exactly
    # when it is below both its w0 rank and its w1 value.
    if all_std(R):
        return le(limits.rank1_sum(L), limits.rank1_sum(R))
    if not A:
        v = rank0_side(R)
        if v is not None:
            return le(a, v) and le(a, limits.rank1_sum(R))
    if not le(limits.rank1_sum(L), limits.rank1_sum(R)):
        return False
    lo, hi = thresholds.get((A, R), (None, None))
    if lo is not None and le(a, lo):
        return True
    if hi is not None and le(hi, a):
        return False
    st["depth"] += 1
    st["maxd"] = max(st["maxd"], st["depth"])
    try:
        r = forced_game(L, R)
    finally:
        st["depth"] -= 1
    thresholds[(A, R)] = (a, hi) if r else (lo, a)
    return r


# The opponent's sequence index: one beyond every coefficient of the
# position ("both", the default), or only beyond those of the left side
# ("left"), which its own moves produce.  "left" keeps the responder's
# large indices from inflating the opponent's, so plays stay short; it
# weakens the opponent, so its "forced" verdicts are weaker evidence and
# its "not forced" verdicts stronger.
OPP = os.environ.get("KRIPKE_OPP", "both")
# The responder's sequence index: the total of the left side's
# coefficients plus the position's size ("total", the default), or twice
# the left side's largest coefficient plus 2 ("small").  "small" keeps
# the indices from snowballing; a "not forced" verdict under it should be
# rechecked with "total".
RESP = os.environ.get("KRIPKE_RESP", "total")


def resp_index(L2, R):
    if RESP == "small":
        return 2 * limits.size_of(L2) + 2
    return coef_total(L2) + limits.size_of(L2 + R) + 1


@lru_cache(maxsize=None)
def forced_game(L, R):
    S = limits.size_of(L if OPP == "left" else L + R) + 1
    for i, comp in enumerate(L):
        for p, comp2 in limits.moves(comp, "opp", S):
            L2 = canon(L[:i] + (comp2,) + L[i + 1:])
            idx = resp_index(L2, R)
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

_kle = limits.kle


def push_run(out, part, k):
    """append k copies of part to a run list, merging with the last run"""
    if not part.T:
        return
    if out and is_std(part) and is_std(out[-1][0]):
        out[-1] = (std(oadd(out[-1][0].T, scal_std(part.T, k))), 1)
    elif out and out[-1][0] is part:
        out[-1] = (part, out[-1][1] + k)
    else:
        out.append((part, k))


def scal_std(a, k):
    """a · k (ordinary): ω^e·c + rest becomes ω^e·(c·k) + rest"""
    if not a or not k:
        return ZERO
    return ((a[0][0], a[0][1] * k),) + a[1:]


@lru_cache(maxsize=None)
def summands(x):
    """x as an ordinary sum: runs (part, count), adjacent standard parts merged"""
    how = STRUCT.get(x)
    if how is None or how[0] != "add":
        return ((x, 1),)
    out = list(summands(how[1]))
    for part, k in summands(how[2]):
        push_run(out, part, k)
    return tuple(out)


def runs_val(runs, which):
    """the w1 value ("T") or w0 rank ("rho") of a run list, as a classical sum"""
    r = ZERO
    for part, k in runs:
        v = part.T if which == "T" else rank0(part)
        if v is None:
            return None
        r = oadd(r, scal_std(v, k))
    return r


def ksum(runs):
    r = K0
    for part, k in runs:
        for _ in range(k):
            r = kadd(r, part)
    return r


def fam_std(f):
    """every member of the family is standard (False when unknown)"""
    kind, v = f
    if kind == "one":
        return is_std(v)
    k = v.key
    if k[0] in ("std", "succ"):
        return True
    if k[0] == "exp1":
        return is_std(k[1])
    if k[0] == "expS" and k[1] in Seq.registry:
        return fam_std(("seq", Seq.registry[k[1]]))
    return False


@lru_cache(maxsize=None)
def kle(x, y):
    """limits.kle, settled by exact rules where possible:
    - x ≤ y forces T(x) ≤ T(y) and ρx ≤ ρy;
    - T(x) ≤ ρy, T(y) gives x ≤ y, through the standard ordinal T(x)
      (x ≤ std(T x) since trees are consistent);
    - when the children of x are standard, x is equivalent to the pair
      (ρx, T x), and then T(x) ≤ T(y) and ρx ≤ ρy suffice;
    - left cancellation: h + a ≤ h + b iff a ≤ b."""
    if not le(x.T, y.T):
        return False
    rx, ry = rank0(x), rank0(y)
    if rx is not None and ry is not None:
        if not le(rx, ry):
            return False
        if le(x.T, ry):
            return True
        if all(fam_std(f) for f in x.fams):
            return True
    xs, ys = list(summands(x)), list(summands(y))
    stripped = False
    while xs and ys and xs[0][0] is ys[0][0]:
        k = min(xs[0][1], ys[0][1])
        for rs in (xs, ys):
            rs[0] = (rs[0][0], rs[0][1] - k)
            if not rs[0][1]:
                rs.pop(0)
        stripped = True
    if stripped:
        if not xs:
            return True
        if not ys:
            return False    # y = h and x = h + a with a > 0 (T(x) ≤ T(y) failed otherwise)
        # the rank rules on the remainders, before rebuilding them
        tx, ty, px, py = runs_val(xs, "T"), runs_val(ys, "T"), runs_val(xs, "rho"), runs_val(ys, "rho")
        if not le(tx, ty):
            return False
        if px is not None and py is not None:
            if not le(px, py):
                return False
            if le(tx, py):
                return True
        one = lambda rs: rs[0][0] if len(rs) == 1 and rs[0][1] == 1 else ksum(rs)
        return kle(one(xs), one(ys))
    return _kle.__wrapped__(x, y)


limits.kle = kle

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
    """ordinary sum: the children of x, and x + y' for children y' of y.

    When y has children at w0, those of x lie below every x + y' and are
    dropped (an equivalent tree); otherwise kmul(x, n) would carry n
    copies of every family of x."""
    if not y.T:
        return x
    if not x.T:
        return y
    if is_std(x) and is_std(y):
        return std(oadd(x.T, y.T))
    # A single child y' of y gives the constant family x + y', built lazily:
    # building it eagerly would build a whole successor chain for a
    # standard tail.
    fams = [fam_map(g, lambda c: kadd(x, c), ("add", x)) if g[0] == "seq"
            else ("seq", Seq(("add1", x, g[1]), lambda n, x=x, c=g[1]: kadd(x, c)))
            for g in y.fams] or list(x.fams)
    return built(mark(mk(fams, oadd(x.T, y.T)), x, y), "add", x, y)


# How each non-standard tree was built, for rank0.
STRUCT = {}


def built(r, *how):
    if not is_std(r):
        STRUCT.setdefault(r, how)
    return r


@lru_cache(maxsize=None)
def rank0(x):
    """the rank of x at w0, or None when its structure is not known.

    ρ(x + y) = ρx + ρy (kadd keeps only the children x + y' when y has
    any), ρ(x ⊕ y) = ρx ⊕ ρy, ρ(ω^c) = ω^ρc, and otherwise the supremum of
    ρc + 1 over single children."""
    if is_std(x):
        return x.T
    how = STRUCT.get(x)
    if how is not None:
        if how[0] == "exp":
            c = rank0(how[1])
            if c is None or not is_finite_T(c):
                return None
            return ((finite_value(c), 1),)
        u, v = rank0(how[1]), rank0(how[2])
        if u is None or v is None:
            return None
        return oadd(u, v) if how[0] == "add" else nadd(u, v)
    out = ZERO
    for kind, v in x.fams:
        c = rank0(v) if kind == "one" else None
        if c is None:
            return None
        out = omax(out, succ(c))
    return out


def rank0_side(side):
    """the w0 rank of a natural sum of single-rectangle regions, or None"""
    total = ZERO
    for reg in side:
        if len(reg) != 1:
            return None
        (x, y), = reg
        u = rank0(x)
        if u is None or not is_std(y):
            return None
        total = nadd(total, nmul(u, y.T))
    return total


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
    return built(mark(mk(fams, nadd(x.T, y.T)), x, y), "nadd", x, y)


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
    return built(mark(mk(fams, ((finite_value(c.T), 1),)), c), "exp", c)


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
