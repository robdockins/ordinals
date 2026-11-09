"""Classical ordinals below ω^ω in Cantor normal form, and the exact rank
of staircase regions (the de Jongh-Parikh game) at a single classical world.

An ordinal is a tuple of (exponent, coefficient) pairs, exponents strictly
descending, coefficients positive.  () is zero.
"""
import sys
from functools import lru_cache, cmp_to_key
sys.setrecursionlimit(1000000)

ZERO = ()
ONE = ((0, 1),)
OMEGA = ((1, 1),)


def nat(n):
    return ((0, n),) if n > 0 else ZERO


def omega_mul(k, m=0):
    """ω·k + m"""
    t = []
    if k > 0:
        t.append((1, k))
    if m > 0:
        t.append((0, m))
    return tuple(t)


def cmp(a, b):
    for (ea, ca), (eb, cb) in zip(a, b):
        if ea != eb:
            return 1 if ea > eb else -1
        if ca != cb:
            return 1 if ca > cb else -1
    return (len(a) > len(b)) - (len(a) < len(b))


def le(a, b):
    return cmp(a, b) <= 0


def lt(a, b):
    return cmp(a, b) < 0


def omin(a, b):
    return a if le(a, b) else b


def omax(a, b):
    return b if le(a, b) else a


def nadd(a, b):
    d = {}
    for e, c in a + b:
        d[e] = d.get(e, 0) + c
    return tuple(sorted(d.items(), reverse=True))


def oadd(a, b):
    if not b:
        return a
    lead = b[0][0]
    keep = tuple(t for t in a if t[0] > lead)
    same = [t for t in a if t[0] == lead]
    if same:
        b = ((lead, same[0][1] + b[0][1]),) + b[1:]
    return keep + b


def scal(a, n):
    """n-fold natural sum"""
    return tuple((e, c * n) for e, c in a) if n > 0 else ZERO


def nmul(a, b):
    """Hessenberg product (exponents below ω, so ⊕ on exponents is +)"""
    d = {}
    for ea, ca in a:
        for eb, cb in b:
            d[ea + eb] = d.get(ea + eb, 0) + ca * cb
    return tuple(sorted(d.items(), reverse=True))


def succ(a):
    return oadd(a, ONE)


def is_succ(a):
    return bool(a) and a[-1][0] == 0


def pred(a):
    assert is_succ(a)
    e, c = a[-1]
    return a[:-1] + (((0, c - 1),) if c > 1 else ())


def finite_part(a):
    return a[-1][1] if is_succ(a) else 0


def strip_finite(a):
    return a[:-1] if is_succ(a) else a


def fund(a, n):
    """n-th element of the fundamental sequence of a limit ordinal"""
    e, c = a[-1]
    assert e >= 1
    base = a[:-1] + (((e, c - 1),) if c > 1 else ())
    return oadd(base, ((e - 1, n),) if n > 0 else ZERO)


def show(a):
    if not a:
        return "0"
    parts = []
    for e, c in a:
        p = "1" if e == 0 else ("ω" if e == 1 else f"ω^{e}")
        if e == 0:
            parts.append(str(c))
        else:
            parts.append(p if c == 1 else f"{p}·{c}")
    return " + ".join(parts)


# ---------------------------------------------------------------------------
# Rank of a staircase region (finite union of rectangles X × Y at the origin)

SEQ_SAMPLES = (4, 5, 6, 7)


def normalize(rects):
    rs = list(set((x, y) for x, y in rects if x and y))
    out = [(x, y) for (x, y) in rs
           if not any((x2, y2) != (x, y) and le(x, x2) and le(y, y2)
                      for (x2, y2) in rs)]
    return tuple(sorted(out, key=cmp_to_key(lambda r, s: cmp(r[0], s[0]))))


def cut(rects, p):
    px, py = p
    out = []
    for x, y in rects:
        out.append((omin(x, px), y))
        out.append((x, omin(y, py)))
    return normalize(out)


def extrapolate_sup(vals):
    """sup of an increasing sequence sampled at a few indices"""
    for a, b in zip(vals, vals[1:]):
        assert le(a, b), ("not increasing", [show(v) for v in vals])
    if all(v == vals[0] for v in vals):
        return vals[0]
    # highest exponent at which some coefficient differs
    exps = set(e for v in vals for e, _ in v)
    for e in sorted(exps, reverse=True):
        cs = [dict(v).get(e, 0) for v in vals]
        if len(set(cs)) > 1:
            prefix = tuple(t for t in vals[0] if t[0] > e)
            for v in vals:
                assert tuple(t for t in v if t[0] > e) == prefix
            return oadd(prefix, ((e + 1, 1),))
    raise AssertionError("unreachable")


def max_coef(D):
    return max((c for r in D for z in r for _, c in z), default=0)


def near(z):
    """points cofinal below z: ('fixed', z-1) or ('seq', fn)"""
    if is_succ(z):
        return ("fixed", pred(z))
    return ("seq", lambda n: fund(z, n))


@lru_cache(maxsize=None)
def rank(rects):
    D = normalize(rects)
    if not D:
        return ZERO
    if D != rects:
        return rank(D)
    X1, Y1 = D[0]
    Xk, Yk = D[-1]
    if is_succ(Y1):
        Y2 = D[1][1] if len(D) > 1 else ZERO
        L = strip_finite(Y1)
        if le(L, Y2):
            steps = finite_part(Y1) - finite_part(Y2)
            target = Y2
        else:
            steps = finite_part(Y1)
            target = L
        newD = normalize(((X1, target),) + D[1:])
        return nadd(rank(newD), scal(X1, steps))
    if is_succ(Xk):
        X2 = D[-2][0] if len(D) > 1 else ZERO
        L = strip_finite(Xk)
        if le(L, X2):
            steps = finite_part(Xk) - finite_part(X2)
            target = X2
        else:
            steps = finite_part(Xk)
            target = L
        newD = normalize(D[:-1] + ((target, Yk),))
        return nadd(rank(newD), scal(Yk, steps))
    best = ZERO
    for X, Y in D:
        nx, ny = near(X), near(Y)
        if nx[0] == "fixed" and ny[0] == "fixed":
            v = succ(rank(cut(D, (nx[1], ny[1]))))
        else:
            vals = []
            base = max_coef(D) + 1
            for n in range(base, base + 4):
                px = nx[1] if nx[0] == "fixed" else nx[1](n)
                py = ny[1] if ny[0] == "fixed" else ny[1](n)
                vals.append(succ(rank(cut(D, (px, py)))))
            v = extrapolate_sup(vals)
        best = omax(best, v)
    return best
