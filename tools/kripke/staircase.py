"""Closed form for the rank of a staircase region at a classical world.

For a normalized staircase with corners (x_1, y_1), ..., (x_k, y_k),
widths decreasing and heights increasing, the rank is
    x_1 ⊗ y_1  ⊕  x_2 ⊗ (y_2 ⊖ y_1)  ⊕ ...  ⊕  x_k ⊗ (y_k ⊖ y_(k-1)),
where y ⊖ x is the left difference (x + (y ⊖ x) = y).
"""
from functools import cmp_to_key
from ordinals import ZERO, cmp, le, lt, nadd, nmul, oadd


def lsub(y, x):
    """the d with x + d = y, for x ≤ y"""
    assert le(x, y)
    for i, (tx, ty) in enumerate(zip(x, y)):
        if tx != ty:
            (ex, cx), (ey, cy) = tx, ty
            if ex == ey:
                return ((ey, cy - cx),) + y[i + 1:]
            return y[i:]
    return y[len(x):]


def srank(rects):
    rs = [(x, y) for x, y in rects if x and y]
    rs = [r for r in rs if not any(s != r and le(r[0], s[0]) and le(r[1], s[1]) for s in rs)]
    rs = sorted(set(rs), key=cmp_to_key(lambda r, s: cmp(r[1], s[1])))
    total, prev = ZERO, ZERO
    for x, y in rs:
        total = nadd(total, nmul(x, lsub(y, prev)))
        prev = y
    return total


if __name__ == "__main__":
    import random
    from ordinals import rank, show, nat, OMEGA, omega_mul
    random.seed(3)
    pool = [nat(1), nat(2), nat(3), OMEGA, omega_mul(1, 1), omega_mul(1, 2), omega_mul(2),
            omega_mul(2, 1)]
    for a in pool:
        for n in range(1, 5):
            assert oadd(nat(0), a) == a
    bad = 0
    for trial in range(120):
        k = random.randint(1, 3)
        rs = tuple((random.choice(pool), random.choice(pool)) for _ in range(k))
        try:
            r = rank(rs)
        except (AssertionError, RecursionError):
            continue
        if r != srank(rs):
            bad += 1
            if bad <= 5:
                print("MISMATCH", [(show(x), show(y)) for x, y in rs], show(r), show(srank(rs)))
    print("mismatches:", bad)
