"""Does the natural sum preserve completeness?  Exact search in the
nested (finitely branching) two-world model."""
import random, sys
from functools import lru_cache
from nested import *
from ordinals import nadd

def complete(x):
    # directed, inhabitedness decided at w0, children complete
    if not x.ch and x.T != ZERO:
        return False
    return directed(x) and all(complete(c) for c in x.ch)

@lru_cache(maxsize=None)
def knadd(u, v):
    ch = [knadd(c, v) for c in u.ch] + [knadd(u, d) for d in v.ch]
    return mk(ch, nadd(u.T, v.T))

pool = [OMEGA, omega_mul(1, 1), omega_mul(2), ((2, 1),)]
def gen(d):
    k = random.randint(0, 2) if d > 0 else 0
    ch = [gen(d - 1) for _ in range(k)]
    T = ZERO
    for c in ch: T = omax(T, succ(c.T))
    T = random.choice([T, T] + [p for p in pool + [nat(i) for i in range(1, 5)] if lt(T, p)] or [T])
    return mk(ch, T)

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
cs = []
while len(cs) < 60:
    x = gen(3)
    if complete(x) and not is_standard(x): cs.append(x)
cs += [stdn(i) for i in range(1, 4)]
bad = []
for u in cs:
    for v in cs:
        if not complete(knadd(u, v)):
            bad.append((u, v))
print(f"{len(cs)**2} pairs, {len(bad)} with an incomplete natural sum")
bad.sort(key=lambda p: len(repr(p)))
for u, v in bad[:5]:
    print("  u =", fmt(u), "  v =", fmt(v), "  u⊕v =", fmt(knadd(u, v)))
