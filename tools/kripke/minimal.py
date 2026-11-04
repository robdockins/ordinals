import itertools
from nested import *
w = OMEGA
one = stdn(1)
Ts = [nat(1), nat(2), w, omega_mul(1,1), omega_mul(2)]
def size(x): return 1 + sum(size(c) for c in x.ch)
# all trees of depth <= 2 with <= 2 children and T from Ts
lvl0 = [mk((), T) for T in Ts]
def build(prev):
    out = set(prev)
    for k in [1, 2]:
        for cs in itertools.combinations_with_replacement(prev, k):
            lo = ZERO
            for c in cs: lo = omax(lo, succ(c.T))
            for T in Ts + [lo]:
                if le(lo, T): out.add(mk(cs, T))
    return list(out)
trees = build(build(lvl0))
print(len(trees), "trees")
found = []
for a in sorted(trees, key=lambda x: (size(x), repr(x))):
    if is_standard(a): continue
    for b in [1, 2]:
        L, R = canon([rect(a, stdn(b)), rect(a, one)]), canon([rect(a, stdn(b+1))])
        if not forced(L, R):
            found.append((size(a), a, b, directed(a)))
    if len(found) >= 6: break
for s, a, b, d in found:
    print(f"size {s}: a = {fmt(a)}  b = {b}  directed={d}")
