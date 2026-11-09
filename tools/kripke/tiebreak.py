import collections
from functools import lru_cache
from directed_strategies import insts, answers, maximal, ptle, widths
from nested import *

def pick(cands, rule):
    if not cands: return None
    def ykey(a): return a[1][1].T
    def xkey(a): return a[1][0].T
    import functools
    from ordinals import cmp
    if rule == "top":   k = lambda a, b: -cmp(ykey(a), ykey(b)) or -cmp(xkey(a), xkey(b))
    if rule == "level": k = lambda a, b: cmp(ykey(a), ykey(b)) or -cmp(xkey(a), xkey(b))
    if rule == "wide":  k = lambda a, b: -cmp(xkey(a), xkey(b)) or -cmp(ykey(a), ykey(b))
    return sorted(cands, key=functools.cmp_to_key(k))[0]

@lru_cache(maxsize=None)
def det_wins(L, R, rule):
    if not le(rank1_sum(L), rank1_sum(R)):
        return False
    for i, comp in enumerate(L):
        for p, comp2 in moves(comp):
            L2 = canon(L[:i] + (comp2,) + L[i+1:])
            c = pick(maximal([a for a in answers(R) if ptle(p, a[1])]), rule)
            if c is None or not det_wins(L2, c[2], rule):
                return False
    return True

for rule in ["top", "level", "wide"]:
    cnt = collections.Counter()
    for kind, L, R in insts:
        if kind != "succ": continue
        cnt[det_wins(L, R, rule)] += 1
    print(f"rule {rule:5s}: successor-law instances won {cnt[True]}, lost {cnt[False]}")
