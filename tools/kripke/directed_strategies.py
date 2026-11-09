import random, collections, time
from functools import lru_cache
from nested import *
w = OMEGA
one = stdn(1)

def ptle(p, q):
    return kle(p[0], q[0]) and kle(p[1], q[1])

def answers(R):
    out = []
    for j, rc in enumerate(R):
        for q, rc2 in moves(rc):
            out.append((j, q, canon(R[:j] + (rc2,) + R[j+1:])))
    return out

def maximal(cands):
    return [c for c in cands if not any(d is not c and ptle(c[1], d[1]) and not ptle(d[1], c[1]) for d in cands)]

# ---- rule as a strategy: responder may only use maximal dominating answers
@lru_cache(maxsize=None)
def rule_wins(L, R, mode):
    if not le(rank1_sum(L), rank1_sum(R)):
        return False
    for i, comp in enumerate(L):
        for p, comp2 in moves(comp):
            L2 = canon(L[:i] + (comp2,) + L[i+1:])
            dom = [a for a in answers(R) if ptle(p, a[1])]
            cands = maximal(dom)
            if mode == "any-maxdom":
                ok = any(rule_wins(L2, a[2], mode) for a in cands)
            else:  # "every-maxdom": the choice among maximal dominating answers is irrelevant
                ok = bool(cands) and all(rule_wins(L2, a[2], mode) for a in cands)
            if not ok:
                return False
    return True

# ---- instances: directed nested widths
random.seed(11)
pool = [w, omega_mul(1,1), omega_mul(2), ((2,1),)]
def gen(d):
    k = random.randint(0, 2) if d > 0 else 0
    ch = [gen(d - 1) for _ in range(k)]
    T = ZERO
    for c in ch: T = omax(T, succ(c.T))
    T = random.choice([T, T] + [p for p in pool if le(T, p) and T != p] or [T])
    if not T: T = random.choice(pool)
    return mk(ch, T)
widths = []
while len(widths) < 150:
    x = gen(3)
    if not is_standard(x) and x.ch and directed(x): widths.append(x)

insts = []
for a in widths:
    for b in [1, 2]:
        insts.append(("succ", canon([rect(a, stdn(b)), rect(a, one)]), canon([rect(a, stdn(b+1))])))
        for (u, v), cr in moves(rect(a, stdn(b))):
            insts.append(("[S]", canon([cr, rect(a, one)]), canon([rect(a, stdn(b)), rect(u, one)])))

t0 = time.time()
summary = collections.Counter()
bad = []
for kind, L, R in insts:
    f = forced(L, R)
    a_ = rule_wins(L, R, "any-maxdom")
    e_ = rule_wins(L, R, "every-maxdom")
    summary[(kind, f, a_, e_)] += 1
    if f and not a_ and len(bad) < 3: bad.append((kind, L, R))
print(f"{len(insts)} instances over {len(widths)} directed widths ({round(time.time()-t0,1)}s)")
print("kind  forced  some-maximal-dominating-answer-wins  every-maximal-dominating-answer-wins  count")
for k, n in sorted(summary.items(), key=str):
    print("  ", *k, n)
for kind, L, R in bad:
    print("\nrule fails though forced:", kind, "\n  L =", fmt_pos(L), "\n  R =", fmt_pos(R))
