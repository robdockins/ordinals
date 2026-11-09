import random, time
from nested import *
w = OMEGA
def run(L, R, show_fail=False):
    L, R = canon(L), canon(R)
    r = forced(L, R)
    if not r and show_fail: explain(L, R)
    return r

one, two = stdn(1), stdn(2)
print("== calibration")
W = mk((stdn(0),), w); D = mk((stdn(0), stdn(1)), w)
print("row_lower_EM instance forced:", run([rect(D, one), rect(W, one)], [normalize(((W, two), (D, one)))], True), "(expect False)")
print("standard 3x2 successor:", run([rect(stdn(3), two), rect(stdn(3), one)], [rect(stdn(3), stdn(3))]), "(expect True)")
Wc = mk((stdn(0),) + tuple(stdn(n) for n in range(1, 4)), w)   # crude 'ω' at w0 truncated: not standard, skip
print("\n== obstruction instance: t = succ(t_i), t_i = <|ω>, s = 1")
ti = mk((), w); t = mk((ti,), omega_mul(1, 1))
print("   t =", fmt(t), " directed:", directed(t))
for y in [0, 1]:
    for extra in [(), ((stdn(3), stdn(1)),), ((mk((ti,stdn(2)), omega_mul(1,1)), one),)]:
        E = normalize(((t, stdn(y + 1)),) + extra)
        r = run([cut(E, (one, stdn(y))), rect(t, one)], [E, rect(one, one)], True)
        print(f"   [S_gen] E={fmt_region(E)} s=1 y={y}: forced={r}")

print("\n== random nested Kripke widths")
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
while len(widths) < 120:
    x = gen(3)
    if not is_standard(x) and x.ch: widths.append(x)
t0 = time.time()
res = {"succ": [0, 0], "succ-dir": [0, 0], "[S]": [0, 0], "[S]-dir": [0, 0]}
fails = []
for a in widths:
    dr = directed(a)
    for b in [1, 2]:
        r = run([rect(a, stdn(b)), rect(a, one)], [rect(a, stdn(b + 1))])
        res["succ"][0] += 1; res["succ"][1] += (not r)
        if dr: res["succ-dir"][0] += 1; res["succ-dir"][1] += (not r)
        if not r: fails.append(("succ", a, b))
        for (u, v), cr in moves(rect(a, stdn(b))):
            r = run([cr, rect(a, one)], [rect(a, stdn(b)), rect(u, one)])
            res["[S]"][0] += 1; res["[S]"][1] += (not r)
            if dr: res["[S]-dir"][0] += 1; res["[S]-dir"][1] += (not r)
            if not r: fails.append(("[S]", a, b, u, v))
print(f"   ({round(time.time()-t0,1)}s)")
for k, (n, f) in res.items():
    print(f"   {k:9s}: {n} instances, {f} not forced")
for f in fails[:4]:
    print("   e.g.", f[0], "a =", fmt(f[1]), "b =", f[2], *(("q =", fmt(f[3]), fmt(f[4])) if len(f) > 3 else ()))
