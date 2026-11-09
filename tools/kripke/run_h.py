import sys, time
from limits import *
import limwidths as LW
from ordinals import OMEGA as w
one, two = stdn(1), stdn(2)
heights = [int(x) for x in sys.argv[1:] if x.isdigit()] or [1]
def run(L, R): return forced(canon(L), canon(R))
t0 = time.time()
print("== calibration")
for a in [std(w), std(omega_mul(1,1)), std(omega_mul(2))] + ([std(((2,1),))] if "--w2" in sys.argv else []):
    print(f"   standard {fmt(a)}: successor law: {[run(*LW.succ_inst(a, b)) for b in heights]} (expect True)", flush=True)
W = mk((("one", stdn(0)),), w); D = mk((("one", stdn(0)), ("one", stdn(1))), w)
print("   row_lower_EM:", run([rect(D, one), rect(W, one)], [normalize(((W, two), (D, one)))]), "(expect False)")
c1 = mk((), omega_mul(1,1)); e = mk((), nat(1)); c2 = mk((("one", e),), nat(2))
print("   succ_lower_WEM witness:", run(*LW.succ_inst(mk((("one", c1), ("one", c2)), omega_mul(1,2)), 1)), "(expect False)")
print(f"== Kripke limits, heights {heights}")
for name, a in LW.widths.items():
    sl = [run(*LW.succ_inst(a, b)) for b in heights]
    S = []
    for b in heights:
        for (u, v), cr in moves(rect(a, stdn(b)), "opp", 2):
            S.append(run([cr, rect(a, one)], [rect(a, stdn(b)), rect(u, one)]))
    print(f"   {name} = {fmt(a)}: successor law {sl}; [S] {sum(S)}/{len(S)} forced   ({round(time.time()-t0,1)}s)", flush=True)
