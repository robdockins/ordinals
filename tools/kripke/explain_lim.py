import sys
from limits import *
import limwidths as LW
def tree(L, R, d, pad=""):
    print(f"{pad}L={fmt_pos(L)}  R={fmt_pos(R)}  w1 {show(rank1_sum(L))} vs {show(rank1_sum(R))}")
    if not le(rank1_sum(L), rank1_sum(R)): print(pad+"  ** w1 fails"); return
    if d == 0 or (L, R) not in witness: return
    i, p, L2 = witness[(L, R)]
    S2 = max(size_of(L + R), size_of(L2))
    print(f"{pad}  opp plays ({fmt(p[0])},{fmt(p[1])})")
    for j, rc in enumerate(R):
        for q, rc2 in moves(rc, "resp", S2):
            R2 = canon(R[:j] + (rc2,) + R[j+1:])
            print(f"{pad}  resp ({fmt(q[0])},{fmt(q[1])}):")
            tree(L2, R2, d - 1, pad + "    ")
name = sys.argv[1]; a = LW.widths[name]
L, R = map(canon, LW.succ_inst(a, 1))
print(forced(L, R)); tree(L, R, int(sys.argv[2]))
