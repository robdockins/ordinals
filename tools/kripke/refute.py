from nested import *
w = OMEGA
one, two = stdn(1), stdn(2)
c1 = mk((), omega_mul(1,1))            # ord P (fun _ => ω)
e  = mk((), nat(1))                    # ord P (fun _ => 0)
c2 = mk((e,), nat(2))                  # succ e
a  = mk((c1, c2), omega_mul(1,2))      # ord bool [c1; c2]
print("a =", fmt(a), " directed:", directed(a))

def tree(L, R, depth):
    pad = "  " * depth
    print(f"{pad}L = {fmt_pos(L)}  vs  R = {fmt_pos(R)}   [w1: {show(rank1_sum(L))} ≤? {show(rank1_sum(R))}]"
          + ("" if le(rank1_sum(L), rank1_sum(R)) else "   ✗ fails at w1"))
    if not le(rank1_sum(L), rank1_sum(R)) or forced(L, R):
        return
    i, p, L2 = witness[(L, R)]
    print(f"{pad}  opponent: component {i}, point ({fmt(p[0])},{fmt(p[1])})")
    for j, rc in enumerate(R):
        for q, rc2 in moves(rc):
            R2 = canon(R[:j] + (rc2,) + R[j+1:])
            print(f"{pad}  - answer: component {j}, point ({fmt(q[0])},{fmt(q[1])})")
            tree(L2, R2, depth + 2)

L, R = canon([rect(a, one), rect(a, one)]), canon([rect(a, two)])
print("forced:", forced(L, R))
tree(L, R, 0)
