import itertools, random
from ordinals import *

def check(name, got, want):
    ok = got == want
    print(("ok  " if ok else "FAIL"), name, show(got), "" if ok else f"(want {show(want)})")
    return ok

w = OMEGA
allok = True
# rectangles agree with the Hessenberg product
for a, b in [(nat(3), nat(4)), (w, nat(2)), (omega_mul(1,1), omega_mul(1,1)),
             (omega_mul(2), omega_mul(1,3)), (((2,1),), omega_mul(1,1)), (((2,1),(1,1)), ((2,1),(1,1)))]:
    allok &= check(f"rect {show(a)} x {show(b)}", rank(((a, b),)), nmul(a, b))
# hand-computed L-shapes
allok &= check("col 1x(w+1) + row w x1", rank(((nat(1), omega_mul(1,1)), (w, nat(1)))), omega_mul(2,1))
allok &= check("col 1xw + row wx1", rank(((nat(1), w), (w, nat(1)))), omega_mul(2))
# finite staircases: rank = number of points
random.seed(1)
for _ in range(200):
    k = random.randint(1, 4)
    rs = tuple((nat(random.randint(0, 5)), nat(random.randint(0, 5))) for _ in range(k))
    pts = set((u, v) for x, y in rs for u in range(finite_part(x)) for v in range(finite_part(y)))
    if rank(rs) != nat(len(pts)):
        allok = False; print("FAIL finite", rs, show(rank(rs)), len(pts)); break
else:
    print("ok   200 random finite staircases")
print("ALL OK" if allok else "SOME FAILED")
