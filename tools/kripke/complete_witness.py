"""The witness of succ_lower_complete_WEM in the limits model.

c_n has the w0 child n and value ω+1 at w1 (where P holds); a is the
limit of c_0, c_1, ...  All children are directed.
"""
from limits import *
from limwidths import lim, succ_inst

cfam = lambda n: mk((("one", stdn(n)),), omega_mul(1, 1))
a = lim("c", cfam, omega_mul(1, 2))
print("successor law a ⊕ a ≤ a ⊗ 2 forced:", forced(*map(canon, succ_inst(a, 1))), "(expect False)")
# the core: a bottom-row move also cuts the top row
for n, j in [(1, 1), (1, 3), (2, 5)]:
    cn, cj = cfam(n), cfam(j)
    print(f"  c_{j} ⊕ c_{n} ≤ rk{{c_{n}×2, c_{j}×1}} forced:",
          forced(canon([rect(cj, stdn(1)), rect(cn, stdn(1))]),
                 canon([normalize(((cn, stdn(2)), (cj, stdn(1))))])))
