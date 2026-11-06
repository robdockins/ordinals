"""Is ω^γ ⊕ ω^γ ≤ ω^γ · K forced when γ is not directed?

This is the question behind a heredity counterexample for nadd_closed_con:
if natural sums below ω^γ stay below ω^γ · K, then the closure of ω^(γ+1)
under ⊕ survives a non-directed child γ.

γ has two children that are incomparable at w0: b1 = ⟨0 | 3⟩ (one child
at w0, value 3 at w1) and b2 = 2 (standard).  The model is linear, so a
"not forced" verdict shows non-constructivity, not WEM as such.

    python3 nadd_power.py [instance numbers]
"""
import sys, time, threading
from transfinite import *

b1 = mk((("one", K0),), nat(3))
b2 = stdn(2)
gamma = mk((("one", b1), ("one", b2)), nat(4))
E = kexp(gamma)
E4 = kexp(stdn(4))          # calibration: the standard ω^4


def nsum_le_mul(e, k):
    """e ⊕ e ≤ e · k"""
    return [rect(e, stdn(1)), rect(e, stdn(1))], [rect(kmul(e, k), stdn(1))]


insts = [("calibration ω^4 ⊕ ω^4 ≤ ω^4·2", nsum_le_mul(E4, 2)),
         ("calibration ω^4 ⊕ ω^4 ≤ ω^4·1 (expect NOT)", nsum_le_mul(E4, 1)),
         ("ω^γ ⊕ ω^γ ≤ ω^γ·2", nsum_le_mul(E, 2)),
         ("ω^γ ⊕ ω^γ ≤ ω^γ·3", nsum_le_mul(E, 3))]


def main():
    assert not kle(b1, b2) and not kle(b2, b1), "children must be incomparable at w0"
    sel = sys.argv[1:]
    for k, (name, inst) in enumerate(insts):
        if sel and str(k) not in sel:
            continue
        t0 = time.time()
        r = run(*inst)
        print(f"  [{k}] {name}: {'forced' if r else 'NOT forced'}  ({round(time.time() - t0, 1)}s)",
              flush=True)


threading.stack_size(1 << 29)
sys.setrecursionlimit(10 ** 7)
th = threading.Thread(target=main)
th.start()
th.join()
