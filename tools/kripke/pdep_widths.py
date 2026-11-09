"""Successor law at widths built from ω^c with P-dependent exponent c
standard children n at w0, value ω^2 (or ω^3) at w1."""
import sys
from limits import *
from limwidths import lim, succ_inst
W2 = lim("W2", lambda n: stdn(n), ((2, 1),))          # ω (¬P) / ω^2 (P)
W3 = lim("W3", lambda n: stdn(n), ((3, 1),))          # ω / ω^3
for name, a in [("W2", W2), ("W3", W3)]:
    for b in [1, 2]:
        print(name, "b =", b, "succ law forced:", forced(*map(canon, succ_inst(a, b))), flush=True)
def ksucc(x): return mk((("one", x),), succ(x.T))
def kplus(x, n):
    for _ in range(n): x = ksucc(x)
    return x
W2p1 = ksucc(W2)                                   # ω+1 / ω^2+1
W2x2 = lim("W2x2", lambda n: kplus(W2, n), ((2, 2),))   # ω·2 / ω^2·2
for name, a, bs in [("W+1", W2p1, [1, 2]), ("W·2", W2x2, [1])]:
    for b in bs:
        print(name, "b =", b, "succ law forced:", forced(*map(canon, succ_inst(a, b))), flush=True)
