from limits import *
w = OMEGA
one = stdn(1)
def lim(name, fn, T, extra=()):
    return mk((("seq", Seq((name,), fn)),) + tuple(("one", e) for e in extra), T)
def succ_inst(a, b): return [rect(a, stdn(b)), rect(a, one)], [rect(a, stdn(b + 1))]
Pw = mk((), w)
A = lim("A", lambda n: mk((("one", stdn(n)),), omega_mul(1, n + 1)), omega_mul(2))
B = lim("B", lambda n: mk((("one", stdn(n)),), omega_mul(n + 1)), ((2,1),))
C = lim("C", lambda n: mk((("one", mk((("one", stdn(n)),), omega_mul(1, n + 1))),), omega_mul(1, n + 2)), omega_mul(2))
Dd = lim("D", lambda n: mk((("one", stdn(n)),), omega_mul(1, n + 1)), omega_mul(2), extra=(Pw,))
E = mk((("one", A),), omega_mul(2, 1))
F = glb(A, std(omega_mul(1, 3)))
G = lim("G", lambda n: std(nat(n)) if n % 2 == 0 else mk((("one", stdn(n - 1)),), omega_mul(1, n)), omega_mul(2))
widths = {"A": A, "B": B, "C": C, "D": Dd, "E": E, "F": F, "G": G}
