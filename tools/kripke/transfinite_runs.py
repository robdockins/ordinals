import sys, time
from transfinite import *
t0 = time.time()
def say(name, inst):
    r = run(*inst)
    print(f"  {name}: {'forced' if r else 'NOT forced'}   ({round(time.time()-t0,1)}s)", flush=True)
    return r
one, two = stdn(1), stdn(2)
W = kexp(stdn(1))                       # standard ω
which = sys.argv[1] if len(sys.argv) > 1 else "cal"
if which == "cal":
    print("== calibration (standard)")
    say("exp lower 1,1", exp_lower(one, one))
    say("exp upper 1,1", exp_upper(one, one))
    say("superdist ω×(ω⊕ω)", superdist(W, W, W))
    say("succ law ω×(ω+1)", succ_law(W, W))
    print("== known failure (succ_lower_WEM witness, height 1)")
    c1 = mk((), ((1, 1), (0, 1))); e = mk((), nat(1)); c2 = mk((("one", e),), nat(2))
    a_bad = mk((("one", c1), ("one", c2)), ((1, 1), (0, 2)))
    say("succ law at witness", succ_law(a_bad, one))
elif which == "pdep":
    WP = kexp(xP)                       # ω, or ω^2 if P
    print("== P-dependent exponent xP (1 or 2)")
    say("exp lower xP,1", exp_lower(xP, one))
    say("exp upper xP,1", exp_upper(xP, one))
    say("exp lower xP,xP", exp_lower(xP, xP))
    say("exp upper xP,xP", exp_upper(xP, xP))
    say("succ law ω^xP × (ω+1)", succ_law(WP, W))
    say("superdist ω^xP × (ω⊕ω)", superdist(WP, W, W))
elif which == "danger":
    WD = kexp(cP)                       # ω^2, or ω^3 if P; children ω^xP·(n+1)
    print("== children with P-dependent values (exponent cP = xP+1)")
    say("succ law ω^cP × (ω+1)", succ_law(WD, W))
    say("superdist ω^cP × (ω⊕ω)", superdist(WD, W, W))
    say("exp lower cP,1", exp_lower(cP, one))
