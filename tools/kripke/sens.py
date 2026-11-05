"""Transfinite-height instances: python3 sens.py [instance numbers]"""
import sys, transfinite as t
from transfinite import *
one = stdn(1); W = kexp(stdn(1)); WP = kexp(xP); WD = kexp(cP)
insts = [("exp lower xP,1", exp_lower(xP, one)), ("exp upper xP,1", exp_upper(xP, one)),
         ("exp lower xP,xP", exp_lower(xP, xP)), ("exp upper xP,xP", exp_upper(xP, xP)),
         ("succ ω^xP×(ω+1)", succ_law(WP, W)), ("superdist ω^xP×(ω⊕ω)", superdist(WP, W, W)),
         ("succ ω^cP×(ω+1)", succ_law(WD, W)), ("superdist ω^cP×(ω⊕ω)", superdist(WD, W, W)),
         ("exp lower cP,1", exp_lower(cP, one)), ("exp upper cP,1", exp_upper(cP, one))]
import time
def main():
    sel = sys.argv[1:]
    for k, (name, inst) in enumerate(insts):
        if sel and str(k) not in sel:
            continue
        t0 = time.time()
        r = run(*inst)
        print(f"  [{k}] {name}: {'forced' if r else 'NOT forced'}  ({round(time.time()-t0,1)}s)", flush=True)

import threading
threading.stack_size(1 << 29)
sys.setrecursionlimit(10 ** 7)
th = threading.Thread(target=main); th.start(); th.join()
