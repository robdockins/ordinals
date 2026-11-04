from search import *
w = OMEGA
one, two = nat(1), nat(2)

print("== standard instances of the successor law (must be forced)")
for a in [nat(2), w, omega_mul(1,1), omega_mul(2), omega_mul(2,1)]:
    for b in [1, 2]:
        A = std(a)
        check(f"a={show(a)} b={b}", [rect(A, std(nat(b))), rect(A, std(one))],
              [rect(A, std(nat(b+1)))], expect=True)

print("== row_lower_EM instance (must NOT be forced)")
W = (one, w)          # 1 ⊔ sup_P ω
D = (two, w)          # 1 + W
check("row w over d x 1", [rect(D, std(one)), rect(W, std(one))],
      [normalize(((W, std(two)), (D, std(one))))], expect=False)
print("== same instance with P decided classically (must be forced)")
for Wc, Dc in [(std(w), std(w)), (std(one), std(two))]:
    check(f"W={fmt_k(Wc)} D={fmt_k(Dc)}", [rect(Dc, std(one)), rect(Wc, std(one))],
          [normalize(((Wc, std(two)), (Dc, std(one))))], expect=True)
