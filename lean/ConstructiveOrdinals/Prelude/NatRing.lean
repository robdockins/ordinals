import ConstructiveOrdinals.Prelude.Nat

/-!
# Normal forms of commutative-semiring expressions over `Nat`

The soundness half of the `nat_ring` tactic (`Tactic/NatRing.lean`): an
expression built from atoms, numerals, `+` and `*` is normalised to a sorted
list of monomials with coefficients, and two expressions with the same normal
form have the same value (`PExpr.eq_of_norm`). The normal forms are compared by
kernel computation. Nothing here uses `propext`.
-/

namespace ConstructiveOrdinals.NatRing

/-- Polynomial expressions over the atoms `0, 1, …`. -/
inductive PExpr : Type where
  | atom : Nat → PExpr
  | const : Nat → PExpr
  | add : PExpr → PExpr → PExpr
  | mul : PExpr → PExpr → PExpr

def PExpr.eval (env : Nat → Nat) : PExpr → Nat
  | atom i => env i
  | const n => n
  | add a b => eval env a + eval env b
  | mul a b => eval env a * eval env b

/-- The `i`-th atom of a list, `0` when out of range (`List.getD` uses
`propext`). -/
def lookup : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => lookup xs i

/-- A monomial: the sorted list of its atoms. -/
abbrev Mono : Type := List Nat

/-- A polynomial: coefficients and monomials, sorted by monomial. -/
abbrev Poly : Type := List (Nat × Mono)

def evalMono (env : Nat → Nat) : Mono → Nat
  | [] => 1
  | a :: m => env a * evalMono env m

def evalPoly (env : Nat → Nat) : Poly → Nat
  | [] => 0
  | (c, m) :: p => c * evalMono env m + evalPoly env p

def insertAtom (a : Nat) : Mono → Mono
  | [] => [a]
  | b :: m => if a ≤ b then a :: b :: m else b :: insertAtom a m

def mulMono : Mono → Mono → Mono
  | [], m => m
  | a :: m1, m2 => insertAtom a (mulMono m1 m2)

def monoBeq : Mono → Mono → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: m, b :: m' => Nat.beq a b && monoBeq m m'

def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: m, b :: m' => Nat.blt a b || (Nat.beq a b && monoLt m m')

def insertAux (c : Nat) (m : Mono) : Poly → Poly
  | [] => [(c, m)]
  | (c', m') :: p =>
    if monoBeq m m' then (c + c', m) :: p
    else if monoLt m m' then (c, m) :: (c', m') :: p
    else (c', m') :: insertAux c m p

def insertTerm (c : Nat) (m : Mono) (p : Poly) : Poly :=
  if c = 0 then p else insertAux c m p

def addPoly : Poly → Poly → Poly
  | [], q => q
  | (c, m) :: p, q => insertTerm c m (addPoly p q)

def mulTerm (c : Nat) (m : Mono) : Poly → Poly
  | [] => []
  | (c', m') :: q => insertTerm (c * c') (mulMono m m') (mulTerm c m q)

def mulPoly : Poly → Poly → Poly
  | [], _ => []
  | (c, m) :: p, q => addPoly (mulTerm c m q) (mulPoly p q)

def norm : PExpr → Poly
  | .atom i => [(1, [i])]
  | .const n => insertTerm n [] []
  | .add a b => addPoly (norm a) (norm b)
  | .mul a b => mulPoly (norm a) (norm b)

/-! ## Soundness -/

theorem add_left_comm' (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

theorem monoBeq_eq : ∀ {m m' : Mono}, monoBeq m m' = true → m = m'
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: m, b :: m', h => by
    change (Nat.beq a b && monoBeq m m') = true at h
    cases e1 : Nat.beq a b with
    | false => rw [e1] at h; exact Bool.noConfusion h
    | true =>
      rw [e1] at h
      rw [Nat.eq_of_beq_eq_true e1, monoBeq_eq (m := m) (m' := m') h]

theorem evalMono_insert (env : Nat → Nat) (a : Nat) : ∀ m : Mono, evalMono env (insertAtom a m) = env a * evalMono env m
  | [] => rfl
  | b :: m => by
    unfold insertAtom
    by_cases h : a ≤ b
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]
      show env b * evalMono env (insertAtom a m) = env a * (env b * evalMono env m)
      rw [evalMono_insert env a m, Nat.mul_left_comm]

theorem evalMono_mul (env : Nat → Nat) : ∀ m1 m2 : Mono, evalMono env (mulMono m1 m2) = evalMono env m1 * evalMono env m2
  | [], m2 => (Nat.one_mul _).symm
  | a :: m1, m2 => by
    show evalMono env (insertAtom a (mulMono m1 m2)) = env a * evalMono env m1 * evalMono env m2
    rw [evalMono_insert, evalMono_mul env m1 m2, Nat.mul_assoc]

theorem evalPoly_insertAux (env : Nat → Nat) (c : Nat) (m : Mono) :
    ∀ p : Poly, evalPoly env (insertAux c m p) = c * evalMono env m + evalPoly env p
  | [] => rfl
  | (c', m') :: p => by
    unfold insertAux
    cases hb : monoBeq m m' with
    | true =>
      rw [monoBeq_eq hb]
      show (c + c') * evalMono env m' + evalPoly env p = c * evalMono env m' + (c' * evalMono env m' + evalPoly env p)
      rw [Nat.add_mul, Nat.add_assoc]
    | false =>
      cases hl : monoLt m m' with
      | true => rfl
      | false =>
        show c' * evalMono env m' + evalPoly env (insertAux c m p) = _
        rw [evalPoly_insertAux env c m p]
        exact add_left_comm' _ _ _

theorem evalPoly_insertTerm (env : Nat → Nat) (c : Nat) (m : Mono) (p : Poly) :
    evalPoly env (insertTerm c m p) = c * evalMono env m + evalPoly env p := by
  unfold insertTerm
  by_cases h : c = 0
  · rw [ite_eq_left h, h, Nat.zero_mul, Nat.zero_add]
  · rw [ite_eq_right h]; exact evalPoly_insertAux env c m p

theorem evalPoly_add (env : Nat → Nat) : ∀ p q : Poly, evalPoly env (addPoly p q) = evalPoly env p + evalPoly env q
  | [], q => (Nat.zero_add _).symm
  | (c, m) :: p, q => by
    show evalPoly env (insertTerm c m (addPoly p q)) = c * evalMono env m + evalPoly env p + evalPoly env q
    rw [evalPoly_insertTerm, evalPoly_add env p q, Nat.add_assoc]

theorem evalPoly_mulTerm (env : Nat → Nat) (c : Nat) (m : Mono) :
    ∀ q : Poly, evalPoly env (mulTerm c m q) = c * evalMono env m * evalPoly env q
  | [] => (Nat.mul_zero _).symm
  | (c', m') :: q => by
    show evalPoly env (insertTerm (c * c') (mulMono m m') (mulTerm c m q)) =
      c * evalMono env m * (c' * evalMono env m' + evalPoly env q)
    rw [evalPoly_insertTerm, evalPoly_mulTerm env c m q, evalMono_mul, Nat.mul_add]
    congr 1
    rw [Nat.mul_assoc c c', Nat.mul_assoc c (evalMono env m), Nat.mul_left_comm c' (evalMono env m)]

theorem evalPoly_mul (env : Nat → Nat) : ∀ p q : Poly, evalPoly env (mulPoly p q) = evalPoly env p * evalPoly env q
  | [], _ => (Nat.zero_mul _).symm
  | (c, m) :: p, q => by
    show evalPoly env (addPoly (mulTerm c m q) (mulPoly p q)) = (c * evalMono env m + evalPoly env p) * evalPoly env q
    rw [evalPoly_add, evalPoly_mulTerm, evalPoly_mul env p q, Nat.add_mul]

theorem norm_sound (env : Nat → Nat) : ∀ e : PExpr, evalPoly env (norm e) = e.eval env
  | .atom i => by show 1 * (env i * 1) + 0 = env i; rw [Nat.one_mul, Nat.mul_one]; rfl
  | .const n => by
    show evalPoly env (insertTerm n [] []) = n
    rw [evalPoly_insertTerm]; show n * 1 + 0 = n; rw [Nat.mul_one]; rfl
  | .add a b => by
    show evalPoly env (addPoly (norm a) (norm b)) = a.eval env + b.eval env
    rw [evalPoly_add, norm_sound env a, norm_sound env b]
  | .mul a b => by
    show evalPoly env (mulPoly (norm a) (norm b)) = a.eval env * b.eval env
    rw [evalPoly_mul, norm_sound env a, norm_sound env b]

/-- Expressions with the same normal form have the same value. -/
theorem PExpr.eq_of_norm (env : Nat → Nat) (a b : PExpr) (h : norm a = norm b) : a.eval env = b.eval env := by
  rw [← norm_sound env a, ← norm_sound env b, h]

end ConstructiveOrdinals.NatRing
