import ConstructiveOrdinals.NaturalArith

/-!
# An ordinal measure for hereditary substitution in Leivant's predicative System F

Port of `Ordinal/HereditarySubstF.v`.

In predicative System F, quantifiers carry a level (a kind `k`): `∀X:k. U`
quantifies over types of kind `k`, and has kind `max (k+1) k'` if `U` has kind
`k'`. Hereditary substitution terminates only on well-typed input: the type
`V` instantiating `∀X:k. U` may be larger than `U`. Mangin and Sozeau order
types lexicographically by the multiset of the kinds they quantify over, and
then by depth.

Here the multiset becomes an ordinal: `κ U` is the natural sum of `ω^k` over
the quantifiers `∀X:k` in `U`, and the type measure is `ω · κ U + depth U`.
The components of an arrow type are smaller (`tord_arrow_l`, `tord_arrow_r`),
and instantiating a quantifier by a well-kinded type is smaller (`tord_inst`).
A type of kind `k` has measure below `ω · ω^k` (`tord_bound`).
-/

namespace ConstructiveOrdinals.HereditarySubstF

open Ordinal

/-! ## Types and kinding -/

/-- Rocq: `HereditarySubstF.kind`. -/
abbrev Kind : Type := Nat

/-- Rocq: `HereditarySubstF.typ`. -/
inductive Typ : Type where
  | tvar : Nat → Typ
  | arrow : Typ → Typ → Typ
  | all : Kind → Typ → Typ

open Typ

/-- Rocq: `HereditarySubstF.tshift`. -/
def tshift : Nat → Typ → Typ
  | c, tvar Y => tvar (if Y < c then Y else Y + 1)
  | c, arrow A B => arrow (tshift c A) (tshift c B)
  | c, all k U => all k (tshift (c + 1) U)

/-- `tsubst U X T` substitutes `T` for the variable `X` in `U`.
Rocq: `HereditarySubstF.tsubst`. -/
def tsubst : Typ → Nat → Typ → Typ
  | tvar Y, X, T => if Y = X then T else tvar (if Y < X then Y else Y - 1)
  | arrow A B, X, T => arrow (tsubst A X T) (tsubst B X T)
  | all k V, X, T => all k (tsubst V (X + 1) (tshift 0 T))

/-- The number of occurrences of `X` in `U`. Rocq: `HereditarySubstF.occ`. -/
def occ : Nat → Typ → Nat
  | X, tvar Y => if Y = X then 1 else 0
  | X, arrow A B => occ X A + occ X B
  | X, all _ V => occ (X + 1) V

/-- Kinding, with cumulativity at variables. Rocq: `HereditarySubstF.kinding`. -/
inductive Kinding : List Kind → Typ → Kind → Prop where
  | var (Γ : List Kind) (X : Nat) (k k' : Kind) : List.nthError Γ X = some k → k ≤ k' →
      Kinding Γ (tvar X) k'
  | arrow (Γ : List Kind) (A B : Typ) (k k' : Kind) : Kinding Γ A k → Kinding Γ B k' →
      Kinding Γ (arrow A B) (Nat.max k k')
  | all (Γ : List Kind) (k : Kind) (U : Typ) (k' : Kind) : Kinding (k :: Γ) U k' →
      Kinding Γ (all k U) (Nat.max (k + 1) k')

/-! ## The ordinal of the kinds of a type -/

/-- Rocq: `HereditarySubstF.kord`. -/
def kord : Typ → Ordinal.{0}
  | tvar _ => 0
  | arrow A B => kord A ♯ kord B
  | all k U => ω ^ ofNat k ♯ kord U

/-- Rocq: `HereditarySubstF.depth`. -/
def depth : Typ → Nat
  | tvar _ => 1
  | arrow A B => depth A + depth B
  | all _ U => depth U + 1

/-- Rocq: `HereditarySubstF.depth_pos`. -/
theorem depth_pos : ∀ T, 0 < depth T
  | tvar _ => Nat.zero_lt_one
  | arrow A _ => Nat.lt_of_lt_of_le (depth_pos A) (Nat.le_add_right _ _)
  | all _ _ => Nat.zero_lt_succ _

/-- `n` copies of `x`, added naturally. Rocq: `HereditarySubstF.nrep`. -/
def nrep : Nat → Ordinal.{0} → Ordinal.{0}
  | 0, _ => 0
  | n + 1, x => x ♯ nrep n x

/-- Rocq: `HereditarySubstF.nrep_add`. -/
theorem nrep_add (x : Ordinal.{0}) : ∀ m n : Nat, nrep (m + n) x ≈ nrep m x ♯ nrep n x
  | 0, n => by rw [Nat.zero_add]; exact equiv_symm (nadd_zero_l _)
  | m + 1, n => by
    rw [Nat.add_right_comm]
    exact equiv_trans (nadd_congr (equiv_refl x) (nrep_add x m n)) (nadd_assoc _ _ _)

/-- Rocq: `HereditarySubstF.nadd_swap`. -/
theorem nadd_swap (a b c d : Ordinal.{0}) : (a ♯ b) ♯ (c ♯ d) ≈ (a ♯ c) ♯ (b ♯ d) :=
  equiv_trans (equiv_symm (nadd_assoc _ _ _))
    (equiv_trans (nadd_congr (equiv_refl a)
      (equiv_trans (nadd_assoc b c d) (equiv_trans (nadd_congr (nadd_comm b c) (equiv_refl d))
        (equiv_symm (nadd_assoc c b d)))))
      (nadd_assoc _ _ _))

/-- Rocq: `HereditarySubstF.kord_tshift`. -/
theorem kord_tshift : ∀ (T : Typ) (c : Nat), kord (tshift c T) = kord T
  | tvar _, _ => rfl
  | arrow A B, c => by show kord (tshift c A) ♯ kord (tshift c B) = _; rw [kord_tshift A, kord_tshift B]; rfl
  | all k U, c => by show _ ♯ kord (tshift (c + 1) U) = _; rw [kord_tshift U]; rfl

/-- Substitution adds one copy of the kinds of `T` per occurrence.
Rocq: `HereditarySubstF.kord_tsubst`. -/
theorem kord_tsubst : ∀ (U : Typ) (X : Nat) (T : Typ), kord (tsubst U X T) ≈ kord U ♯ nrep (occ X U) (kord T)
  | tvar Y, X, T => by
    show kord (if Y = X then T else _) ≈ 0 ♯ nrep (if Y = X then 1 else 0) (kord T)
    by_cases h : Y = X
    · rw [ite_eq_left h, ite_eq_left h]
      exact equiv_symm (equiv_trans (nadd_zero_l _) (nadd_zero_r _))
    · rw [ite_eq_right h, ite_eq_right h]
      exact equiv_symm (nadd_zero_l _)
  | arrow A B, X, T =>
    equiv_trans (nadd_congr (kord_tsubst A X T) (kord_tsubst B X T))
      (equiv_trans (nadd_swap _ _ _ _) (nadd_congr (equiv_refl _) (equiv_symm (nrep_add _ _ _))))
  | all k V, X, T => by
    show _ ♯ kord (tsubst V (X + 1) (tshift 0 T)) ≈ (_ ♯ kord V) ♯ nrep (occ (X + 1) V) (kord T)
    have h := kord_tsubst V (X + 1) (tshift 0 T)
    rw [kord_tshift] at h
    exact equiv_trans (nadd_congr (equiv_refl _) h) (nadd_assoc _ _ _)

/-- A type of kind `k` quantifies only over kinds below `k`.
Rocq: `HereditarySubstF.kinded_bound`. -/
theorem kinded_bound {Γ : List Kind} {T : Typ} {k : Kind} (h : Kinding Γ T k) : kord T < ω ^ ofNat k := by
  induction h with
  | var => exact pow_pos ω _
  | arrow _ _ _ k k' _ _ ih1 ih2 =>
    exact nadd_closed_con _ _ _ (ofNat_complete _)
      (lt_of_lt_of_le ih1 (pow_le_pow_right ω (ofNat_monotone (Nat.le_max_left _ _))))
      (lt_of_lt_of_le ih2 (pow_le_pow_right ω (ofNat_monotone (Nat.le_max_right _ _))))
  | all _ k _ k' _ ih =>
    exact nadd_closed_con _ _ _ (ofNat_complete _)
      (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 (ofNat_increasing (Nat.lt_succ_self k)))
        (pow_le_pow_right ω (ofNat_monotone (Nat.le_max_left _ _))))
      (lt_of_lt_of_le ih (pow_le_pow_right ω (ofNat_monotone (Nat.le_max_right _ _))))

/-- Rocq: `HereditarySubstF.nrep_below`. -/
theorem nrep_below {x : Ordinal.{0}} {k : Nat} (hx : x < ω ^ ofNat k) : ∀ n, nrep n x < ω ^ ofNat k
  | 0 => pow_pos ω _
  | n + 1 => nadd_closed_con _ _ _ (ofNat_complete _) hx (nrep_below hx n)

/-- Instantiating a quantifier by a well-kinded type decreases the ordinal of
the kinds: `ω^k` absorbs any number of copies of the instance.
Rocq: `HereditarySubstF.kord_inst`. -/
theorem kord_inst {Γ : List Kind} {T : Typ} {k : Kind} (U : Typ) (hT : Kinding Γ T k) :
    kord (tsubst U 0 T) < kord (all k U) :=
  lt_of_le_of_lt (kord_tsubst U 0 T).le
    (lt_of_lt_of_le (nadd_increasing2 _ (nrep_below (kinded_bound hT) _)) (nadd_comm _ _).le)

/-! ## The type measure `ω · κ + depth` -/

/-- Rocq: `HereditarySubstF.tord`. -/
def tord (T : Typ) : Ordinal.{0} := ω * kord T + ofNat (depth T)

/-- Lexicographic comparison, as ordinal comparison. Rocq: `HereditarySubstF.lex_lt_major`. -/
theorem lex_lt_major {a a' : Ordinal.{0}} (d d' : Nat) (h : a' < a) : ω * a' + ofNat d' < ω * a + ofNat d :=
  lt_of_lt_of_le (add_lt_add_left _ (index_lt ω ⟨d'⟩))
    (le_trans (mul_succ ω a').ge (le_trans (mul_le_mul_left ω (succ_least h)) (le_add_right _ _)))

/-- Rocq: `HereditarySubstF.lex_lt_minor`. -/
theorem lex_lt_minor {a a' : Ordinal.{0}} {d d' : Nat} (ha : a' ≤ a) (hd : d' < d) :
    ω * a' + ofNat d' < ω * a + ofNat d :=
  lt_of_le_of_lt (add_le_add (mul_le_mul_left ω ha) (le_refl _)) (add_lt_add_left _ (ofNat_increasing hd))

/-- Rocq: `HereditarySubstF.tord_arrow_l`. -/
theorem tord_arrow_l (A B : Typ) : tord A < tord (arrow A B) :=
  lex_lt_minor (nadd_le1 _ _) (Nat.add_lt_add_left (depth_pos B) (depth A))

/-- Rocq: `HereditarySubstF.tord_arrow_r`. -/
theorem tord_arrow_r (A B : Typ) : tord B < tord (arrow A B) := by
  refine lex_lt_minor (nadd_le2 _ _) ?_
  have := Nat.add_lt_add_right (depth_pos A) (depth B)
  rw [Nat.zero_add] at this
  exact this

/-- The key decrease: a well-kinded instance of `∀X:k. U` is smaller, whatever
its depth. Rocq: `HereditarySubstF.tord_inst`. -/
theorem tord_inst {Γ : List Kind} {T : Typ} {k : Kind} (U : Typ) (hT : Kinding Γ T k) :
    tord (tsubst U 0 T) < tord (all k U) :=
  lex_lt_major _ _ (kord_inst U hT)

/-- Rocq: `HereditarySubstF.depth_tshift`. -/
theorem depth_tshift : ∀ (T : Typ) (c : Nat), depth (tshift c T) = depth T
  | tvar _, _ => rfl
  | arrow A B, c => by show depth (tshift c A) + depth (tshift c B) = _; rw [depth_tshift A, depth_tshift B]; rfl
  | all _ U, c => by show depth (tshift (c + 1) U) + 1 = _; rw [depth_tshift U]; rfl

/-- Shifting does not change the measure. Rocq: `HereditarySubstF.tord_tshift`. -/
theorem tord_tshift (T : Typ) (c : Nat) : tord (tshift c T) ≈ tord T := by
  unfold tord; rw [kord_tshift, depth_tshift]

/-- A type of kind `k` has measure below `ω · ω^k`, that is `ω^(k+1)`; so all
measures lie below `ω^ω`. Rocq: `HereditarySubstF.tord_bound`. -/
theorem tord_bound {Γ : List Kind} {T : Typ} {k : Kind} (hT : Kinding Γ T k) : tord T < ω * ω ^ ofNat k :=
  lt_of_lt_of_le (add_lt_add_left _ (index_lt ω ⟨depth T⟩))
    (le_trans (mul_succ ω _).ge (mul_le_mul_left ω (succ_least (kinded_bound hT))))

/-- `∀X:1. X → X` instantiated with `∀Y:0. Y` (of kind 1): the instance is
deeper, but its kinds are smaller. Rocq example `tord_inst_example`. -/
theorem tord_inst_example :
    tord (tsubst (arrow (tvar 0) (tvar 0)) 0 (all 0 (tvar 0))) < tord (all 1 (arrow (tvar 0) (tvar 0))) :=
  tord_inst (Γ := []) _ (.all [] 0 (tvar 0) 0 (.var _ 0 0 0 rfl (Nat.le_refl 0)))

end ConstructiveOrdinals.HereditarySubstF
