import ConstructiveOrdinals.Fixpoints

/-!
# Additively closed ordinals and Cantor normal forms

Port of `Ordinal/Cantor.v`.

Classically (with `ExcludedMiddle`), every ordinal has a unique Cantor normal
form. Conversely, the existence of Cantor normal forms implies the excluded
middle, even when restricted to complete ordinals.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-! ## Additively closed ordinals -/

/-- Rocq: `Cantor.additively_closed`. -/
def AdditivelyClosed (x : Ordinal.{u}) : Prop := ∀ a b, a < x → b < x → a + b < x

/-- Additive closure is invariant under `≈`. -/
theorem AdditivelyClosed.congr {x y : Ordinal.{u}} (h : x ≈ y) (hx : AdditivelyClosed x) :
    AdditivelyClosed y := fun a b ha hb =>
  lt_of_lt_of_le (hx a b (lt_of_lt_of_le ha h.ge) (lt_of_lt_of_le hb h.ge)) h.le

/-- Rocq: `Cantor.additively_closed_collapse`. -/
theorem additively_closed_collapse {a b : Ordinal.{u}} (hb : AdditivelyClosed b) (ha : a < b) :
    a + b ≤ b := by
  rw [add_unfold]
  exact lub_least (le_of_lt ha) (sup_least fun i => succ_least (hb a (b i) ha (index_lt b i)))

/-- Rocq: `Cantor.additively_closed_limit`. -/
theorem additively_closed_limit {x : Ordinal.{u}} (h₁ : 1 < x) (hx : AdditivelyClosed x) :
    IsLimit x :=
  ⟨(lt_elim h₁).elim fun b _ => ⟨b⟩, fun a =>
    let h := lt_of_le_of_lt (succ_le_add_one (x a)) (hx (x a) 1 (index_lt x a) h₁)
    let ⟨a', ha'⟩ := lt_elim h
    ⟨a', le_elim ha' PUnit.unit⟩⟩

/-- `a + a * n ≤ a * (n + 1)` for finite `n`. -/
theorem add_mul_ofNat_le (a : Ordinal.{u}) (n : Nat) :
    a + a * ofNat n ≤ a * ofNat (n + 1) :=
  calc a + a * ofNat n ≤ a * 1 + a * ofNat n := add_le_add (mul_one a).ge (le_refl _)
    _ ≤ a * (1 + ofNat n) := (mul_add a 1 _).ge
    _ ≤ a * ofNat (n + 1) := mul_le_mul_left a (ofNat_add n 1).ge

/-- `a * n ≤ a * ω` for finite `n`. -/
private theorem mul_ofNat_le_mul_omega (a : Ordinal.{u}) (n : Nat) : a * ofNat n ≤ a * ω := by
  rw [mul_unfold a ω]
  exact le_trans (le_add_right _ a) (sup_le (fun i : (ω : Ordinal.{u}).Carrier => a * ω i + a) ⟨n⟩)

/-- Rocq: `Cantor.additively_closed_mul_omega`. -/
theorem additively_closed_mul_omega (x : Ordinal.{u}) : AdditivelyClosed (x * ω) := by
  intro a b ha hb
  rw [mul_unfold x ω] at ha hb
  obtain ⟨⟨i⟩, ha⟩ := sup_lt ha
  obtain ⟨⟨j⟩, hb⟩ := sup_lt hb
  refine lt_of_lt_of_le (add_lt_add_left a hb) ?_
  calc a + (x * ofNat j + x) ≤ (x * ofNat i + x) + (x * ofNat j + x) :=
        add_le_add (le_of_lt ha) (le_refl _)
    _ ≤ x * ofNat (i + 1) + x * ofNat (j + 1) :=
        add_le_add (mul_succ x (ofNat i)).ge (mul_succ x (ofNat j)).ge
    _ ≤ x * (ofNat (i + 1) + ofNat (j + 1)) := (mul_add x _ _).ge
    _ ≤ x * ofNat ((j + 1) + (i + 1)) := mul_le_mul_left x (ofNat_add (j + 1) (i + 1)).ge
    _ ≤ x * ω := mul_ofNat_le_mul_omega x _

/-- Rocq: `Cantor.additively_closed_one`. -/
theorem additively_closed_one : AdditivelyClosed (1 : Ordinal.{u}) := fun a b ha hb =>
  let ⟨_, h⟩ := lt_elim ha
  lt_of_le_of_lt (le_trans (add_le_add h (le_refl b)) (zero_add b).le) hb

/-- Rocq: `Cantor.additively_closed_omega`. -/
theorem additively_closed_omega : AdditivelyClosed (ω : Ordinal.{u}) := fun a b ha hb =>
  lt_of_lt_of_le (additively_closed_mul_omega 1 a b (lt_of_lt_of_le ha (one_mul ω).ge)
    (lt_of_lt_of_le hb (one_mul ω).ge)) (one_mul ω).le

/-- `ω ^ c` bounds `ω ^ (c i) * ω` for each index `i` of `c`. -/
theorem pow_index_mul_omega_le (c : Ordinal.{u}) (i : c) : ω ^ c i * ω ≤ ω ^ c := by
  rw [pow_unfold ω c]
  exact le_trans (sup_le (fun i : c => ω ^ c i * ω) i) (lub_le2 _ _)

/-- `ω ≤ ω ^ c` when `0 < c`. -/
theorem omega_le_pow_omega {c : Ordinal.{u}} (h₀ : 0 < c) : ω ≤ ω ^ c := by
  obtain ⟨c₀, _⟩ := lt_elim h₀
  exact le_trans (le_trans (one_mul ω).ge (mul_le_mul_right ω (succ_least (pow_pos ω _))))
    (pow_index_mul_omega_le c c₀)

/-- Rocq: `Cantor.expOmega_additively_closed`. -/
theorem powOmega_additively_closed {c : Ordinal.{u}} (hc : Complete c) :
    AdditivelyClosed (ω ^ c) := by
  intro a b ha hb
  have ha' := ha
  have hb' := hb
  rw [pow_unfold] at ha hb
  match lub_lt ha with
  | .inl ha =>
    obtain ⟨_, h⟩ := lt_elim ha
    exact lt_of_le_of_lt (le_trans (add_le_add h (le_refl b)) (zero_add b).le) hb'
  | .inr ha =>
    match lub_lt hb with
    | .inl hb =>
      obtain ⟨_, h⟩ := lt_elim hb
      exact lt_of_le_of_lt (le_trans (add_le_add (le_refl a) h) (add_zero a).le) ha'
    | .inr hb =>
      obtain ⟨ca, ha⟩ := sup_lt ha
      obtain ⟨cb, hb⟩ := sup_lt hb
      obtain ⟨c', h₁, h₂⟩ := complete_directed hc ca cb
      exact lt_of_lt_of_le (additively_closed_mul_omega _ a b
          (lt_of_lt_of_le ha (mul_le_mul_right ω (pow_le_pow_right ω h₁)))
          (lt_of_lt_of_le hb (mul_le_mul_right ω (pow_le_pow_right ω h₂))))
        (pow_index_mul_omega_le c c')

/-- Rocq: `Cantor.epslion_additively_closed` (sic). -/
theorem epsilon_additively_closed {x : Ordinal.{u}} (hx : Complete x) :
    AdditivelyClosed (ε x) := fun a b ha hb =>
  lt_of_lt_of_le (powOmega_additively_closed (ε_complete hx) a b
      (lt_of_lt_of_le ha (ε_fixpoint x).le) (lt_of_lt_of_le hb (ε_fixpoint x).le))
    (ε_fixpoint x).ge

/-- Rocq: `Cantor.expOrd_add_collapse`. -/
theorem pow_add_collapse {b c : Ordinal.{u}} (hc : Complete c) (h : b < c) :
    ω ^ b + ω ^ c ≤ ω ^ c :=
  additively_closed_collapse (powOmega_additively_closed hc) (pow_lt_pow_right omega_gt1 h)

/-- Rocq: `Cantor.mul_omega_collapse`. -/
theorem mul_omega_collapse (a b : Ordinal.{u}) (n : (ω : Ordinal.{u}).Carrier) (h : b ≤ a * ω n) :
    (a + b) * ω ≤ a * ω := by
  have hN : a + b ≤ a * ofNat (n.down + 1) :=
    le_trans (add_le_add (le_refl a) h) (add_mul_ofNat_le a n.down)
  rw [mul_unfold (a + b) ω]
  refine sup_least fun ⟨m⟩ => ?_
  show (a + b) * ofNat m + (a + b) ≤ a * ω
  calc (a + b) * ofNat m + (a + b) ≤ a * ofNat (n.down + 1) * ofNat m + a * ofNat (n.down + 1) :=
        add_le_add (mul_le_mul_right _ hN) hN
    _ ≤ a * (ofNat (n.down + 1) * ofNat m) + a * ofNat (n.down + 1) :=
        add_le_add (mul_assoc _ _ _).ge (le_refl _)
    _ ≤ a * (ofNat (n.down + 1) * ofNat m + ofNat (n.down + 1)) := (mul_add a _ _).ge
    _ ≤ a * (ofNat (m * (n.down + 1)) + ofNat (n.down + 1)) :=
        mul_le_mul_left a (add_le_add (ofNat_mul m _).ge (le_refl _))
    _ ≤ a * ofNat ((n.down + 1) + m * (n.down + 1)) := mul_le_mul_left a (ofNat_add _ _).ge
    _ ≤ a * ω := mul_ofNat_le_mul_omega a _

/-- Rocq: `Cantor.expOrd_omega_collapse`. -/
theorem pow_omega_collapse (a b : Ordinal.{u}) (n : (ω : Ordinal.{u}).Carrier) (h : b ≤ a * ω n) :
    ∀ c : Ordinal.{u}, Complete c → 0 < c → (a + b) * ω ^ c ≤ a * ω ^ c
  | c, hc, h₀ => by
    have hcollapse : (a + b) * ω ≤ a * ω ^ c :=
      le_trans (mul_omega_collapse a b n h) (mul_le_mul_left a (omega_le_pow_omega h₀))
    obtain ⟨c₀, _⟩ := lt_elim h₀
    rw [pow_unfold ω c]
    refine le_trans (mul_lub _ _ _).le (lub_least ?_ ?_)
    · exact le_trans (le_trans (mul_one _).le (le_trans (mul_one _).ge
        (mul_le_mul_left _ (le_of_lt omega_gt1)))) (by rw [← pow_unfold ω c]; exact hcollapse)
    · refine le_trans (mul_continuous (a + b) _ (fun i : c => ω ^ c i * ω) c₀)
        (sup_least fun i => ?_)
      rw [← pow_unfold ω c]
      match complete_zeroDec (complete_subord hc i) with
      | .inl hz =>
        refine le_trans (mul_le_mul_left _ ?_) hcollapse
        exact le_trans (mul_le_mul_right ω (le_trans (pow_le_pow_right ω hz) (pow_zero ω).le))
          (one_mul ω).le
      | .inr hp =>
        calc (a + b) * (ω ^ c i * ω) ≤ (a + b) * ω ^ c i * ω := (mul_assoc _ _ _).le
          _ ≤ a * ω ^ c i * ω :=
              mul_le_mul_right ω (pow_omega_collapse a b n h (c i) (complete_subord hc i) hp)
          _ ≤ a * (ω ^ c i * ω) := (mul_assoc _ _ _).ge
          _ ≤ a * ω ^ c := mul_le_mul_left a (pow_index_mul_omega_le c i)
termination_by c => c
decreasing_by exact index_lt c i

/-- Rocq: `Cantor.omegaMul_closed`. -/
theorem omegaMul_closed {x y : Ordinal.{u}} (hx : x < ω) (hy : y < ω) : x * y < ω := by
  obtain ⟨⟨i⟩, hi⟩ := lt_elim hx
  obtain ⟨⟨j⟩, hj⟩ := lt_elim hy
  exact lt_of_le_of_lt (le_trans (mul_le_mul hi hj) (ofNat_mul j i).ge)
    (index_lt ω ⟨j * i⟩)

/-- Finite powers of finite ordinals are finite. -/
private theorem ofNat_pow_lt_omega {x : Ordinal.{u}} (hx : x < ω) (h₀ : 0 < x) :
    ∀ i : Nat, x ^ ofNat.{u} i < ω
  | 0 => lt_of_le_of_lt (pow_zero x).le omega_gt1
  | i + 1 => lt_of_le_of_lt (pow_succ (ofNat i) h₀).le (omegaMul_closed (ofNat_pow_lt_omega hx h₀ i) hx)

/-- Rocq: `Cantor.expNatToOmega`. -/
theorem expNatToOmega (n : (ω : Ordinal.{u}).Carrier) (hn : 1 < ω n) : ω n ^ (ω : Ordinal.{u}) ≈ ω := by
  have h₀ : 0 < ω n := lt_trans (succ_lt 0) hn
  refine equiv_intro ?_ (increasing_inflationary (fun _ _ h => pow_lt_pow_right hn h) ω)
  rw [pow_unfold]
  exact lub_least (le_of_lt omega_gt1) (sup_least fun i => le_of_lt
    (omegaMul_closed (ofNat_pow_lt_omega (index_lt ω n) h₀ i.down) (index_lt ω n)))

/-- Rocq: `Cantor.expNatToOmegaPow`. -/
theorem expNatToOmegaPow (n : (ω : Ordinal.{u}).Carrier) (e : Ordinal.{u}) (hn : 1 < ω n) :
    ω n ^ (ω ^ (1 + e)) ≈ ω ^ (ω ^ e) :=
  equiv_trans (pow_congr (equiv_refl _) (equiv_trans (pow_add ω 1 e)
      (mul_congr (pow_one' omega_gt0) (equiv_refl _))))
    (equiv_trans (pow_mul _ ω _) (pow_congr (expNatToOmega n hn) (equiv_refl _)))

/-- Rocq: `Cantor.expNatToOmegaInf`. -/
theorem expNatToOmegaInf (n : (ω : Ordinal.{u}).Carrier) (e : Ordinal.{u}) (hn : 1 < ω n)
    (he : e ≈ 1 + e) : ω n ^ (ω ^ e) ≈ ω ^ (ω ^ e) :=
  equiv_trans (pow_congr (equiv_refl _) (pow_congr (equiv_refl _) he)) (expNatToOmegaPow n e hn)

/-- Rocq: `Cantor.expToOmega_collapse`. -/
theorem expToOmega_collapse (a b : Ordinal.{u}) (n : (ω : Ordinal.{u}).Carrier)
    (ha : ω n + 1 ≤ a) (hb : b ≤ a * ω n) : (a + b) ^ (ω : Ordinal.{u}) ≤ a ^ (ω : Ordinal.{u}) := by
  have hn1 : ofNat (n.down + 1) ≤ a := le_trans (succ_le_add_one _) ha
  have ha₀ : 0 < a := lt_of_lt_of_le (lt_of_le_of_lt (zero_least _) (succ_lt (ofNat n.down))) hn1
  have hab₀ : 0 < a + b := lt_of_lt_of_le ha₀ (le_add_right a b)
  have hab : a + b ≤ a * a :=
    le_trans (le_trans (add_le_add (le_refl a) hb) (add_mul_ofNat_le a n.down))
      (mul_le_mul_left a hn1)
  have claim : ∀ i : Nat, (a + b) ^ ofNat.{u} i ≤ a ^ ofNat.{u} (2 * i) := by
    intro i
    induction i with
    | zero => exact le_trans (pow_zero _).le (pow_zero _).ge
    | succ i ih =>
      calc (a + b) ^ ofNat.{u} (i + 1) ≤ (a + b) ^ ofNat.{u} i * (a + b) := (pow_succ _ hab₀).le
        _ ≤ a ^ ofNat.{u} (2 * i) * (a * a) := mul_le_mul ih hab
        _ ≤ a ^ ofNat.{u} (2 * i) * a * a := (mul_assoc _ _ _).le
        _ ≤ a ^ ofNat.{u} (2 * i + 1) * a := mul_le_mul_right a (pow_succ _ ha₀).ge
        _ ≤ a ^ ofNat.{u} (2 * (i + 1)) := (pow_succ _ ha₀).ge
  rw [pow_unfold (a + b) ω]
  refine lub_least (succ_least (pow_pos _ _)) (sup_least fun ⟨i⟩ => ?_)
  exact le_trans (pow_succ (ofNat i) hab₀).ge
    (le_trans (claim (i + 1)) (pow_le_pow_right a (index_le ω ⟨2 * (i + 1)⟩)))

/-- Rocq: `Cantor.expToOmega_collapse_tower`. -/
theorem expToOmega_collapse_tower (a b : Ordinal.{u}) (n : (ω : Ordinal.{u}).Carrier)
    (ha : ω n + 1 ≤ a) (hb : b ≤ a * ω n) :
    ∀ c : Ordinal.{u}, Complete c → 0 < c → (a + b) ^ (ω ^ c) ≤ a ^ (ω ^ c)
  | c, hc, h₀ => by
    have hω : (a + b) ^ (ω : Ordinal.{u}) ≤ a ^ (ω ^ c) :=
      le_trans (expToOmega_collapse a b n ha hb) (pow_le_pow_right a (omega_le_pow_omega h₀))
    obtain ⟨c₀, _⟩ := lt_elim h₀
    rw [pow_unfold ω c]
    refine le_trans (pow_lub _ _ _).le (lub_least ?_ ?_)
    · exact le_trans (pow_le_pow_right _ (le_of_lt omega_gt1)) (by rw [← pow_unfold ω c]; exact hω)
    · refine le_trans (pow_continuous (a + b) _ (fun i : c => ω ^ c i * ω) c₀)
        (sup_least fun i => ?_)
      rw [← pow_unfold ω c]
      match complete_zeroDec (complete_subord hc i) with
      | .inl hz =>
        refine le_trans (pow_le_pow_right _ ?_) hω
        exact le_trans (mul_le_mul_right ω (le_trans (pow_le_pow_right ω hz) (pow_zero ω).le))
          (one_mul ω).le
      | .inr hp =>
        calc (a + b) ^ (ω ^ c i * ω) ≤ ((a + b) ^ (ω ^ c i)) ^ (ω : Ordinal.{u}) := (pow_mul _ _ _).le
          _ ≤ (a ^ (ω ^ c i)) ^ (ω : Ordinal.{u}) :=
              pow_le_pow_left (expToOmega_collapse_tower a b n ha hb (c i) (complete_subord hc i) hp) _
          _ ≤ a ^ (ω ^ c i * ω) := (pow_mul _ _ _).ge
          _ ≤ a ^ (ω ^ c) := pow_le_pow_right a (pow_index_mul_omega_le c i)
termination_by c => c
decreasing_by exact index_lt c i

/-! ## Truth ordinals and `ω`-exponentiation -/

/-- Rocq: `Cantor.expOrd_truth_ord_complete`. -/
theorem powOmega_truthOrd_complete (P : Prop) : Complete (ω ^ truthOrd.{u} P) := by
  have hm : Complete ((ω : Ordinal.{u}) ^ (0 : Ordinal.{u}) * ω) :=
    mul_complete (pow_complete omega_gt0 omega_complete zero_complete) ω omega_complete
  rw [pow_unfold]
  refine Complete.intro ?_ (.inl ⟨.inl PUnit.unit⟩) ?_
  · rintro (_ | ⟨hp, o⟩) (_ | ⟨hp', o'⟩)
    · exact ⟨.inl PUnit.unit, le_refl _, le_refl _⟩
    · exact ⟨.inr ⟨hp', o'⟩, zero_least _, le_refl _⟩
    · exact ⟨.inr ⟨hp, o⟩, le_refl _, zero_least _⟩
    · obtain ⟨o'', h₁, h₂⟩ := complete_directed hm o o'
      exact ⟨.inr ⟨hp, o''⟩, h₁, h₂⟩
  · rintro (_ | ⟨_, o⟩)
    · exact zero_complete
    · exact complete_subord hm o

/-- Rocq: `Cantor.truth_ord'_expOmega`. -/
theorem truthOrd'_powOmega (P : Prop) : truthOrd'.{u} P ≈ ω ^ truthOrd.{u} P := by
  refine equiv_intro (sup_least fun n => lub_least (succ_least (pow_pos _ _)) (le_intro fun hp => ?_)) ?_
  · refine lt_of_lt_of_le (index_lt ω n) ?_
    rw [pow_unfold]
    exact le_trans (le_trans (one_mul ω).ge (mul_le_mul_right ω (succ_least (pow_pos ω 0))))
      (le_trans (sup_le (fun i : (truthOrd.{u} P).Carrier => ω ^ truthOrd.{u} P i * ω) hp)
        (lub_le2 _ _))
  · rw [pow_unfold]
    refine lub_least (le_trans (lub_le1 1 _) (sup_le (fun n : ULift.{u} Nat =>
      1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down) ⟨0⟩)) (sup_least fun hp => ?_)
    exact le_trans (le_trans (mul_le_mul_right ω (pow_zero ω).le) (one_mul ω).le)
      (truthOrd'_true hp.down.down).ge

/-- Classically, `ω ^ ·` enumerates the nonzero additively closed ordinals.
Rocq: `Cantor.additively_closed_enumerate`. -/
theorem additively_closed_enumerate (em : ExcludedMiddle) :
    Enumerates (fun x : Ordinal.{u} => ω ^ x) fun x => 0 < x ∧ AdditivelyClosed x where
  included x := ⟨pow_pos ω x, powOmega_additively_closed (ord_complete em x)⟩
  monotone _ _ h := pow_le_pow_right ω h
  increasing _ _ h := pow_lt_pow_right omega_gt1 h
  least x z := fun ⟨hz₁, hz₂⟩ h => by
    rw [pow_unfold]
    refine lub_least (succ_least hz₁) (sup_least fun i => ?_)
    rw [mul_unfold]
    refine sup_least fun ⟨j⟩ => le_of_lt ?_
    show ω ^ x i * ofNat j + ω ^ x i < z
    induction j with
    | zero => exact lt_of_le_of_lt (le_trans (add_le_add (mul_zero _).le (le_refl _))
        (zero_add _).le) (h (x i) (index_lt x i))
    | succ j ih =>
      exact lt_of_le_of_lt (add_le_add (mul_succ _ _).le (le_refl _))
        (hz₂ _ _ ih (h (x i) (index_lt x i)))

/-- Rocq: `Cantor.additively_closed_expOrd`. -/
theorem additively_closed_powOmega (em : ExcludedMiddle) {x : Ordinal.{u}} (h₀ : 0 < x)
    (hx : AdditivelyClosed x) : ∃ c : Ordinal.{u}, ω ^ c ≈ x :=
  enumerates_surjective em (additively_closed_enumerate em) x ⟨h₀, hx⟩

/-! ## Cantor normal forms -/

/-- `ls` is a non-increasing list of exponents, each at most `x`.
Rocq: `Cantor.cantor_sequence`. -/
def CantorSequence (x : Ordinal.{u}) : List Ordinal.{u} → Prop
  | [] => True
  | y :: ys => y ≤ x ∧ CantorSequence y ys

/-- The ordinal denoted by a list of exponents: `ω ^ y₁ + ω ^ y₂ + ⋯`.
Rocq: `Cantor.cantor_denote`. -/
def cantorDenote : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | y :: ys => ω ^ y + cantorDenote ys

theorem CantorSequence.mono {x x' : Ordinal.{u}} (h : x ≤ x') :
    ∀ {ls : List Ordinal.{u}}, CantorSequence x ls → CantorSequence x' ls
  | [], _ => trivial
  | _ :: _, ⟨hy, hys⟩ => ⟨le_trans hy h, hys⟩

/-- Rocq: `Cantor.cantor_normal_add`. -/
theorem cantor_normal_add (em : ExcludedMiddle) :
    ∀ (x : Ordinal.{u}) (xs : List Ordinal.{u}) (y : Ordinal.{u}) (ys : List Ordinal.{u}),
      CantorSequence x xs → CantorSequence y ys →
      ∃ zs, CantorSequence (x ⊔ y) zs ∧ cantorDenote zs ≈ cantorDenote xs + cantorDenote ys
  | x, [], y, ys, _, hys => ⟨ys, hys.mono (lub_le2 x y), equiv_symm (zero_add _)⟩
  | x, a :: xs, y, ys, ⟨ha, hxs⟩, hys => by
    obtain ⟨zs, hzs₁, hzs₂⟩ := cantor_normal_add em a xs y ys hxs hys
    have hassoc : cantorDenote (a :: xs) + cantorDenote ys ≈
        ω ^ a + (cantorDenote xs + cantorDenote ys) := equiv_symm (add_assoc _ _ _)
    match zs, hzs₁, hzs₂ with
    | [], _, hzs₂ =>
      exact ⟨[a], ⟨le_trans ha (lub_le1 x y), trivial⟩,
        equiv_trans (add_congr (equiv_refl _) hzs₂) (equiv_symm hassoc)⟩
    | o :: zs, ⟨ho, hzs⟩, hzs₂ =>
      match order_total em o a with
      | .inl hoa =>
        exact ⟨a :: o :: zs, ⟨le_trans ha (lub_le1 x y), hoa, hzs⟩,
          equiv_trans (add_congr (equiv_refl _) hzs₂) (equiv_symm hassoc)⟩
      | .inr hao =>
        refine ⟨o :: zs, ⟨le_trans ho (lub_monotone ha (le_refl y)), hzs⟩, ?_⟩
        refine equiv_trans ?_ (equiv_trans (add_congr (equiv_refl _) hzs₂) (equiv_symm hassoc))
        show ω ^ o + cantorDenote zs ≈ ω ^ a + (ω ^ o + cantorDenote zs)
        refine equiv_trans ?_ (equiv_symm (add_assoc _ _ _))
        exact add_congr (equiv_intro (le_add_left _ _)
          (pow_add_collapse (ord_complete em o) hao)) (equiv_refl _)

/-- Elementwise equivalence of lists of exponents. Rocq: `Cantor.cantor_eq`. -/
def CantorEq : List Ordinal.{u} → List Ordinal.{u} → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | x :: xs, y :: ys => x ≈ y ∧ CantorEq xs ys

private theorem one_le_cantorDenote_cons (o : Ordinal.{u}) (ys : List Ordinal.{u}) :
    1 ≤ cantorDenote (o :: ys) :=
  le_trans (succ_least (pow_pos ω o)) (le_add_right _ _)

theorem cantorDenote_lt (em : ExcludedMiddle) :
    ∀ (ys : List Ordinal.{u}) (o a : Ordinal.{u}), CantorSequence o ys → o < a →
      cantorDenote ys < ω ^ a
  | [], _, a, _, _ => pow_pos ω a
  | o' :: ys, _, a, ⟨ho', hys⟩, hoa =>
    powOmega_additively_closed (ord_complete em a) _ _
      (pow_lt_pow_right omega_gt1 (lt_of_le_of_lt ho' hoa))
      (cantorDenote_lt em ys o' a hys (lt_of_le_of_lt ho' hoa))

/-- Classically, Cantor normal forms are unique.
Rocq: `Cantor.cantor_decomposition_unique`. -/
theorem cantor_decomposition_unique (em : ExcludedMiddle) :
    ∀ (x y : Ordinal.{u}) (xs ys : List Ordinal.{u}), CantorSequence x xs → CantorSequence y ys →
      cantorDenote xs ≈ cantorDenote ys → CantorEq xs ys
  | _, _, [], [], _, _, _ => trivial
  | _, _, [], o :: ys, _, _, h =>
    lt_irrefl 0 (lt_of_lt_of_le (succ_lt 0) (le_trans (one_le_cantorDenote_cons o ys) h.ge))
  | _, _, a :: xs, [], _, _, h =>
    lt_irrefl 0 (lt_of_lt_of_le (succ_lt 0) (le_trans (one_le_cantorDenote_cons a xs) h.le))
  | _, _, a :: xs, o :: ys, ⟨_, hxs⟩, ⟨_, hys⟩, h => by
    have contra : ∀ (p q : Ordinal.{u}) (ps qs : List Ordinal.{u}), CantorSequence q qs → q < p →
        ω ^ p + cantorDenote ps ≈ ω ^ q + cantorDenote qs → False :=
      fun p q ps qs hqs hqp h' => lt_irrefl (ω ^ p) (lt_of_le_of_lt
        (le_trans (le_add_right _ _) h'.le)
        (powOmega_additively_closed (ord_complete em p) _ _ (pow_lt_pow_right omega_gt1 hqp)
          (cantorDenote_lt em qs q p hqs hqp)))
    match order_total em o a with
    | .inl hoa =>
      match order_total em a o with
      | .inl hao =>
        exact ⟨equiv_intro hao hoa, cantor_decomposition_unique em a o xs ys hxs hys
          (add_cancel h (pow_congr (equiv_refl ω) (equiv_intro hao hoa)))⟩
      | .inr hoa' => exact (contra a o xs ys hys hoa' h).elim
    | .inr hao => exact (contra o a ys xs hxs hao (equiv_symm h)).elim

/-- Classically, every ordinal has a Cantor normal form.
Rocq: `Cantor.cantor_decomposition`. -/
theorem cantor_decomposition (em : ExcludedMiddle) (x : Ordinal.{u}) :
    ∃ ls, CantorSequence x ls ∧ cantorDenote ls ≈ x := by
  induction x using ltRec with
  | ind x ih =>
    match em (∃ a b, a < x ∧ b < x ∧ a + b ≈ x) with
    | .inl ⟨a, b, ha, hb, hab⟩ =>
      obtain ⟨ls₁, h₁, h₁'⟩ := ih a ha
      obtain ⟨ls₂, h₂, h₂'⟩ := ih b hb
      obtain ⟨ls, hls, hls'⟩ := cantor_normal_add em a ls₁ b ls₂ h₁ h₂
      exact ⟨ls, hls.mono (lub_least (le_of_lt ha) (le_of_lt hb)),
        equiv_trans hls' (equiv_trans (add_congr h₁' h₂') hab)⟩
    | .inr hn =>
      match order_total em x 0 with
      | .inl hx => exact ⟨[], trivial, equiv_intro (zero_least x) hx⟩
      | .inr hx₀ =>
        have hclosed : AdditivelyClosed x := fun a b ha hb => by
          match order_total em x (a + b) with
          | .inr h => exact h
          | .inl hxab =>
            obtain ⟨b', ⟨hb'x, hxb'⟩, hleast⟩ :=
              ord_well_ordered em (fun b' => b' < x ∧ x ≤ a + b') b ⟨hb, hxab⟩
            refine (hn ⟨a, b', ha, hb'x, equiv_intro ?_ hxb'⟩).elim
            match order_total em (a + b') x with
            | .inl h => exact h
            | .inr h =>
              rw [add_unfold] at h
              match lub_lt h with
              | .inl h => exact (lt_irrefl a (lt_trans ha h)).elim
              | .inr h =>
                obtain ⟨q, hq⟩ := sup_lt h
                obtain ⟨_, hq⟩ := lt_elim hq
                have := hleast (b' q) ⟨lt_trans (index_lt b' q) hb'x, hq⟩
                exact (lt_irrefl _ (lt_of_le_of_lt this (index_lt b' q))).elim
        obtain ⟨c, hc⟩ := additively_closed_powOmega em hx₀ hclosed
        exact ⟨[c], ⟨le_trans (increasing_inflationary (fun _ _ h => pow_lt_pow_right omega_gt1 h) c)
          hc.le, trivial⟩, equiv_trans (add_zero _) hc⟩

/-- The existence of Cantor normal forms implies the excluded middle.
Rocq: `Cantor.cantor_decomposition_is_classical`. -/
theorem cantor_decomposition_is_classical
    (h : ∀ x : Ordinal.{u}, ∃ ls, CantorSequence x ls ∧ cantorDenote ls ≈ x) : ExcludedMiddle :=
  fun P =>
    match h (truthOrd P) with
    | ⟨[], _, hd⟩ => .inr fun hp =>
      lt_irrefl 0 (lt_of_lt_of_le (lt_intro (show (truthOrd.{u} P).Carrier from ⟨⟨hp⟩⟩)
        (le_refl _)) hd.ge)
    | ⟨o :: ls, _, hd⟩ =>
      .inl ((lt_elim (le_elim (le_trans (one_le_cantorDenote_cons o ls) hd.le) PUnit.unit)).elim
        fun ⟨⟨hp⟩⟩ _ => hp)

private theorem cantorDenote_lt_omega :
    ∀ (ls : List Ordinal.{u}) (o : Ordinal.{u}), CantorSequence o ls → o ≤ 0 → cantorDenote ls < ω
  | [], _, _, _ => omega_gt0
  | y :: ys, _, ⟨hy, hys⟩, ho =>
    additively_closed_omega _ _
      (lt_of_le_of_lt (le_trans (pow_le_pow_right ω (le_trans hy ho)) (pow_zero ω).le) omega_gt1)
      (cantorDenote_lt_omega ys y hys (le_trans hy ho))

/-- The existence of Cantor normal forms, even only for complete ordinals and
with complete exponents, implies the excluded middle.
Rocq: `Cantor.cantor_decomposition_is_classical_for_complete_ordinals`. -/
theorem cantor_decomposition_is_classical_for_complete_ordinals
    (h : ∀ x : Ordinal.{u}, Complete x → ∃ ls : List Ordinal.{u},
      (∀ y, y ∈ ls → Complete y) ∧ CantorSequence x ls ∧ cantorDenote ls ≈ x) :
    ExcludedMiddle := fun P => by
  have h1 : 1 ≤ truthOrd'.{u} P := le_trans (lub_le1 1 _) (sup_le (fun n : ULift.{u} Nat =>
    1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down) ⟨0⟩)
  obtain ⟨ls, hcomp, hseq, hd⟩ := h (truthOrd' P) (truthOrd'_complete P)
  match ls, hcomp, hseq, hd with
  | [], _, _, hd => exact (lt_irrefl 0 (le_elim (le_trans h1 hd.ge) PUnit.unit)).elim
  | o :: ls, hcomp, ⟨_, hls⟩, hd =>
    match complete_zeroDec (hcomp o (.head ls)) with
    | .inl ho =>
      refine .inr fun hp => lt_irrefl (ω : Ordinal.{u}) ?_
      refine lt_of_le_of_lt (le_trans (truthOrd'_true hp).ge hd.ge) ?_
      exact additively_closed_omega _ _
        (lt_of_le_of_lt (le_trans (pow_le_pow_right ω ho) (pow_zero ω).le) omega_gt1)
        (cantorDenote_lt_omega ls o hls ho)
    | .inr ho =>
      have hω : ω ≤ truthOrd'.{u} P :=
        le_trans (le_trans (omega_le_pow_omega ho) (le_add_right _ _)) hd.le
      obtain ⟨⟨n⟩, hn⟩ := sup_lt (lt_of_lt_of_le (index_lt ω ⟨1⟩) hω)
      match lub_lt hn with
      | .inl h => exact (lt_irrefl _ h).elim
      | .inr h => exact .inl ((lt_elim h).elim fun ⟨⟨hp⟩⟩ _ => hp)

end Ordinal

end ConstructiveOrdinals
