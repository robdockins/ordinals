import ConstructiveOrdinals.Analysis.OmegaLogic

/-!
# Embedding Peano arithmetic in the ω-logic

Port of `Ordinal/Analysis/Embedding.v`.

A derivation of `Γ ⊢ A` in `PeanoArith` becomes, for every assignment `σ` of
numerals below the control `n`, an ω-derivation of the sequent `A⟨σ⟩, ¬Γ⟨σ⟩`
(`embed`), of height `ω^3·k` and fixed cut rank, for `n` large enough. Most
rules become one or two inferences with a cut; the induction rule becomes an
ω-rule whose `i`-th premise chains `i` cuts. Witnesses given by terms are
raised to the control with `OD.up`, at a cost `ω^2·k` that bounds the value of
the term (`term_bound`). Bounded formulas are decided: a true one is an axiom,
and a false one is deleted from a premise.

Lean notes:

- `teval_occ01` and `teval_occ0` are in `OmegaLogic`.
- Arithmetic is done by hand, since `omega` uses `propext`; the thresholds
  on the control are nested maxima.
-/

namespace ConstructiveOrdinals.Embedding

open Ordinal PeanoArith ATerm Form Hardy VNotation VForm OmegaLogic

/-! ## Arithmetic helpers -/

theorem max_le_l {a b c : Nat} (h : Nat.max a b ≤ c) : a ≤ c := Nat.le_trans (Nat.le_max_left a b) h
theorem max_le_r {a b c : Nat} (h : Nat.max a b ≤ c) : b ≤ c := Nat.le_trans (Nat.le_max_right a b) h

theorem two_mul_succ (y : Nat) : y + 1 + 1 + y = 2 * (y + 1) := by
  rw [Nat.two_mul, Nat.add_assoc (y + 1) 1 y, Nat.add_comm 1 y]

/-! ## Small ordinals and their Hardy functions -/

/-- Rocq: `Analysis.Embedding.e1`. -/
def e1 : VForm := V Z Z
/-- Rocq: `Analysis.Embedding.e2`. -/
def e2 : VForm := V Z e1
/-- Rocq: `Analysis.Embedding.e3`. -/
def e3 : VForm := V Z e2

/-- Rocq: `Analysis.Embedding.fin`. -/
def fin (c : Nat) : VForm := vrep c Z Z

/-- Rocq: `Analysis.Embedding.fin_S`. -/
theorem fin_S (c : Nat) : fin (c + 1) = vcat (fin c) e1 := by
  unfold fin; rw [vrep_S_r, vrep_vcat]; rfl

/-- Rocq: `Analysis.Embedding.Pn_fin`. -/
theorem Pn_fin (n c : Nat) : Pn n (fin (c + 1)) (fin c) := by
  rw [fin_S]
  have h := Pn_vcat (Pn.one (n := n)) (fin c)
  rw [vcat_Z] at h
  exact h

/-- Rocq: `Analysis.Embedding.hardy_fin`. -/
theorem hardy_fin : ∀ (c x : Nat), Hardy (fin c) x (x + c)
  | 0, x => .z x
  | c + 1, x => .p _ _ _ _ (Pn_fin x c) (by
      have h := hardy_fin c (x + 1)
      rw [Nat.add_right_comm] at h
      exact h)

/-- Rocq: `Analysis.Embedding.Pn_omega`. -/
theorem Pn_omega (n : Nat) : Pn n (V e1 Z) (fin (n - 1)) := .exp e1 Z Z .one .one

/-- Rocq: `Analysis.Embedding.Pn_e2`. -/
theorem Pn_e2 (n : Nat) : Pn n e2 e1 := .tail Z (V Z Z) Z .one

/-- Rocq: `Analysis.Embedding.Pn_omega2`. -/
theorem Pn_omega2 (n : Nat) : Pn n (V e2 Z) (vrep (n - 1) e1 (fin (n - 1))) := .exp _ _ _ (Pn_e2 n) (Pn_omega n)

/-- Rocq: `Analysis.Embedding.hardy_omega_k`. -/
theorem hardy_omega_k : ∀ (j x : Nat), 1 ≤ x → Hardy (vrep j e1 Z) x (2 ^ j * x)
  | 0, x, _ => by rw [Nat.pow_zero, Nat.one_mul]; exact .z x
  | j + 1, x, hx => by
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, (Nat.sub_one_add_one (Nat.ne_of_gt hx)).symm⟩
    rw [vrep_S_r, vrep_vcat]
    refine .p _ _ _ _ (Pn_vcat (Pn_omega (y + 1)) _) ?_
    have h := hardy_omega_k j (y + 1 + 1 + y) (Nat.le_trans (Nat.le_add_left 1 (y + 1)) (Nat.le_add_right _ y))
    have e : 2 ^ j * (y + 1 + 1 + y) = 2 ^ (j + 1) * (y + 1) := by
      rw [two_mul_succ, ← Nat.mul_assoc, ← Nat.pow_succ]
    rw [e] at h
    exact hardy_vcat _ (hardy_fin y (y + 1 + 1)) h

/-- Rocq: `Analysis.Embedding.hardy_omega2`. -/
theorem hardy_omega2 (x : Nat) (hx : 1 ≤ x) : Hardy (V e2 Z) x (2 ^ x * x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, (Nat.sub_one_add_one (Nat.ne_of_gt hx)).symm⟩
  refine .p _ _ _ _ (Pn_omega2 (y + 1)) ?_
  show Hardy (vrep y e1 (fin y)) (y + 1 + 1) _
  rw [vrep_vcat]
  have h := hardy_omega_k y (y + 1 + 1 + y) (Nat.le_trans (Nat.le_add_left 1 (y + 1)) (Nat.le_add_right _ y))
  have e : 2 ^ y * (y + 1 + 1 + y) = 2 ^ (y + 1) * (y + 1) := by
    rw [two_mul_succ, ← Nat.mul_assoc, ← Nat.pow_succ]
  rw [e] at h
  exact hardy_vcat _ (hardy_fin y (y + 1 + 1)) h

/-- Rocq: `Analysis.Embedding.pow2_ge`. -/
theorem pow2_ge : ∀ x : Nat, x + 1 ≤ 2 ^ x
  | 0 => Nat.le_refl 1
  | x + 1 => by
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.add_le_add (pow2_ge x) (Nat.le_trans (Nat.le_add_left 1 x) (pow2_ge x))

/-- Rocq: `Analysis.Embedding.hardy_omega2_ge`. -/
theorem hardy_omega2_ge {x h : Nat} (hx : 1 ≤ x) (H : Hardy (V e2 Z) x h) : x * (x + 1) ≤ h := by
  rw [hardy_fun H (hardy_omega2 x hx), Nat.mul_comm]
  exact Nat.mul_le_mul_right x (pow2_ge x)

/-- Rocq: `Analysis.Embedding.om2`. -/
def om2 (k : Nat) : VForm := vrep k e2 Z

/-- Rocq: `Analysis.Embedding.hardy_om2_add`. -/
theorem hardy_om2_add (a b : Nat) {n h : Nat} (H : Hardy (om2 (a + b)) n h) :
    ∃ m, Hardy (om2 b) n m ∧ Hardy (om2 a) m h := by
  unfold om2 at H
  rw [vrep_add, vrep_vcat a e2 (vrep b e2 Z)] at H
  exact hardy_vcat_inv _ _ H

/-- Rocq: `Analysis.Embedding.hardy_om2_S`. -/
theorem hardy_om2_S (k : Nat) {n h : Nat} (H : Hardy (om2 (k + 1)) n h) :
    ∃ m, Hardy (om2 k) n m ∧ Hardy (V e2 Z) m h :=
  hardy_vcat_inv (V e2 Z) (om2 k) H

theorem pos_of_ge1 {m : Nat} (h : 1 ≤ m) : m + 1 ≤ m * (m + 1) := by
  rw [Nat.mul_succ]
  exact Nat.le_trans (Nat.add_le_add_left h m) (Nat.add_le_add_right (Nat.le_mul_of_pos_left m h) m)

/-- Every term is bounded by `H_(ω^2·k)` of the control, for assignments below
the control. Rocq: `Analysis.Embedding.term_bound`. -/
theorem term_bound : ∀ t : ATerm, ∃ k, ∀ (n : Nat) (σ : Nat → Nat) (h : Nat), 1 ≤ n → (∀ i, σ i < n) →
    Hardy (om2 k) n h → teval σ t < h
  | tv i => ⟨1, fun n σ h hn hσ H => by
      obtain ⟨m, hm, H'⟩ := hardy_om2_S 0 H
      cases hm with
      | z => exact Nat.lt_of_lt_of_le (hσ i) (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self n))
          (Nat.le_trans (pos_of_ge1 hn) (hardy_omega2_ge hn H')))
      | p _ _ _ _ hb _ => exact absurd hb (Pn_Z _ _)⟩
  | tz => ⟨1, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | ts t =>
    let ⟨k, IH⟩ := term_bound t
    ⟨k + 1, fun n σ h hn hσ H => by
      obtain ⟨m, Hm, H'⟩ := hardy_om2_S k H
      have hv := IH n σ m hn hσ Hm
      have hm1 : 1 ≤ m := Nat.le_trans hn (hardy_ge Hm)
      exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ hv) (Nat.le_trans (pos_of_ge1 hm1) (hardy_omega2_ge hm1 H'))⟩
  | tplus s t =>
    let ⟨ks, IHs⟩ := term_bound s
    let ⟨kt, IHt⟩ := term_bound t
    ⟨ks + kt + 1, fun n σ h hn hσ H => by
      obtain ⟨m, Hm, H'⟩ := hardy_om2_S _ H
      obtain ⟨mt, Ht, Hs⟩ := hardy_om2_add ks kt Hm
      obtain ⟨ms, Hms⟩ := hardy_exists (om2 ks) n
      have hvs := IHs n σ ms hn hσ Hms
      have hvt := IHt n σ mt hn hσ Ht
      have hmsm : ms ≤ m := hardy_mono_arg (om2 ks) (hardy_ge Ht) Hms Hs
      have hmtm : mt ≤ m := hardy_ge Hs
      have hm1 : 1 ≤ m := Nat.le_trans hn (Nat.le_trans (hardy_ge Ht) hmtm)
      have h2 : teval σ s + teval σ t < m + m :=
        Nat.add_lt_add (Nat.lt_of_lt_of_le hvs hmsm) (Nat.lt_of_lt_of_le hvt hmtm)
      refine Nat.lt_of_lt_of_le h2 (Nat.le_trans ?_ (hardy_omega2_ge hm1 H'))
      rw [Nat.mul_succ]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_left m hm1) m⟩
  | tmult s t =>
    let ⟨ks, IHs⟩ := term_bound s
    let ⟨kt, IHt⟩ := term_bound t
    ⟨ks + kt + 1, fun n σ h hn hσ H => by
      obtain ⟨m, Hm, H'⟩ := hardy_om2_S _ H
      obtain ⟨mt, Ht, Hs⟩ := hardy_om2_add ks kt Hm
      obtain ⟨ms, Hms⟩ := hardy_exists (om2 ks) n
      have hvs := IHs n σ ms hn hσ Hms
      have hvt := IHt n σ mt hn hσ Ht
      have hmsm : ms ≤ m := hardy_mono_arg (om2 ks) (hardy_ge Ht) Hms Hs
      have hmtm : mt ≤ m := hardy_ge Hs
      have hm1 : 1 ≤ m := Nat.le_trans hn (Nat.le_trans (hardy_ge Ht) hmtm)
      have h2 : teval σ s * teval σ t < m * m :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_of_lt_of_le hvt hmtm)))
          (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_of_lt_of_le hvs hmsm) (Nat.le_refl m) hm1)
      exact Nat.lt_of_lt_of_le h2 (Nat.le_trans (Nat.mul_le_mul_left m (Nat.le_succ m)) (hardy_omega2_ge hm1 H'))⟩

/-! ## Heights `ω^3·k + δ` -/

/-- Rocq: `Analysis.Embedding.W`. -/
def W (k : Nat) : VForm := vrep k e3 Z

/-- `ω^2·j + c`. Rocq: `Analysis.Embedding.sm`. -/
def sm (j c : Nat) : VForm := vrep j e2 (fin c)

/-- The leading exponent of `x` is at most `e`. -/
def LeadLe (x e : VForm) : Prop :=
  match x with
  | Z => True
  | V b _ => denote b ≤ denote e

/-- Rocq: `Analysis.Embedding.normal_vrep`. -/
theorem normal_vrep (e x : VForm) (he : IsNormal e) (hx : IsNormal x) (hlead : LeadLe x e) :
    ∀ j : Nat, IsNormal (vrep j e x)
  | 0 => hx
  | j + 1 => ⟨he, normal_vrep e x he hx hlead j, match j with
      | 0 => hlead
      | _ + 1 => le_refl _⟩

/-- Rocq: `Analysis.Embedding.e1_normal`. -/
theorem e1_normal : IsNormal e1 := ⟨trivial, trivial, trivial⟩

/-- Rocq: `Analysis.Embedding.e2_normal`. -/
theorem e2_normal : IsNormal e2 := ⟨trivial, e1_normal, le_refl _⟩

/-- Rocq: `Analysis.Embedding.e3_normal`. -/
theorem e3_normal : IsNormal e3 := ⟨trivial, e2_normal, le_refl _⟩

/-- Rocq: `Analysis.Embedding.fin_normal`. -/
theorem fin_normal (c : Nat) : IsNormal (fin c) := normal_vrep Z Z trivial trivial trivial c

/-- Rocq: `Analysis.Embedding.Z_lt_V`. -/
theorem Z_lt_V (a x : VForm) : sz Z < sz (V a x) := lt_of_le_of_lt (zero_least _) (denote_shrink1 a x)

/-- Rocq: `Analysis.Embedding.sm_normal`. -/
theorem sm_normal (j c : Nat) : IsNormal (sm j c) :=
  normal_vrep e2 (fin c) e2_normal (fin_normal c) (match c with
    | 0 => trivial
    | _ + 1 => zero_least _) j

/-- Rocq: `Analysis.Embedding.Ve3_normal`. -/
theorem Ve3_normal : IsNormal (V e3 Z) := ⟨e3_normal, trivial, trivial⟩

/-- Rocq: `Analysis.Embedding.Ve2_normal`. -/
theorem Ve2_normal : IsNormal (V e2 Z) := ⟨e2_normal, trivial, trivial⟩

/-- Rocq: `Analysis.Embedding.e2_lt_e3`. -/
theorem e2_lt_e3 : sz e2 < sz e3 := denote_shrink2 e2 Z e3_normal

/-- Rocq: `Analysis.Embedding.fin_lt_exp`. -/
theorem fin_lt_exp (c : Nat) {e : VForm} (h : sz Z < sz e) : sz (fin c) < sz (V e Z) :=
  vrep_lt h (Z_lt_V Z Z) c

/-- Rocq: `Analysis.Embedding.sm_lt`. -/
theorem sm_lt (j c : Nat) : sz (sm j c) < sz (V e3 Z) :=
  vrep_lt e2_lt_e3 (fin_lt_exp c (Z_lt_V _ _)) j

/-- Rocq: `Analysis.Embedding.VF_size_fin`. -/
theorem VF_size_fin : ∀ c : Nat, size (fin c) = c
  | 0 => rfl
  | c + 1 => by
    show size Z + size (fin c) + 1 = c + 1
    rw [VF_size_fin c]
    show 0 + c + 1 = c + 1
    rw [Nat.zero_add]

/-- Rocq: `Analysis.Embedding.VF_size_sm`. -/
theorem VF_size_sm (c : Nat) : ∀ j : Nat, size (sm j c) = 3 * j + c
  | 0 => by
    show size (fin c) = 3 * 0 + c
    rw [Nat.mul_zero, Nat.zero_add]; exact VF_size_fin c
  | j + 1 => by
    show size e2 + size (sm j c) + 1 = 3 * (j + 1) + c
    rw [VF_size_sm c j, Nat.mul_succ]
    show 2 + (3 * j + c) + 1 = 3 * j + 3 + c
    rw [Nat.add_comm 2 (3 * j + c), Nat.add_assoc, Nat.add_right_comm (3 * j) c 3]

/-- Rocq: `Analysis.Embedding.reach_ne_olt`. -/
theorem reach_ne_olt {n : Nat} {b a : VForm} (h : Reach n b a) (hne : b ≠ a) : Olt n b a := by
  cases h with
  | refl => exact absurd rfl hne
  | step _ a1 _ ha1 hr => exact ⟨a1, ha1, hr⟩

/-- Rocq: `Analysis.Embedding.olt_of_lt`. -/
theorem olt_of_lt {n : Nat} {a b : VForm} (ha : IsNormal a) (hb : IsNormal b) (hab : sz a < sz b)
    (hn : size a < n) : Olt n a b :=
  reach_ne_olt (reach_of_lt b a n ha hb hab hn) (fun e => by subst e; exact lt_irrefl _ hab)

/-- Rocq: `Analysis.Embedding.vcat_vrep`. -/
theorem vcat_vrep (k : Nat) (e x : VForm) : vcat (vrep k e Z) x = vrep k e x := (vrep_vcat k e x).symm

/-- Rocq: `Analysis.Embedding.reach_fin`. -/
theorem reach_fin (n : Nat) {a b : Nat} (h : a ≤ b) : Reach n (fin a) (fin b) := reach_vrep_le n Z Z h

/-- Rocq: `Analysis.Embedding.olt_fin`. -/
theorem olt_fin (n : Nat) {a b : Nat} (h : a < b) : Olt n (fin a) (fin b) :=
  match b, h with
  | b + 1, h => ⟨fin b, Pn_fin n b, reach_fin n (Nat.le_of_lt_succ h)⟩

/-- Rocq: `Analysis.Embedding.olt_W_fin`. -/
theorem olt_W_fin (n k : Nat) {a b : Nat} (h : a < b) : Olt n (vcat (W k) (fin a)) (vcat (W k) (fin b)) :=
  olt_vcat (W k) (olt_fin n h)

/-- Rocq: `Analysis.Embedding.reach_W`. -/
theorem reach_W (n : Nat) {k1 k : Nat} (h : k1 ≤ k) : Reach n (W k1) (W k) := reach_vrep_le n e3 Z h

/-- Rocq: `Analysis.Embedding.W_S`. -/
theorem W_S (k : Nat) : W (k + 1) = vcat (W k) (V e3 Z) := by
  unfold W; rw [vrep_S_r, vrep_vcat]

/-- A small ordinal on top of `ω^3·k` is below `ω^3·(k+1)`. Rocq: `Analysis.Embedding.reach_bump`. -/
theorem reach_bump {n : Nat} (k : Nat) {δ : VForm} (hδ : IsNormal δ) (hlt : sz δ < sz (V e3 Z))
    (hn : size δ < n) : Reach n (vcat (W k) δ) (W (k + 1)) := by
  rw [W_S]; exact reach_vcat _ (reach_of_lt (V e3 Z) δ n hδ Ve3_normal hlt hn)

/-- Rocq: `Analysis.Embedding.od_bump`. -/
theorem od_bump {n ρ k : Nat} {δ : VForm} {Γ : List SForm} (h : OD n ρ (vcat (W k) δ) Γ) (hδ : IsNormal δ)
    (hlt : sz δ < sz (V e3 Z)) (hn : size δ < n) : OD n ρ (W (k + 1)) Γ :=
  od_height h (reach_bump k hδ hlt hn)

/-- Rocq: `Analysis.Embedding.od_bump_fin`. -/
theorem od_bump_fin {n ρ k c : Nat} {Γ : List SForm} (h : OD n ρ (vcat (W k) (fin c)) Γ) (hc : c < n) :
    OD n ρ (W (k + 1)) Γ :=
  od_bump h (fin_normal c) (fin_lt_exp c (Z_lt_V _ _)) (by rw [VF_size_fin]; exact hc)

/-- Rocq: `Analysis.Embedding.od_bump_sm`. -/
theorem od_bump_sm {n ρ k j c : Nat} {Γ : List SForm} (h : OD n ρ (vcat (W k) (sm j c)) Γ) (hc : 3 * j + c < n) :
    OD n ρ (W (k + 1)) Γ :=
  od_bump h (sm_normal j c) (sm_lt j c) (by rw [VF_size_sm]; exact hc)

/-- Small heights lie below `ω^3·k` for `k ≥ 1`. Rocq: `Analysis.Embedding.reach_fin_W`. -/
theorem reach_fin_W {n k c : Nat} (hk : 1 ≤ k) (hc : c < n) : Reach n (fin c) (W k) :=
  reach_trans (reach_of_lt (V e3 Z) (fin c) n (fin_normal c) Ve3_normal (fin_lt_exp c (Z_lt_V _ _))
    (by rw [VF_size_fin]; exact hc)) (reach_W n hk)

/-- Rocq: `Analysis.Embedding.reach_sm_W`. -/
theorem reach_sm_W {n k j c : Nat} (hk : 1 ≤ k) (hc : 3 * j + c < n) : Reach n (sm j c) (W k) :=
  reach_trans (reach_of_lt (V e3 Z) (sm j c) n (sm_normal j c) Ve3_normal (sm_lt j c)
    (by rw [VF_size_sm]; exact hc)) (reach_W n hk)

/-- Rocq: `Analysis.Embedding.reach_W_vcat`. -/
theorem reach_W_vcat (n k : Nat) (δ : VForm) : Reach n (W k) (vcat (W k) δ) := reach_prefix n _ δ

/-- `c ≺_n ω^2` for `c < n`. Rocq: `Analysis.Embedding.olt_fin_om2`. -/
theorem olt_fin_om2 {n c : Nat} (hc : c < n) : Olt n (fin c) (V e2 Z) :=
  olt_of_lt (fin_normal c) Ve2_normal (fin_lt_exp c (Z_lt_V _ _)) (by rw [VF_size_fin]; exact hc)

/-! ## Numeral instances -/

/-- Rocq: `Analysis.Embedding.nsub`. -/
def nsub (σ : Nat → Nat) : Nat → ATerm := fun i => num (σ i)

/-- Rocq: `Analysis.Embedding.ninst`. -/
def ninst (σ : Nat → Nat) (A : Form) : Form := fsubst (nsub σ) A

/-- Rocq: `Analysis.Embedding.asubst_num`. -/
theorem asubst_num (τ : Nat → ATerm) : ∀ m : Nat, asubst τ (num m) = num m
  | 0 => rfl
  | m + 1 => congrArg ts (asubst_num τ m)

/-- Rocq: `Analysis.Embedding.asubst_inst1_shift`. -/
theorem asubst_inst1_shift (u t : ATerm) : asubst (inst1 u) (asubst shiftSub t) = t :=
  (asubst_comp _ _ t).trans ((asubst_ext (τ := tv) (fun _ => rfl) t).trans (asubst_id t))

/-- Rocq: `Analysis.Embedding.ninst_inst`. -/
theorem ninst_inst (σ : Nat → Nat) (A : Form) (i : Nat) :
    sub1 (fsubst (up (nsub σ)) A) (num i) = ninst (scons i σ) A := by
  unfold sub1 ninst
  rw [fsubst_comp]
  exact fsubst_ext A (fun
    | 0 => rfl
    | j + 1 => asubst_inst1_shift _ _)

/-- Rocq: `Analysis.Embedding.ninst_fshift`. -/
theorem ninst_fshift (σ : Nat → Nat) (i : Nat) (G : Form) : ninst (scons i σ) (fshift G) = ninst σ G := by
  unfold ninst fshift
  rw [fsubst_comp]
  exact fsubst_ext G (fun _ => rfl)

/-- Rocq: `Analysis.Embedding.ninst_suc`. -/
theorem ninst_suc (σ : Nat → Nat) (A : Form) (i : Nat) :
    ninst (scons i σ) (fsubst sucSub A) = sub1 (fsubst (up (nsub σ)) A) (num (i + 1)) := by
  unfold sub1 ninst
  rw [fsubst_comp, fsubst_comp]
  exact fsubst_ext A (fun
    | 0 => rfl
    | j + 1 => (asubst_inst1_shift _ _).symm)

/-- Rocq: `Analysis.Embedding.ninst_sub1`. -/
theorem ninst_sub1 (σ : Nat → Nat) (A : Form) (t : ATerm) :
    ninst σ (sub1 A t) = sub1 (fsubst (up (nsub σ)) A) (asubst (nsub σ) t) := fsubst_sub1 _ A t

/-- Rocq: `Analysis.Embedding.ninst_sub1_tz`. -/
theorem ninst_sub1_tz (σ : Nat → Nat) (A : Form) :
    ninst σ (sub1 A tz) = sub1 (fsubst (up (nsub σ)) A) (num 0) := ninst_sub1 σ A tz

/-- Rocq: `Analysis.Embedding.teval_nsub`. -/
theorem teval_nsub (ρ σ : Nat → Nat) (t : ATerm) : teval ρ (asubst (nsub σ) t) = teval σ t :=
  (teval_asubst _ _ t).trans (teval_ext (fun i => teval_num ρ (σ i)) t)

/-- Rocq: `Analysis.Embedding.ninst_All`. -/
theorem ninst_All (σ : Nat → Nat) (A : Form) : ninst σ (all A) = all (fsubst (up (nsub σ)) A) := rfl

/-- Rocq: `Analysis.Embedding.ninst_Ex`. -/
theorem ninst_Ex (σ : Nat → Nat) (A : Form) : ninst σ (ex A) = ex (fsubst (up (nsub σ)) A) := rfl

/-- Rocq: `Analysis.Embedding.isD_ninst`. -/
theorem isD_ninst (σ : Nat → Nat) (A : Form) : isD (ninst σ A) = isD A := isD_fsubst_eq A _

/-- Rocq: `Analysis.Embedding.rank_ninst`. -/
theorem rank_ninst (σ : Nat → Nat) (A : Form) : rank (ninst σ A) = rank A := rank_fsubst A _

/-! ## The identity sequent, up to the values of terms -/

/-- Rocq: `Analysis.Embedding.fsize`. -/
def fsize : Form → Nat
  | .eq _ _ => 0
  | bot => 0
  | conj A B => fsize A + fsize B + 1
  | disj A B => fsize A + fsize B + 1
  | imp A B => fsize A + fsize B + 1
  | all A => fsize A + 1
  | ex A => fsize A + 1
  | px _ => 0

/-- Rocq: `Analysis.Embedding.teq`. -/
def Teq (τ1 τ2 : Nat → ATerm) : Prop := ∀ i ρ, teval ρ (τ1 i) = teval ρ (τ2 i)

/-- Rocq: `Analysis.Embedding.teq_sym`. -/
theorem teq_sym {τ1 τ2 : Nat → ATerm} (h : Teq τ1 τ2) : Teq τ2 τ1 := fun i ρ => (h i ρ).symm

/-- Rocq: `Analysis.Embedding.teq_inst`. -/
theorem teq_inst {τ1 τ2 : Nat → ATerm} (i : Nat) (h : Teq τ1 τ2) :
    Teq (fun j => asubst (inst1 (num i)) (up τ1 j)) (fun j => asubst (inst1 (num i)) (up τ2 j))
  | 0, _ => rfl
  | j + 1, ρ => by
    show teval ρ (asubst (inst1 (num i)) (asubst shiftSub (τ1 j))) =
      teval ρ (asubst (inst1 (num i)) (asubst shiftSub (τ2 j)))
    rw [asubst_inst1_shift, asubst_inst1_shift]; exact h j ρ

/-- Rocq: `Analysis.Embedding.sub1_up_comp`. -/
theorem sub1_up_comp (τ : Nat → ATerm) (B : Form) (i : Nat) :
    sub1 (fsubst (up τ) B) (num i) = fsubst (fun j => asubst (inst1 (num i)) (up τ j)) B :=
  fsubst_comp B _ _

/-- Rocq: `Analysis.Embedding.sat_teq`. -/
theorem sat_teq {τ1 τ2 : Nat → ATerm} (B : Form) (h : Teq τ1 τ2) :
    sat ρ0 (fsubst τ1 B) ↔ sat ρ0 (fsubst τ2 B) :=
  (sat_fsubst B ρ0 τ1).trans ((sat_ext B (fun i => h i ρ0)).trans (sat_fsubst B ρ0 τ2).symm)

/-- Rocq: `Analysis.Embedding.od_id_D`. -/
theorem od_id_D {B : Form} {τ1 τ2 : Nat → ATerm} {n ρ : Nat} {α : VForm} {Γ : List SForm} (hτ : Teq τ1 τ2)
    (hD : isD B = true) (h1 : (false, fsubst τ1 B) ∈ Γ) (h2 : (true, fsubst τ2 B) ∈ Γ) : OD n ρ α Γ := by
  have hD1 := isD_fsubst B τ1 hD
  have hD2 := isD_fsubst B τ2 hD
  cases e : deval ρ0 (fsubst τ1 B) with
  | true =>
    exact .ax _ _ _ _ _ h2 ⟨hD2, (deval_sat hD2 ρ0).2 ((sat_teq B hτ).1 ((deval_sat hD1 ρ0).1 e))⟩
  | false => exact .ax _ _ _ _ _ h1 ⟨hD1, e⟩

theorem two_le_mul {a b : Nat} (h : a ≤ b) : 2 * a ≤ 2 * b := Nat.mul_le_mul_left 2 h

/-- Rocq: `Analysis.Embedding.od_id`. -/
theorem od_id : ∀ (B : Form) {τ1 τ2 : Nat → ATerm} {n ρ : Nat} {Γ : List SForm}, Teq τ1 τ2 →
    (false, fsubst τ1 B) ∈ Γ → (true, fsubst τ2 B) ∈ Γ → OD n ρ (fin (2 * fsize B)) Γ := by
  intro B
  induction B with
  | eq s t => intro τ1 τ2 n ρ Γ hτ h1 h2; exact od_id_D hτ rfl h1 h2
  | bot => intro τ1 τ2 n ρ Γ hτ h1 h2; exact od_id_D hτ rfl h1 h2
  | conj B1 B2 ih1 ih2 =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    cases hD : isD (conj B1 B2) with
    | true => exact od_id_D hτ hD h1 h2
    | false =>
      refine .conj _ _ _ (fin (2 * (fsize B1 + fsize B2) + 1)) _ _ (true, fsubst τ2 B1) (true, fsubst τ2 B2)
        h2 rfl ?_ ?_ (olt_fin n (Nat.lt_succ_self _))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (false, fsubst τ1 B1) (false, fsubst τ1 B2) _
          (.tail _ h1) rfl (.inl rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih1 hτ (.head _) (.tail _ (.head _))) (reach_fin n (two_le_mul (Nat.le_add_right _ _)))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (false, fsubst τ1 B1) (false, fsubst τ1 B2) _
          (.tail _ h1) rfl (.inr rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih2 hτ (.head _) (.tail _ (.head _))) (reach_fin n (two_le_mul (Nat.le_add_left _ _)))
  | disj B1 B2 ih1 ih2 =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    cases hD : isD (disj B1 B2) with
    | true => exact od_id_D hτ hD h1 h2
    | false =>
      refine .conj _ _ _ (fin (2 * (fsize B1 + fsize B2) + 1)) _ _ (false, fsubst τ1 B1) (false, fsubst τ1 B2)
        h1 rfl ?_ ?_ (olt_fin n (Nat.lt_succ_self _))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (true, fsubst τ2 B1) (true, fsubst τ2 B2) _
          (.tail _ h2) rfl (.inl rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih1 hτ (.tail _ (.head _)) (.head _)) (reach_fin n (two_le_mul (Nat.le_add_right _ _)))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (true, fsubst τ2 B1) (true, fsubst τ2 B2) _
          (.tail _ h2) rfl (.inr rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih2 hτ (.tail _ (.head _)) (.head _)) (reach_fin n (two_le_mul (Nat.le_add_left _ _)))
  | imp B1 B2 ih1 ih2 =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    cases hD : isD (imp B1 B2) with
    | true => exact od_id_D hτ hD h1 h2
    | false =>
      refine .conj _ _ _ (fin (2 * (fsize B1 + fsize B2) + 1)) _ _ (true, fsubst τ1 B1) (false, fsubst τ1 B2)
        h1 rfl ?_ ?_ (olt_fin n (Nat.lt_succ_self _))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (false, fsubst τ2 B1) (true, fsubst τ2 B2) _
          (.tail _ h2) rfl (.inl rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih1 (teq_sym hτ) (.head _) (.tail _ (.head _)))
          (reach_fin n (two_le_mul (Nat.le_add_right _ _)))
      · refine .disj _ _ _ (fin (2 * (fsize B1 + fsize B2))) _ _ (false, fsubst τ2 B1) (true, fsubst τ2 B2) _
          (.tail _ h2) rfl (.inr rfl) ?_ (olt_fin n (Nat.lt_succ_self _))
        exact od_height (ih2 hτ (.tail _ (.head _)) (.head _)) (reach_fin n (two_le_mul (Nat.le_add_left _ _)))
  | all B ih =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    cases hD : isD (all B) with
    | true => exact od_id_D hτ hD h1 h2
    | false =>
      refine .univ _ _ _ (fun _ => fin (2 * fsize B + 1)) _ _ true (fsubst (up τ2) B) h2 rfl
        ((isD_fsubst_eq (all B) τ2).trans hD) (fun i => ?_) (fun _ => olt_fin _ (Nat.lt_succ_self _))
      refine .exis _ _ _ (fin (2 * fsize B)) _ _ false (fsubst (up τ1) B) i (.tail _ h1) rfl
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_right _ _)) ?_ (olt_fin _ (Nat.lt_succ_self _))
      unfold inst
      rw [sub1_up_comp, sub1_up_comp]
      exact ih (teq_inst i hτ) (.head _) (.tail _ (.head _))
  | ex B ih =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    cases hD : isD (ex B) with
    | true => exact od_id_D hτ hD h1 h2
    | false =>
      refine .univ _ _ _ (fun _ => fin (2 * fsize B + 1)) _ _ false (fsubst (up τ1) B) h1 rfl
        ((isD_fsubst_eq (ex B) τ1).trans hD) (fun i => ?_) (fun _ => olt_fin _ (Nat.lt_succ_self _))
      refine .exis _ _ _ (fin (2 * fsize B)) _ _ true (fsubst (up τ2) B) i (.tail _ h2) rfl
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_right _ _)) ?_ (olt_fin _ (Nat.lt_succ_self _))
      unfold inst
      rw [sub1_up_comp, sub1_up_comp]
      exact ih (teq_inst i hτ) (.tail _ (.head _)) (.head _)
  | px u =>
    intro τ1 τ2 n ρ Γ hτ h1 h2
    refine .xax _ _ _ _ (asubst τ2 u) (asubst τ1 u) h2 h1 ?_
    rw [teval_asubst, teval_asubst]
    exact teval_ext (fun i => (hτ i ρ0).symm) u

/-! ## Bounded quantifiers have small counterexamples -/

/-- Rocq: `Analysis.Embedding.dbound`. -/
def dbound : Form → Nat
  | all (imp G _) => teval (scons 0 (scons 0 ρ0)) (guardBound G)
  | all (.eq _ _) => 0
  | all bot => 0
  | all (conj _ _) => 0
  | all (disj _ _) => 0
  | all (all _) => 0
  | all (ex _) => 0
  | all (px _) => 0
  | ex A => teval (scons 0 ρ0) (bexV A)
  | .eq _ _ => 0
  | bot => 0
  | conj _ _ => 0
  | disj _ _ => 0
  | imp _ _ => 0
  | px _ => 0

/-- Rocq: `Analysis.Embedding.fall_false`. -/
theorem fall_false : ∀ (b : Nat) (f : Nat → Bool), fall b f = false → ∃ z, z ≤ b ∧ f z = false
  | 0, _, h => ⟨0, Nat.le_refl 0, h⟩
  | b + 1, f, h => (bool_and_false h).elim
      (fun h => let ⟨z, hz, hf⟩ := fall_false b f h; ⟨z, Nat.le_succ_of_le hz, hf⟩)
      (fun h => ⟨b + 1, Nat.le_refl _, h⟩)

/-- Rocq: `Analysis.Embedding.D_univ_witness`. -/
theorem D_univ_witness : ∀ (s : SForm) (b : Bool) (A : Form), isD s.2 = true → kindof s = .univ b A → Dfalse s →
    ∃ i, i ≤ dbound s.2 ∧ Dfalse (inst b A i)
  | (true, all A'), b, A, HD, hk, Hf => by
    injection hk with e1 e2
    subst e1; subst e2
    have hdp := isD_DP HD
    cases hdp with
    | ball v B h0 h1 _ =>
      have hv : fall (teval (scons 0 (scons 0 ρ0)) v) (fun z => deval (scons z ρ0) B) = false := Hf.2
      obtain ⟨z, hz, hBz⟩ := fall_false _ _ hv
      refine ⟨z, hz, isD_quant_inst _ _ (.inl HD), ?_⟩
      show deval ρ0 (sub1 _ (num z)) = false
      rw [deval_sub1 _ ρ0 z (isD_of_all HD)]
      show (!(Nat.ble z (teval (scons 0 (scons z ρ0)) v)) || deval (scons z ρ0) B) = false
      rw [teval_occ01 h0 h1 ρ0 0 z 0 0, Nat.ble_eq_true_of_le hz, hBz]; rfl
  | (false, ex A'), b, A, HD, hk, Hf => by
    injection hk with e1 e2
    subst e1; subst e2
    have hdp := isD_DP HD
    cases hdp with
    | bex u v h0 h1 =>
      have hv : Nat.ble (teval (scons 0 ρ0) u) (teval (scons 0 ρ0) v) = true := Hf.2
      refine ⟨teval (scons 0 ρ0) v - teval (scons 0 ρ0) u, Nat.sub_le _ _, rfl, ?_⟩
      show deval ρ0 (sub1 _ (num _)) = true
      rw [deval_sub1 _ ρ0 _ rfl]
      show Nat.beq (teval (scons (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u) ρ0) u +
        (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u)) (teval (scons (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u) ρ0) v) = true
      rw [teval_occ0 h0 ρ0 (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u) 0,
        teval_occ0 h1 ρ0 (teval (scons 0 ρ0) v - teval (scons 0 ρ0) u) 0, add_sub_of_le (Nat.le_of_ble_eq_true hv)]
      exact beq_self _
  | (true, .eq _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, .eq _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (true, bot), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, bot), _, _, _, hk, _ => Kind.noConfusion hk
  | (true, conj _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, conj _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (true, disj _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, disj _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (true, imp _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, imp _ _), _, _, _, hk, _ => Kind.noConfusion hk
  | (false, all _), _, _, _, hk, _ => Kind.noConfusion hk
  | (true, ex _), _, _, _, hk, _ => Kind.noConfusion hk

theorem env2_bnd {σ : Nat → Nat} {n : Nat} (hn : 1 ≤ n) (hσ : ∀ i, σ i < n) : ∀ i, scons 0 (scons 0 σ) i < n
  | 0 => hn
  | 1 => hn
  | i + 2 => hσ i

theorem env1_bnd {σ : Nat → Nat} {n : Nat} (hn : 1 ≤ n) (hσ : ∀ i, σ i < n) : ∀ i, scons 0 σ i < n
  | 0 => hn
  | i + 1 => hσ i

/-- Rocq: `Analysis.Embedding.dbound_ninst`. -/
theorem dbound_ninst (F : Form) (HF : isD F = true) : ∃ k, ∀ (n : Nat) (σ : Nat → Nat) (h : Nat), 1 ≤ n →
    (∀ i, σ i < n) → Hardy (om2 k) n h → dbound (ninst σ F) < h := by
  have hdp := isD_DP HF
  cases hdp with
  | eq => exact ⟨0, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | bot => exact ⟨0, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | conj => exact ⟨0, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | disj => exact ⟨0, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | imp => exact ⟨0, fun n _ h hn _ H => Nat.lt_of_lt_of_le hn (hardy_ge H)⟩
  | ball v B _ _ _ =>
    obtain ⟨k, hk⟩ := term_bound v
    refine ⟨k, fun n σ h hn hσ H => ?_⟩
    show teval (scons 0 (scons 0 ρ0)) (asubst (up (up (nsub σ))) v) < h
    have E : teval (fun i => teval (scons 0 (scons 0 ρ0)) (up (up (nsub σ)) i)) v = teval (scons 0 (scons 0 σ)) v :=
      teval_ext (ρ := fun i => teval (scons 0 (scons 0 ρ0)) (up (up (nsub σ)) i)) (ρ' := scons 0 (scons 0 σ)) (fun i => match i with
        | 0 => rfl
        | 1 => rfl
        | i + 2 => by
          show teval (scons 0 (scons 0 ρ0)) (asubst shiftSub (asubst shiftSub (num (σ i)))) = σ i
          rw [teval_shift, teval_shift, teval_num]) v
    rw [teval_asubst, E]
    exact hk n _ h hn (env2_bnd hn hσ) H
  | bex u v _ _ =>
    obtain ⟨k, hk⟩ := term_bound v
    refine ⟨k, fun n σ h hn hσ H => ?_⟩
    show teval (scons 0 ρ0) (asubst (up (nsub σ)) v) < h
    have E : teval (fun i => teval (scons 0 ρ0) (up (nsub σ) i)) v = teval (scons 0 σ) v :=
      teval_ext (ρ := fun i => teval (scons 0 ρ0) (up (nsub σ) i)) (ρ' := scons 0 σ) (fun i => match i with
        | 0 => rfl
        | i + 1 => by
          show teval (scons 0 ρ0) (asubst shiftSub (num (σ i))) = σ i
          rw [teval_shift, teval_num]) v
    rw [teval_asubst, E]
    exact hk n _ h hn (env1_bnd hn hσ) H

/-- Rocq: `Analysis.Embedding.olt_om2_sm`. -/
theorem olt_om2_sm (n kv : Nat) : Olt n (om2 (kv + 1)) (sm (kv + 1) 1) := by
  unfold sm
  rw [vrep_vcat]
  exact olt_vcat_r n _ (fun h => VForm.noConfusion h)

/-- Rocq: `Analysis.Embedding.olt_up_sm`. -/
theorem olt_up_sm (n k kv : Nat) : Olt n (vcat (vcat (W k) (V e2 Z)) (om2 kv)) (vcat (W k) (sm (kv + 1) 1)) := by
  rw [vcat_assoc]
  exact olt_vcat (W k) (olt_om2_sm n kv)

/-- Introducing a universal: from instances at the raised controls, below
`ω^3·k + ω^2`. A true bounded universal is an axiom, and a false one has a
counterexample below its bound, whose premise is used after raising the
control. Rocq: `Analysis.Embedding.od_univ_intro`. -/
theorem od_univ_intro {n ρ k kv : Nat} {s : SForm} {b : Bool} {A : Form} {Γ : List SForm} (β : Nat → VForm)
    (hs : s ∈ Γ) (hk : kindof s = .univ b A)
    (hb : isD s.2 = true → ∀ h, Hardy (om2 kv) n h → dbound s.2 < h)
    (hprem : ∀ i, OD (Nat.max n (i + 1)) ρ (β i) (inst b A i :: Γ))
    (hlt : ∀ i, Olt (Nat.max n (i + 1)) (β i) (vcat (W k) (V e2 Z))) :
    OD n ρ (vcat (W k) (sm (kv + 1) 1)) Γ := by
  have htop : Reach n (vcat (W k) (V e2 Z)) (vcat (W k) (sm (kv + 1) 1)) :=
    reach_vcat (W k) (reach_prefix n (V e2 Z) (vrep kv e2 (fin 1)))
  cases hD : isD s.2 with
  | true =>
    cases dax_dec s hD with
    | inl hax => exact .ax _ _ _ _ s hs hax
    | inr hf =>
      obtain ⟨i, hi, hfi⟩ := D_univ_witness s b A hD hk hf
      obtain ⟨h, Hh⟩ := hardy_exists (om2 kv) n
      have hih : i < h := Nat.lt_of_le_of_lt hi (hb hD h Hh)
      refine .up _ (Nat.max n (i + 1)) _ _ (vcat (W k) (V e2 Z)) (om2 kv) h _ (Nat.le_max_left _ _) ?_ Hh
        (max_le' (hardy_ge Hh) hih) (olt_up_sm n k kv)
      exact od_struct (hprem i) _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (olt_reach (hlt i))
        (sub_mod_drop hfi (sub_mod_incl (fun _ h => h)))
  | false =>
    exact .univ _ _ _ β _ s b A hs hk hD hprem
      (fun i => olt_reach_trans (hlt i) (reach_mono (Nat.le_max_left _ _) htop))

/-! ## The embedding -/

/-- Rocq: `Analysis.Embedding.seqof`. -/
def seqof (σ : Nat → Nat) (Γ : List Form) (A : Form) : List SForm :=
  (true, ninst σ A) :: Γ.map (fun G => (false, ninst σ G))

/-- Rocq: `Analysis.Embedding.bnd`. -/
def Bnd (σ : Nat → Nat) (n : Nat) : Prop := ∀ i, σ i < n

/-- Rocq: `Analysis.Embedding.Emb`. -/
def Emb (Γ : List Form) (A : Form) : Prop :=
  ∃ k ρ N, 3 ≤ N ∧ ∀ (n : Nat) (σ : Nat → Nat), N ≤ n → Bnd σ n → OD n ρ (W k) (seqof σ Γ A)

/-- Rocq: `Analysis.Embedding.In_neg`. -/
theorem In_neg (σ : Nat → Nat) {Γ : List Form} {G : Form} (h : G ∈ Γ) :
    (false, ninst σ G) ∈ Γ.map (fun G => (false, ninst σ G)) :=
  mem_map_of_mem (fun G => (false, ninst σ G)) h

/-- Rocq: `Analysis.Embedding.bnd_mono`. -/
theorem bnd_mono {σ : Nat → Nat} {n m : Nat} (h : n ≤ m) (hσ : Bnd σ n) : Bnd σ m :=
  fun i => Nat.lt_of_lt_of_le (hσ i) h

/-- Rocq: `Analysis.Embedding.bnd_scons`. -/
theorem bnd_scons {σ : Nat → Nat} {n : Nat} (i : Nat) (hσ : Bnd σ n) : Bnd (scons i σ) (Nat.max n (i + 1))
  | 0 => Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_right _ _)
  | j + 1 => Nat.lt_of_lt_of_le (hσ j) (Nat.le_max_left _ _)

/-- Rocq: `Analysis.Embedding.od_lift`. -/
theorem od_lift {n ρ k ρ' k' : Nat} {Γ Δ : List SForm} (h : OD n ρ (W k) Γ) (hρ : ρ ≤ ρ') (hk : k ≤ k')
    (hi : ∀ s, s ∈ Γ → s ∈ Δ) : OD n ρ' (W k') Δ :=
  od_struct h _ _ _ _ (Nat.le_refl _) hρ (reach_W n hk) (sub_mod_incl hi)

/-- Rocq: `Analysis.Embedding.od_lift_to`. -/
theorem od_lift_to {n ρ k ρ' : Nat} {α : VForm} {Γ Δ : List SForm} (h : OD n ρ (W k) Γ) (hρ : ρ ≤ ρ')
    (hk : Reach n (W k) α) (hi : ∀ s, s ∈ Γ → s ∈ Δ) : OD n ρ' α Δ :=
  od_struct h _ _ _ _ (Nat.le_refl _) hρ hk (sub_mod_incl hi)

/-- Rocq: `Analysis.Embedding.fsize_fsubst`. -/
theorem fsize_fsubst : ∀ (A : Form) (σ : Nat → ATerm), fsize (fsubst σ A) = fsize A
  | .eq _ _, _ => rfl
  | bot, _ => rfl
  | conj A B, σ => by show fsize (fsubst σ A) + fsize (fsubst σ B) + 1 = _; rw [fsize_fsubst A, fsize_fsubst B]; rfl
  | disj A B, σ => by show fsize (fsubst σ A) + fsize (fsubst σ B) + 1 = _; rw [fsize_fsubst A, fsize_fsubst B]; rfl
  | imp A B, σ => by show fsize (fsubst σ A) + fsize (fsubst σ B) + 1 = _; rw [fsize_fsubst A, fsize_fsubst B]; rfl
  | all A, σ => by show fsize (fsubst (up σ) A) + 1 = _; rw [fsize_fsubst A]; rfl
  | ex A, σ => by show fsize (fsubst (up σ) A) + 1 = _; rw [fsize_fsubst A]; rfl
  | px _, _ => rfl

/-- The identity sequent for an instance. Rocq: `Analysis.Embedding.od_id_inst`. -/
theorem od_id_inst {n ρ k : Nat} (σ : Nat → Nat) (A : Form) {Γ : List SForm} (hk : 1 ≤ k) (hn : 2 * fsize A < n)
    (h1 : (false, ninst σ A) ∈ Γ) (h2 : (true, ninst σ A) ∈ Γ) : OD n ρ (W k) Γ :=
  od_height (od_id A (fun _ _ => rfl) h1 h2) (reach_fin_W hk hn)

theorem incl_ins2 {α : Type} {a b : α} {L : List α} : ∀ y, y ∈ a :: L → y ∈ a :: b :: L
  | _, .head _ => .head _
  | _, .tail _ h => .tail _ (.tail _ h)

theorem incl_ins3 {α : Type} {a b c : α} {L : List α} : ∀ y, y ∈ a :: b :: L → y ∈ a :: b :: c :: L
  | _, .head _ => .head _
  | _, .tail _ (.head _) => .tail _ (.head _)
  | _, .tail _ (.tail _ h) => .tail _ (.tail _ (.tail _ h))

theorem incl_ins22 {α : Type} {a b c : α} {L : List α} : ∀ y, y ∈ a :: L → y ∈ a :: b :: c :: L
  | _, .head _ => .head _
  | _, .tail _ h => .tail _ (.tail _ (.tail _ h))

theorem incl_rot {α : Type} {a b c : α} {L : List α} : ∀ y, y ∈ a :: b :: L → y ∈ b :: c :: a :: L
  | _, .head _ => .tail _ (.tail _ (.head _))
  | _, .tail _ (.head _) => .head _
  | _, .tail _ (.tail _ h) => .tail _ (.tail _ (.tail _ h))

theorem incl_single {α : Type} {a : α} {L : List α} : ∀ y, y ∈ [a] → y ∈ a :: L
  | _, .head _ => .head _

theorem incl_swap2 {α : Type} {a b : α} : ∀ y, y ∈ [a, b] → y ∈ [b, a]
  | _, .head _ => .tail _ (.head _)
  | _, .tail _ (.head _) => .head _

theorem fin1_ne : fin 1 ≠ Z := fun h => VForm.noConfusion h
theorem fin2_ne : fin 2 ≠ Z := fun h => VForm.noConfusion h

theorem olt_W1 (n k : Nat) : Olt n (W k) (vcat (W k) (fin 1)) := olt_vcat_r n _ fin1_ne

theorem three_le {N n : Nat} (hN : 3 ≤ N) (h : N ≤ n) : 3 ≤ n := Nat.le_trans hN h

/-- Rocq: `Analysis.Embedding.emb_hyp`. -/
theorem emb_hyp (Γ : List Form) (A : Form) (h : A ∈ Γ) : Emb Γ A :=
  ⟨1, 0, Nat.max 3 (2 * fsize A + 1), Nat.le_max_left _ _, fun _ σ hn _ =>
    od_id_inst σ A (Nat.le_refl 1) (Nat.lt_of_succ_le (max_le_r hn)) (.tail _ (In_neg σ h)) (.head _)⟩

/-- Rocq: `Analysis.Embedding.emb_botE`. -/
theorem emb_botE (Γ : List Form) (A : Form) (H : Emb Γ bot) : Emb Γ A :=
  let ⟨k, ρ, N, hN, h⟩ := H
  ⟨k, ρ, N, hN, fun n σ hn hσ => od_struct (h n σ hn hσ) _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (.refl _)
    (fun x hx => by
      unfold seqof at hx
      cases hx with
      | head => exact .inr ⟨rfl, rfl⟩
      | tail _ h => exact .inl (.tail _ h))⟩

/-- Rocq: `Analysis.Embedding.emb_dne`. -/
theorem emb_dne (Γ : List Form) (A : Form) (H : Emb Γ A.neg.neg) : Emb Γ A := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  refine ⟨Nat.max k1 1 + 1, Nat.max ρ1 (rank A.neg.neg + 1), Nat.max N1 (2 * fsize A + 4),
    Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn3 : 3 ≤ n := three_le hN1 (max_le_l hn)
  have hA : 2 * fsize A + 4 ≤ n := max_le_r hn
  refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) hn3)
  refine .cut _ _ _ (W (Nat.max k1 1)) _ (true, ninst σ A.neg.neg) ?_ ?_ ?_ (olt_W1 n _)
  · show rank (ninst σ A.neg.neg) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift (H1 n σ (max_le_l hn) hσ) (Nat.le_max_left _ _) (Nat.le_max_left _ _) incl_ins2
  · refine od_height (α := fin (2 * fsize A + 2)) ?_ (reach_fin_W (Nat.le_max_right _ _)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ _)) hA))
    refine .conj _ _ _ (fin (2 * fsize A + 1)) _ _ (true, imp (ninst σ A) bot) (false, bot) (.head _) rfl ?_ ?_
      (olt_fin n (Nat.lt_succ_self _))
    · refine .disj _ _ _ (fin (2 * fsize A)) _ _ (false, ninst σ A) (true, bot) _ (.head _) rfl (.inl rfl) ?_
        (olt_fin n (Nat.lt_succ_self _))
      exact od_id A (fun _ _ => rfl) (.head _) (.tail _ (.tail _ (.tail _ (.head _))))
    · exact .ax _ _ _ _ (false, bot) (.head _) ⟨rfl, rfl⟩

/-- Rocq: `Analysis.Embedding.emb_andI`. -/
theorem emb_andI (Γ : List Form) (A B : Form) (HA : Emb Γ A) (HB : Emb Γ B) : Emb Γ (conj A B) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := HA
  obtain ⟨k2, ρ2, N2, _, H2⟩ := HB
  refine ⟨Nat.max k1 k2 + 1, Nat.max ρ1 ρ2, Nat.max N1 N2, Nat.le_trans hN1 (Nat.le_max_left _ _),
    fun n σ hn hσ => ?_⟩
  refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 (max_le_l hn)))
  refine .conj _ _ _ (W (Nat.max k1 k2)) _ _ (true, ninst σ A) (true, ninst σ B) (.head _) rfl ?_ ?_ (olt_W1 n _)
  · exact od_lift (H1 n σ (max_le_l hn) hσ) (Nat.le_max_left _ _) (Nat.le_max_left _ _) incl_ins2
  · exact od_lift (H2 n σ (max_le_r hn) hσ) (Nat.le_max_right _ _) (Nat.le_max_right _ _) incl_ins2

/-- Rocq: `Analysis.Embedding.emb_andE`. -/
theorem emb_andE (Γ : List Form) (A B C : Form) (HC : C = A ∨ C = B) (H : Emb Γ (conj A B)) : Emb Γ C := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  refine ⟨Nat.max k1 1 + 1, Nat.max ρ1 (rank (conj A B) + 1), Nat.max N1 (2 * fsize C + 2),
    Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hC : 2 * fsize C + 2 ≤ n := max_le_r hn
  refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 (max_le_l hn)))
  refine .cut _ _ _ (W (Nat.max k1 1)) _ (true, ninst σ (conj A B)) ?_ ?_ ?_ (olt_W1 n _)
  · show rank (ninst σ (conj A B)) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift (H1 n σ (max_le_l hn) hσ) (Nat.le_max_left _ _) (Nat.le_max_left _ _) incl_ins2
  · refine .disj _ _ _ (fin (2 * fsize C)) _ _ (false, ninst σ A) (false, ninst σ B) (false, ninst σ C) (.head _) rfl
      (HC.elim (fun e => .inl (e ▸ rfl)) (fun e => .inr (e ▸ rfl))) ?_ ?_
    · exact od_id C (fun _ _ => rfl) (.head _) (.tail _ (.tail _ (.head _)))
    · exact olt_reach_trans (olt_fin n (Nat.lt_succ_self _))
        (reach_fin_W (Nat.le_max_right _ _) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hC))

/-- Rocq: `Analysis.Embedding.emb_orI`. -/
theorem emb_orI (Γ : List Form) (A B C : Form) (HC : C = A ∨ C = B) (H : Emb Γ C) : Emb Γ (disj A B) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  refine ⟨k1 + 1, ρ1, N1, hN1, fun n σ hn hσ => ?_⟩
  refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 hn))
  exact .disj _ _ _ (W k1) _ _ (true, ninst σ A) (true, ninst σ B) (true, ninst σ C) (.head _) rfl
    (HC.elim (fun e => .inl (e ▸ rfl)) (fun e => .inr (e ▸ rfl)))
    (od_lift (H1 n σ hn hσ) (Nat.le_refl _) (Nat.le_refl _) incl_ins2) (olt_W1 n _)

/-- Rocq: `Analysis.Embedding.emb_orE`. -/
theorem emb_orE (Γ : List Form) (A B C : Form) (H1 : Emb Γ (disj A B)) (H2 : Emb (A :: Γ) C) (H3 : Emb (B :: Γ) C) :
    Emb Γ C := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H1
  obtain ⟨k2, ρ2, N2, _, H2⟩ := H2
  obtain ⟨k3, ρ3, N3, _, H3⟩ := H3
  refine ⟨Nat.max k1 (Nat.max k2 k3) + 1, Nat.max (Nat.max ρ1 (Nat.max ρ2 ρ3)) (rank (disj A B) + 1),
    Nat.max N1 (Nat.max N2 N3), Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hk1 : k1 ≤ Nat.max k1 (Nat.max k2 k3) := Nat.le_max_left _ _
  have hk2 : k2 ≤ Nat.max k1 (Nat.max k2 k3) := Nat.le_trans (Nat.le_max_left k2 k3) (Nat.le_max_right _ _)
  have hk3 : k3 ≤ Nat.max k1 (Nat.max k2 k3) := Nat.le_trans (Nat.le_max_right k2 k3) (Nat.le_max_right _ _)
  have hr := Nat.le_max_left (Nat.max ρ1 (Nat.max ρ2 ρ3)) (rank (disj A B) + 1)
  refine od_bump_fin (c := 2) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 (max_le_l hn)))
  refine .cut _ _ _ (vcat (W _) (fin 1)) _ (true, ninst σ (disj A B)) ?_ ?_ ?_ (olt_W_fin n _ (Nat.lt_succ_self 1))
  · show rank (ninst σ (disj A B)) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift_to (H1 n σ (max_le_l hn) hσ) (Nat.le_trans (Nat.le_max_left _ _) hr)
      (reach_trans (reach_W n hk1) (reach_prefix _ _ _)) incl_ins2
  · refine .conj _ _ _ (W _) _ _ (false, ninst σ A) (false, ninst σ B) (.head _) rfl ?_ ?_ (olt_W1 n _)
    · exact od_lift (H2 n σ (max_le_l (max_le_r hn)) hσ)
        (Nat.le_trans (Nat.le_trans (Nat.le_max_left ρ2 ρ3) (Nat.le_max_right _ _)) hr) hk2 incl_rot
    · exact od_lift (H3 n σ (max_le_r (max_le_r hn)) hσ)
        (Nat.le_trans (Nat.le_trans (Nat.le_max_right ρ2 ρ3) (Nat.le_max_right _ _)) hr) hk3 incl_rot

/-- Rocq: `Analysis.Embedding.emb_impI`. -/
theorem emb_impI (Γ : List Form) (A B : Form) (H : Emb (A :: Γ) B) : Emb Γ (imp A B) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  refine ⟨k1 + 1, ρ1, N1, hN1, fun n σ hn hσ => ?_⟩
  refine od_bump_fin (c := 2) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 hn))
  refine .disj _ _ _ (vcat (W k1) (fin 1)) _ _ (false, ninst σ A) (true, ninst σ B) (false, ninst σ A) (.head _) rfl
    (.inl rfl) ?_ (olt_W_fin n _ (Nat.lt_succ_self 1))
  refine .disj _ _ _ (W k1) _ (true, ninst σ (imp A B)) (false, ninst σ A) (true, ninst σ B) (true, ninst σ B)
    (.tail _ (.head _)) rfl (.inr rfl) ?_ (olt_W1 n _)
  exact od_lift (H1 n σ hn hσ) (Nat.le_refl _) (Nat.le_refl _) incl_ins3

/-- Rocq: `Analysis.Embedding.emb_impE`. -/
theorem emb_impE (Γ : List Form) (A B : Form) (H1 : Emb Γ (imp A B)) (H2 : Emb Γ A) : Emb Γ B := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H1
  obtain ⟨k2, ρ2, N2, _, H2⟩ := H2
  refine ⟨Nat.max (Nat.max k1 k2) 1 + 1, Nat.max (Nat.max ρ1 ρ2) (rank (imp A B) + 1),
    Nat.max (Nat.max N1 N2) (2 * fsize B + 3), Nat.le_trans (Nat.le_trans hN1 (Nat.le_max_left _ _)) (Nat.le_max_left _ _),
    fun n σ hn hσ => ?_⟩
  have hk := Nat.le_max_left (Nat.max k1 k2) 1
  have hr := Nat.le_max_left (Nat.max ρ1 ρ2) (rank (imp A B) + 1)
  refine od_bump_fin (c := 2) ?_ (Nat.lt_of_lt_of_le (by decide) (three_le hN1 (max_le_l (max_le_l hn))))
  refine .cut _ _ _ (vcat (W _) (fin 1)) _ (true, ninst σ (imp A B)) ?_ ?_ ?_ (olt_W_fin n _ (Nat.lt_succ_self 1))
  · show rank (ninst σ (imp A B)) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift_to (H1 n σ (max_le_l (max_le_l hn)) hσ) (Nat.le_trans (Nat.le_max_left _ _) hr)
      (reach_trans (reach_W n (Nat.le_trans (Nat.le_max_left _ _) hk)) (reach_prefix _ _ _)) incl_ins2
  · refine .conj _ _ _ (W _) _ _ (true, ninst σ A) (false, ninst σ B) (.head _) rfl ?_ ?_ (olt_W1 n _)
    · exact od_lift (H2 n σ (max_le_r (max_le_l hn)) hσ) (Nat.le_trans (Nat.le_max_right _ _) hr)
        (Nat.le_trans (Nat.le_max_right _ _) hk) incl_ins22
    · exact od_id_inst σ B (Nat.le_max_right _ _)
        (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ 2)) (max_le_r hn))
        (.head _) (.tail _ (.tail _ (.head _)))

/-- Axioms: true bounded sentences. Rocq: `Analysis.Embedding.emb_ax`. -/
theorem emb_ax (Γ : List Form) (A : Form) (HD : isD A = true) (Ht : ∀ σ, sat ρ0 (ninst σ A)) : Emb Γ A :=
  ⟨0, 0, 3, Nat.le_refl 3, fun _ σ _ _ =>
    .ax _ _ _ _ (true, ninst σ A) (.head _)
      ⟨(isD_ninst σ A).trans HD, (deval_sat ((isD_ninst σ A).trans HD) ρ0).2 (Ht σ)⟩⟩

/-- Rocq: `Analysis.Embedding.sat_ninst_eq`. -/
theorem sat_ninst_eq (σ : Nat → Nat) (s t : ATerm) : sat ρ0 (ninst σ (.eq s t)) ↔ teval σ s = teval σ t := by
  show teval ρ0 (asubst (nsub σ) s) = teval ρ0 (asubst (nsub σ) t) ↔ _
  rw [teval_nsub, teval_nsub]

/-- Equations whose sides may differ: either true, or the premise is a false
bounded formula and can be dropped. Rocq: `Analysis.Embedding.emb_eq_cond`. -/
theorem emb_eq_cond (Γ : List Form) (s t s' t' : ATerm)
    (Himp : ∀ σ, teval σ s = teval σ t → teval σ s' = teval σ t') (H : Emb Γ (.eq s t)) : Emb Γ (.eq s' t') := by
  obtain ⟨k, ρ, N, hN, h⟩ := H
  refine ⟨k, ρ, N, hN, fun n σ hn hσ => ?_⟩
  cases Nat.decEq (teval σ s) (teval σ t) with
  | isTrue E =>
    exact .ax _ _ _ _ (true, ninst σ (.eq s' t')) (.head _) ⟨rfl, (deval_sat rfl ρ0).2 ((sat_ninst_eq σ s' t').2 (Himp σ E))⟩
  | isFalse E =>
    refine od_struct (h n σ hn hσ) _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (.refl _) (fun x hx => ?_)
    unfold seqof at hx
    cases hx with
    | head =>
      refine .inr ⟨rfl, ?_⟩
      show Nat.beq (teval ρ0 (asubst (nsub σ) s)) (teval ρ0 (asubst (nsub σ) t)) = false
      rw [teval_nsub, teval_nsub]
      cases e : Nat.beq (teval σ s) (teval σ t) with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true e) E
    | tail _ h => exact .inl (.tail _ h)

/-- Rocq: `Analysis.Embedding.map_neg_fshift`. -/
theorem map_neg_fshift (σ : Nat → Nat) (i : Nat) (Γ : List Form) :
    (Γ.map fshift).map (fun G => (false, ninst (scons i σ) G)) = Γ.map (fun G => (false, ninst σ G)) := by
  rw [map_map]
  exact map_ext (fun G => by show (false, ninst (scons i σ) (fshift G)) = _; rw [ninst_fshift]) Γ

/-- Rocq: `Analysis.Embedding.dbound_exists`. -/
theorem dbound_exists (F : Form) : ∃ kv, isD F = true → ∀ (n : Nat) (σ : Nat → Nat) (h : Nat), 1 ≤ n → Bnd σ n →
    Hardy (om2 kv) n h → dbound (ninst σ F) < h := by
  cases hF : isD F with
  | true => obtain ⟨kv, hkv⟩ := dbound_ninst F hF; exact ⟨kv, fun _ => hkv⟩
  | false => exact ⟨0, fun h => Bool.noConfusion h⟩

theorem Ve2_ne : V e2 Z ≠ Z := fun h => VForm.noConfusion h

/-- Rocq: `Analysis.Embedding.emb_allI`. -/
theorem emb_allI (Γ : List Form) (A : Form) (H : Emb (Γ.map fshift) A) : Emb Γ (all A) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  obtain ⟨kv, Hkv⟩ := dbound_exists (all A)
  refine ⟨k1 + 1, ρ1, Nat.max N1 (3 * (kv + 1) + 2), Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) (three_le hN1 (max_le_l hn))
  refine od_bump_sm (j := kv + 1) (c := 1) ?_ (Nat.lt_of_succ_le (max_le_r hn))
  refine od_univ_intro (s := (true, ninst σ (all A))) (b := true) (A := fsubst (up (nsub σ)) A) (fun _ => W k1)
    (.head _) rfl ?_ ?_ ?_
  · intro hD h Hh
    exact Hkv ((isD_ninst σ (all A)).symm.trans hD) n σ h hn1 hσ Hh
  · intro i
    refine od_lift (H1 (Nat.max n (i + 1)) (scons i σ) (Nat.le_trans (max_le_l hn) (Nat.le_max_left _ _))
      (bnd_scons i hσ)) (Nat.le_refl _) (Nat.le_refl _) (fun y hy => ?_)
    unfold seqof at hy
    rw [map_neg_fshift] at hy
    unfold inst
    rw [ninst_inst]
    exact incl_ins2 y hy
  · intro i; exact olt_vcat_r _ (W k1) Ve2_ne

theorem mem3 {α : Type} {a b c : α} {L : List α} : c ∈ a :: b :: c :: L := .tail _ (.tail _ (.head _))

/-- Rocq: `Analysis.Embedding.emb_allE`. -/
theorem emb_allE (Γ : List Form) (A : Form) (t : ATerm) (H : Emb Γ (all A)) : Emb Γ (sub1 A t) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  obtain ⟨kt, Hkt⟩ := term_bound t
  refine ⟨Nat.max k1 1 + 1, Nat.max ρ1 (rank (all A) + 1), Nat.max N1 (Nat.max (2 * fsize A + 2) (3 * (kt + 1) + 2)),
    Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn3 : 3 ≤ n := three_le hN1 (max_le_l hn)
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn3
  have hA : 2 * fsize A + 2 ≤ n := max_le_l (max_le_r hn)
  have hK : 3 * (kt + 1) + 2 ≤ n := max_le_r (max_le_r hn)
  refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) hn3)
  refine .cut _ _ _ (W (Nat.max k1 1)) _ (true, ninst σ (all A)) ?_ ?_ ?_ (olt_W1 n _)
  · show rank (ninst σ (all A)) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift (H1 n σ (max_le_l hn) hσ) (Nat.le_max_left _ _) (Nat.le_max_left _ _) incl_ins2
  · refine od_height (α := sm (kt + 1) 1) ?_ (reach_sm_W (Nat.le_max_right _ _) (Nat.lt_of_succ_le hK))
    obtain ⟨h, Hh⟩ := hardy_exists (om2 kt) n
    have Hw : teval σ t < h := Hkt n σ h hn1 hσ Hh
    have hm : n ≤ Nat.max n (teval σ t + 1) := Nat.le_max_left _ _
    refine .up _ (Nat.max n (teval σ t + 1)) _ _ (V e2 Z) (om2 kt) h _ hm ?_ Hh (max_le' (hardy_ge Hh) Hw)
      (olt_om2_sm n kt)
    refine od_height (α := fin (2 * fsize A + 1)) ?_
      (olt_reach (olt_fin_om2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans hA hm))))
    refine .exis _ _ _ (fin (2 * fsize A)) _ (false, ninst σ (all A)) false (fsubst (up (nsub σ)) A) (teval σ t)
      (.head _) rfl (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) ?_ (olt_fin _ (Nat.lt_succ_self _))
    rw [← fsize_fsubst A (up (nsub σ))]
    have hmem : (true, fsubst (inst1 (asubst (nsub σ) t)) (fsubst (up (nsub σ)) A)) ∈
        inst false (fsubst (up (nsub σ)) A) (teval σ t) :: (false, ninst σ (all A)) :: seqof σ Γ (sub1 A t) := by
      unfold seqof; rw [ninst_sub1]; exact mem3
    refine od_id _ (τ1 := inst1 (num (teval σ t))) (τ2 := inst1 (asubst (nsub σ) t)) ?_ (.head _) hmem
    intro i ρ
    cases i with
    | zero => show teval ρ (num _) = teval ρ (asubst (nsub σ) t); rw [teval_num, teval_nsub]
    | succ i => rfl

/-- Rocq: `Analysis.Embedding.emb_exI`. -/
theorem emb_exI (Γ : List Form) (A : Form) (t : ATerm) (H : Emb Γ (sub1 A t)) : Emb Γ (ex A) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H
  obtain ⟨kt, Hkt⟩ := term_bound t
  refine ⟨Nat.max k1 1 + 1, Nat.max ρ1 (rank A + 1), Nat.max N1 (Nat.max (2 * fsize A + 2) (3 * (kt + 1) + 2)),
    Nat.le_trans hN1 (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn3 : 3 ≤ n := three_le hN1 (max_le_l hn)
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn3
  have hA : 2 * fsize A + 2 ≤ n := max_le_l (max_le_r hn)
  have hK : 3 * (kt + 1) + 2 ≤ n := max_le_r (max_le_r hn)
  refine od_bump_sm (j := kt + 1) (c := 1) ?_ (Nat.lt_of_succ_le hK)
  obtain ⟨h, Hh⟩ := hardy_exists (om2 kt) n
  have Hw : teval σ t < h := Hkt n σ h hn1 hσ Hh
  have hm : n ≤ (Nat.max n (teval σ t + 1)) := Nat.le_max_left _ _
  refine .up _ (Nat.max n (teval σ t + 1)) _ _ (vcat (W (Nat.max k1 1)) (V e2 Z)) (om2 kt) h _ hm ?_ Hh (max_le' (hardy_ge Hh) Hw) (olt_up_sm n (Nat.max k1 1) kt)
  refine od_height (α := vcat (W (Nat.max k1 1)) (fin 2)) ?_
    (olt_reach (olt_vcat (W (Nat.max k1 1)) (olt_fin_om2 (Nat.lt_of_lt_of_le (by decide) (Nat.le_trans hn3 hm)))))
  refine .exis _ _ _ (vcat (W (Nat.max k1 1)) (fin 1)) _ (true, ninst σ (ex A)) true (fsubst (up (nsub σ)) A) (teval σ t)
    (.head _) rfl (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)) ?_ (olt_W_fin (Nat.max n (teval σ t + 1)) (Nat.max k1 1) (Nat.lt_succ_self 1))
  refine .cut _ _ _ (W (Nat.max k1 1)) _ (true, sub1 (fsubst (up (nsub σ)) A) (asubst (nsub σ) t)) ?_ ?_ ?_ (olt_W1 (Nat.max n (teval σ t + 1)) (Nat.max k1 1))
  · show rank (fsubst _ (fsubst _ A)) < _
    rw [rank_fsubst, rank_fsubst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · refine od_lift (H1 (Nat.max n (teval σ t + 1)) σ (Nat.le_trans (max_le_l hn) hm) (bnd_mono hm hσ)) (Nat.le_max_left _ _)
      (Nat.le_max_left _ _) (fun y hy => ?_)
    unfold seqof at hy
    rw [ninst_sub1] at hy
    exact incl_ins22 y hy
  · refine od_height (α := fin (2 * fsize A)) ?_
      (reach_fin_W (Nat.le_max_right _ _) (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ _)) (Nat.le_trans hA hm)))
    rw [← fsize_fsubst A (up (nsub σ))]
    refine od_id _ (τ1 := inst1 (asubst (nsub σ) t)) (τ2 := inst1 (num (teval σ t))) ?_ (.head _) (.tail _ (.head _))
    intro i ρ
    cases i with
    | zero => show teval ρ (asubst (nsub σ) t) = teval ρ (num _); rw [teval_num, teval_nsub]
    | succ i => rfl

/-- Rocq: `Analysis.Embedding.emb_exE`. -/
theorem emb_exE (Γ : List Form) (A B : Form) (H1 : Emb Γ (ex A)) (H2 : Emb (A :: Γ.map fshift) (fshift B)) :
    Emb Γ B := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H1
  obtain ⟨k2, ρ2, N2, _, H2⟩ := H2
  obtain ⟨kv, Hkv⟩ := dbound_exists (ex A)
  refine ⟨Nat.max k1 k2 + 1, Nat.max (Nat.max ρ1 ρ2) (rank (ex A) + 1), Nat.max (Nat.max N1 N2) (3 * (kv + 1) + 3),
    Nat.le_trans (Nat.le_trans hN1 (Nat.le_max_left _ _)) (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) (three_le hN1 (max_le_l (max_le_l hn)))
  have hr := Nat.le_max_left (Nat.max ρ1 ρ2) (rank (ex A) + 1)
  refine od_bump_sm (j := kv + 1) (c := 2) ?_ (Nat.lt_of_succ_le (max_le_r hn))
  refine .cut _ _ _ (vcat (W (Nat.max k1 k2)) (sm (kv + 1) 1)) _ (true, ninst σ (ex A)) ?_ ?_ ?_ ?_
  · show rank (ninst σ (ex A)) < _
    rw [rank_ninst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact od_lift_to (H1 n σ (max_le_l (max_le_l hn)) hσ) (Nat.le_trans (Nat.le_max_left _ _) hr)
      (reach_trans (reach_W n (Nat.le_max_left _ _)) (reach_prefix _ _ _)) incl_ins2
  · refine od_univ_intro (s := (false, ninst σ (ex A))) (b := false) (A := fsubst (up (nsub σ)) A) (fun _ => W k2)
      (.head _) rfl ?_ ?_ ?_
    · intro hD h Hh
      exact Hkv ((isD_ninst σ (ex A)).symm.trans hD) n σ h hn1 hσ Hh
    · intro i
      refine od_lift (H2 (Nat.max n (i + 1)) (scons i σ)
        (Nat.le_trans (max_le_r (max_le_l hn)) (Nat.le_max_left _ _)) (bnd_scons i hσ))
        (Nat.le_trans (Nat.le_max_right _ _) hr) (Nat.le_refl _) (fun y hy => ?_)
      unfold seqof at hy
      rw [List.map, map_neg_fshift, ninst_fshift] at hy
      unfold inst
      rw [ninst_inst]
      exact incl_rot y hy
    · intro i
      exact reach_olt_trans (reach_W _ (Nat.le_max_right _ _)) (olt_vcat_r _ _ Ve2_ne)
  · unfold sm
    rw [vrep_vcat (kv + 1) e2 (fin 1), vrep_vcat (kv + 1) e2 (fin 2)]
    exact olt_vcat _ (olt_vcat _ (olt_fin n (Nat.lt_succ_self 1)))

/-- Rocq: `Analysis.Embedding.emb_leib`. -/
theorem emb_leib (Γ : List Form) (A : Form) (s t : ATerm) (H1 : Emb Γ (.eq s t)) (H2 : Emb Γ (sub1 A s)) :
    Emb Γ (sub1 A t) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H1
  obtain ⟨k2, ρ2, N2, _, H2⟩ := H2
  refine ⟨Nat.max (Nat.max k1 k2) 1 + 1, Nat.max (Nat.max ρ1 ρ2) (rank A + 1), Nat.max (Nat.max N1 N2) (2 * fsize A + 2),
    Nat.le_trans (Nat.le_trans hN1 (Nat.le_max_left _ _)) (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn3 : 3 ≤ n := three_le hN1 (max_le_l (max_le_l hn))
  have hk := Nat.le_max_left (Nat.max k1 k2) 1
  have hr := Nat.le_max_left (Nat.max ρ1 ρ2) (rank A + 1)
  cases Nat.decEq (teval σ s) (teval σ t) with
  | isTrue E =>
    refine od_bump_fin (c := 1) ?_ (Nat.lt_of_lt_of_le (by decide) hn3)
    refine .cut _ _ _ (W _) _ (true, ninst σ (sub1 A s)) ?_ ?_ ?_ (olt_W1 n _)
    · show rank (ninst σ (sub1 A s)) < _
      rw [rank_ninst]; show rank (fsubst _ A) < _; rw [rank_fsubst]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    · exact od_lift (H2 n σ (max_le_r (max_le_l hn)) hσ) (Nat.le_trans (Nat.le_max_right _ _) hr)
        (Nat.le_trans (Nat.le_max_right _ _) hk) incl_ins2
    · refine od_height (α := fin (2 * fsize A)) ?_
        (reach_fin_W (Nat.le_max_right _ _) (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ _)) (max_le_r hn)))
      rw [← fsize_fsubst A (up (nsub σ))]
      have hm1 : (false, fsubst (inst1 (asubst (nsub σ) s)) (fsubst (up (nsub σ)) A)) ∈
          (false, ninst σ (sub1 A s)) :: seqof σ Γ (sub1 A t) := by rw [ninst_sub1]; exact .head _
      have hm2 : (true, fsubst (inst1 (asubst (nsub σ) t)) (fsubst (up (nsub σ)) A)) ∈
          (false, ninst σ (sub1 A s)) :: seqof σ Γ (sub1 A t) := by unfold seqof; rw [ninst_sub1 σ A t]; exact .tail _ (.head _)
      refine od_id _ ?_ hm1 hm2
      intro i ρ
      cases i with
      | zero => show teval ρ (asubst (nsub σ) s) = teval ρ (asubst (nsub σ) t); rw [teval_nsub, teval_nsub]; exact E
      | succ i => rfl
  | isFalse E =>
    refine od_struct (H1 n σ (max_le_l (max_le_l hn)) hσ) _ _ _ _ (Nat.le_refl _)
      (Nat.le_trans (Nat.le_max_left _ _) hr) (reach_W n (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hk (Nat.le_succ _))))
      (fun x hx => ?_)
    unfold seqof at hx
    cases hx with
    | head =>
      refine .inr ⟨rfl, ?_⟩
      show Nat.beq (teval ρ0 (asubst (nsub σ) s)) (teval ρ0 (asubst (nsub σ) t)) = false
      rw [teval_nsub, teval_nsub]
      cases e : Nat.beq (teval σ s) (teval σ t) with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true e) E
    | tail _ h => exact .inl (.tail _ h)

/-- Rocq: `Analysis.Embedding.emb_ind`. -/
theorem emb_ind (Γ : List Form) (A : Form) (H1 : Emb [] (sub1 A tz)) (H2 : Emb [A] (fsubst sucSub A)) :
    Emb Γ (all A) := by
  obtain ⟨k1, ρ1, N1, hN1, H1⟩ := H1
  obtain ⟨k2, ρ2, N2, _, H2⟩ := H2
  obtain ⟨kv, Hkv⟩ := dbound_exists (all A)
  refine ⟨(Nat.max k1 k2) + 1, (Nat.max (Nat.max ρ1 ρ2) (rank A + 1)), Nat.max (Nat.max N1 N2) (3 * (kv + 1) + 2),
    Nat.le_trans (Nat.le_trans hN1 (Nat.le_max_left _ _)) (Nat.le_max_left _ _), fun n σ hn hσ => ?_⟩
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) (three_le hN1 (max_le_l (max_le_l hn)))
  have hr := Nat.le_max_left (Nat.max ρ1 ρ2) (rank A + 1)
  have Hchain : ∀ i, OD (Nat.max n (i + 1)) (Nat.max (Nat.max ρ1 ρ2) (rank A + 1)) (vcat (W (Nat.max k1 k2)) (fin i)) [(true, sub1 (fsubst (up (nsub σ)) A) (num i))] := by
    intro i
    induction i with
    | zero =>
      show OD _ _ (vcat (W (Nat.max k1 k2)) Z) _
      rw [vcat_Z]
      refine od_lift (H1 _ σ (Nat.le_trans (max_le_l (max_le_l hn)) (Nat.le_max_left _ _))
        (bnd_mono (Nat.le_max_left _ _) hσ)) (Nat.le_trans (Nat.le_max_left _ _) hr) (Nat.le_max_left _ _) (fun y hy => ?_)
      unfold seqof at hy
      rw [ninst_sub1_tz] at hy
      exact hy
    | succ i ih =>
      refine .cut _ _ _ (vcat (W (Nat.max k1 k2)) (fin i)) _ (true, sub1 (fsubst (up (nsub σ)) A) (num i)) ?_ ?_ ?_
        (olt_W_fin _ (Nat.max k1 k2) (Nat.lt_succ_self i))
      · show rank (fsubst _ (fsubst _ A)) < _
        rw [rank_fsubst, rank_fsubst]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
      · exact od_struct ih _ _ _ _ (max_mono (Nat.le_refl _) (Nat.le_succ _)) (Nat.le_refl _) (.refl _) (sub_mod_incl incl_single)
      · refine od_lift_to (H2 _ (scons i σ) (Nat.le_trans (max_le_r (max_le_l hn)) (Nat.le_max_left _ _)) ?_)
          (Nat.le_trans (Nat.le_max_right _ _) hr) (reach_trans (reach_W _ (Nat.le_max_right _ _)) (reach_prefix _ _ _))
          (fun y hy => ?_)
        · intro j
          cases j with
          | zero => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _))
          | succ j => exact Nat.lt_of_lt_of_le (hσ j) (Nat.le_max_left _ _)
        · unfold seqof at hy
          rw [List.map, List.map, ninst_suc, ← ninst_inst] at hy
          exact incl_swap2 y hy
  refine od_bump_sm (j := kv + 1) (c := 1) ?_ (Nat.lt_of_succ_le (max_le_r hn))
  refine od_univ_intro (s := (true, ninst σ (all A))) (b := true) (A := fsubst (up (nsub σ)) A)
    (fun i => vcat (W (Nat.max k1 k2)) (fin i)) (.head _) rfl ?_ ?_ ?_
  · intro hD h Hh
    exact Hkv ((isD_ninst σ (all A)).symm.trans hD) n σ h hn1 hσ Hh
  · intro i
    exact od_struct (Hchain i) _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (.refl _) (sub_mod_incl incl_single)
  · intro i
    exact olt_vcat (W (Nat.max k1 k2)) (olt_fin_om2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_right _ _)))

/-- Rocq: `Analysis.Embedding.embed`. -/
theorem embed {cl : Bool} {Γ : List Form} {A : Form} (h : Prov cl Γ A) : Emb Γ A := by
  induction h with
  | hyp Γ A hA => exact emb_hyp Γ A hA
  | botE Γ A _ ih => exact emb_botE Γ A ih
  | dne Γ A _ _ ih => exact emb_dne Γ A ih
  | andI Γ A B _ _ ih1 ih2 => exact emb_andI Γ A B ih1 ih2
  | andE1 Γ A B _ ih => exact emb_andE Γ A B A (.inl rfl) ih
  | andE2 Γ A B _ ih => exact emb_andE Γ A B B (.inr rfl) ih
  | orI1 Γ A B _ ih => exact emb_orI Γ A B A (.inl rfl) ih
  | orI2 Γ A B _ ih => exact emb_orI Γ A B B (.inr rfl) ih
  | orE Γ A B C _ _ _ ih1 ih2 ih3 => exact emb_orE Γ A B C ih1 ih2 ih3
  | impI Γ A B _ ih => exact emb_impI Γ A B ih
  | impE Γ A B _ _ ih1 ih2 => exact emb_impE Γ A B ih1 ih2
  | allI Γ A _ ih => exact emb_allI Γ A ih
  | allE Γ A t _ ih => exact emb_allE Γ A t ih
  | exI Γ A t _ ih => exact emb_exI Γ A t ih
  | exE Γ A B _ _ ih1 ih2 => exact emb_exE Γ A B ih1 ih2
  | refl Γ t => exact emb_ax Γ _ rfl (fun σ => (sat_ninst_eq σ t t).2 rfl)
  | leib Γ A s t _ _ ih1 ih2 => exact emb_leib Γ A s t ih1 ih2
  | succNe Γ t => exact emb_ax Γ _ rfl (fun _ h => Nat.noConfusion h)
  | succInj Γ s t _ ih => exact emb_eq_cond Γ (ts s) (ts t) s t (fun _ E => Nat.add_right_cancel E) ih
  | plus0 Γ t => exact emb_ax Γ _ rfl (fun σ => (sat_ninst_eq σ _ _).2 rfl)
  | plusS Γ s t => exact emb_ax Γ _ rfl (fun σ => (sat_ninst_eq σ _ _).2 rfl)
  | mult0 Γ t => exact emb_ax Γ _ rfl (fun σ => (sat_ninst_eq σ _ _).2 rfl)
  | multS Γ s t => exact emb_ax Γ _ rfl (fun σ => (sat_ninst_eq σ _ _).2 rfl)
  | ind Γ A _ _ ih1 ih2 => exact emb_ind Γ A ih1 ih2

end ConstructiveOrdinals.Embedding
