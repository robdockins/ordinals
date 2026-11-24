import ConstructiveOrdinals.Notation.V

/-!
# The Hardy hierarchy below ε₀

Port of `Ordinal/Analysis/Hardy.v`.

Ordinals are V forms (`VNotation`), not necessarily normal: `V a x` denotes
`ω^a + x`. The predecessor `P_n` of the standard fundamental sequences only
changes the last summand, with `P_n(ω^a) = ω^(P_n a)·(n-1) + P_n(ω^(P_n a))`;
this is the relation `Pn`. `Reach n β α` (β ≼_n α) says that β is reached
from α by `P_n` steps, and `Hardy α n m` says `H_α(n) = m`, where
`H_0(n) = n` and `H_α(n) = H_(P_n α)(n+1)`.

The main results are the Bachmann property (`Pn_bachmann`), so that `≼_n`
grows with `n` (`reach_S`); the monotonicity of `H_α` (`hardy_mono`);
composition `H_(γ+δ) = H_γ ∘ H_δ` (`hardy_vcat`); and, for normal forms,
`α < β` gives `α ≼_n β` once `n` exceeds the size of `α` (`reach_of_lt`).

Lean notes:

- Rocq's `reach` and `hardy` are `Reach` and `Hardy`; the constructors of
  `Pn` are `Pn.one`, `Pn.tail` and `Pn.exp`.
- Arithmetic is done by hand, since `omega` uses `propext`.
-/

namespace ConstructiveOrdinals.Hardy

open Ordinal VNotation VForm

/-! ## Sums and repeated summands -/

/-- Rocq: `Analysis.Hardy.vcat`. -/
def vcat : VForm → VForm → VForm
  | Z, b => b
  | V e x, b => V e (vcat x b)

/-- `vrep k e x` is `ω^e·k + x`. Rocq: `Analysis.Hardy.vrep`. -/
def vrep : Nat → VForm → VForm → VForm
  | 0, _, x => x
  | k + 1, e, x => V e (vrep k e x)

/-- Rocq: `Analysis.Hardy.vcat_Z`. -/
theorem vcat_Z : ∀ a : VForm, vcat a Z = a
  | Z => rfl
  | V e x => congrArg (V e) (vcat_Z x)

/-- Rocq: `Analysis.Hardy.vcat_assoc`. -/
theorem vcat_assoc : ∀ a b c : VForm, vcat (vcat a b) c = vcat a (vcat b c)
  | Z, _, _ => rfl
  | V e x, b, c => congrArg (V e) (vcat_assoc x b c)

/-- Rocq: `Analysis.Hardy.vrep_vcat`. -/
theorem vrep_vcat : ∀ (k : Nat) (e x : VForm), vrep k e x = vcat (vrep k e Z) x
  | 0, _, _ => rfl
  | k + 1, e, x => congrArg (V e) (vrep_vcat k e x)

/-- Rocq: `Analysis.Hardy.vrep_add`. -/
theorem vrep_add : ∀ (j k : Nat) (e x : VForm), vrep (j + k) e x = vrep j e (vrep k e x)
  | 0, k, e, x => by rw [Nat.zero_add]; rfl
  | j + 1, k, e, x => by
    rw [Nat.succ_add]; exact congrArg (V e) (vrep_add j k e x)

/-- Rocq: `Analysis.Hardy.vrep_S_r`. -/
theorem vrep_S_r : ∀ (k : Nat) (e x : VForm), vrep (k + 1) e x = vrep k e (V e x)
  | 0, _, _ => rfl
  | k + 1, e, x => congrArg (V e) (vrep_S_r k e x)

/-! ## Denotations -/

/-- Rocq: `Analysis.Hardy.V_eq`. -/
theorem V_eq (a x : VForm) : sz (V a x) ≈ ω ^ sz a + sz x :=
  veblen_onePlus _ (complete a) _ (complete x)

/-- Rocq: `Analysis.Hardy.VZ_eq`. -/
theorem VZ_eq (a : VForm) : sz (V a Z) ≈ ω ^ sz a := equiv_trans (V_eq a Z) (add_zero _)

/-- Rocq: `Analysis.Hardy.below_exp_add`. -/
theorem below_exp_add (c : VForm) {x y : Ordinal.{0}} (hx : x < ω ^ sz c) (hy : y < ω ^ sz c) :
    x + y < ω ^ sz c :=
  powOmega_additively_closed (complete c) x y hx hy

/-- Rocq: `Analysis.Hardy.VF_ind`. -/
theorem VF_ind (P : VForm → Prop) (H : ∀ a, (∀ b, sz b < sz a → P b) → P a) (a : VForm) : P a :=
  (InvImage.wf (fun v : VForm => sz v) lt_wf).induction a H

/-- Rocq: `Analysis.Hardy.V_tail_lt`. -/
theorem V_tail_lt (e : VForm) {x y : VForm} (h : sz x < sz y) : sz (V e x) < sz (V e y) :=
  lt_of_le_of_lt (V_eq e x).le (lt_of_lt_of_le (add_lt_add_left _ h) (V_eq e y).ge)

/-- Rocq: `Analysis.Hardy.exp_lt`. -/
theorem exp_lt {e f : VForm} (h : sz e < sz f) : sz (V e Z) < sz (V f Z) :=
  lt_of_le_of_lt (VZ_eq e).le (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 h) (VZ_eq f).ge)

/-- Rocq: `Analysis.Hardy.vrep_lt`. -/
theorem vrep_lt {e f y : VForm} (hef : sz e < sz f) (hy : sz y < sz (V e Z)) :
    ∀ k : Nat, sz (vrep k e y) < sz (V f Z)
  | 0 => lt_trans hy (exp_lt hef)
  | k + 1 =>
    lt_of_le_of_lt (V_eq e _).le
      (lt_of_lt_of_le
        (below_exp_add f (pow_lt_pow_right omega_gt1 hef)
          (lt_of_lt_of_le (vrep_lt hef hy k) (VZ_eq f).le))
        (VZ_eq f).ge)

/-- Rocq: `Analysis.Hardy.exp_le_V`. -/
theorem exp_le_V (e x : VForm) : sz (V e Z) ≤ sz (V e x) :=
  le_trans (VZ_eq e).le (le_trans (le_add_right _ _) (V_eq e x).ge)

/-- Rocq: `Analysis.Hardy.tail_le_V`. -/
theorem tail_le_V (e x : VForm) : sz x ≤ sz (V e x) :=
  le_trans (le_add_left _ _) (V_eq e x).ge

/-- Rocq: `Analysis.Hardy.exp_shrink`. -/
theorem exp_shrink (e : VForm) : sz e < sz (V e Z) := denote_shrink1 e Z

/-! ## The predecessor relation -/

/-- `Pn n a b`: `b` is `P_n(a)`. Rocq: `Analysis.Hardy.Pn`. -/
inductive Pn (n : Nat) : VForm → VForm → Prop
  /-- Rocq: `Pn_one`. -/
  | one : Pn n (V Z Z) Z
  /-- Rocq: `Pn_tail`. -/
  | tail (e x y : VForm) : Pn n x y → Pn n (V e x) (V e y)
  /-- Rocq: `Pn_exp`. -/
  | exp (e e' y : VForm) : Pn n e e' → Pn n (V e' Z) y → Pn n (V e Z) (vrep (n - 1) e' y)

/-- Rocq: `Analysis.Hardy.Pn_nonzero`. -/
theorem Pn_nonzero {n : Nat} {a b : VForm} (h : Pn n a b) : a ≠ Z := by
  cases h <;> intro h' <;> cases h'

/-- Rocq: `Analysis.Hardy.Pn_Z`. -/
theorem Pn_Z (n : Nat) (b : VForm) : ¬ Pn n Z b := fun h => Pn_nonzero h rfl

/-- Rocq: `Analysis.Hardy.Pn_fun`. -/
theorem Pn_fun {n : Nat} {a b : VForm} (h : Pn n a b) : ∀ {c}, Pn n a c → b = c := by
  induction h with
  | one =>
    intro c hc
    cases hc with
    | one => rfl
    | tail _ _ _ h' => exact absurd h' (Pn_Z _ _)
    | exp _ _ _ h' _ => exact absurd h' (Pn_Z _ _)
  | tail e x y h ih =>
    intro c hc
    cases hc with
    | one => exact absurd h (Pn_Z _ _)
    | tail _ _ y' h' => rw [ih h']
    | exp _ _ _ _ _ => exact absurd h (Pn_Z _ _)
  | exp e e' y h1 h2 ih1 ih2 =>
    intro c hc
    cases hc with
    | one => exact absurd h1 (Pn_Z _ _)
    | tail _ _ _ h' => exact absurd h' (Pn_Z _ _)
    | exp _ e2 y2 h1' h2' =>
      have he := ih1 h1'
      subst he
      rw [ih2 h2']

/-- Rocq: `Analysis.Hardy.Pn_lt`. -/
theorem Pn_lt {n : Nat} {a b : VForm} (h : Pn n a b) : sz b < sz a := by
  induction h with
  | one => exact denote_shrink1 Z Z
  | tail e x y _ ih => exact V_tail_lt e ih
  | exp e e' y _ _ ih1 ih2 => exact vrep_lt ih1 ih2 _

/-- Rocq: `Analysis.Hardy.Pn_exists_of_exps`. -/
theorem Pn_exists_of_exps (n : Nat) :
    ∀ a : VForm, a ≠ Z → (∀ c, sz (V c Z) ≤ sz a → ∃ y, Pn n (V c Z) y) → ∃ b, Pn n a b
  | Z, ha, _ => absurd rfl ha
  | V Z Z, _, _ => ⟨Z, .one⟩
  | V (V e1 e2) Z, _, H => H (V e1 e2) (le_refl _)
  | V e (V f x'), _, H =>
    let ⟨y, hy⟩ := Pn_exists_of_exps n (V f x') (fun h => VForm.noConfusion h)
      (fun c hc => H c (le_trans hc (tail_le_V e _)))
    ⟨V e y, .tail _ _ _ hy⟩

/-- Rocq: `Analysis.Hardy.Pn_exists_exp`. -/
theorem Pn_exists_exp (n : Nat) (e : VForm) : ∃ y, Pn n (V e Z) y := by
  refine VF_ind (fun e => ∃ y, Pn n (V e Z) y) (fun e IH => ?_) e
  match e, IH with
  | Z, _ => exact ⟨Z, .one⟩
  | V f x, IH =>
    obtain ⟨e', he'⟩ := Pn_exists_of_exps n (V f x) (fun h => VForm.noConfusion h)
      (fun c hc => IH c (lt_of_lt_of_le (exp_shrink c) hc))
    obtain ⟨y, hy⟩ := IH e' (Pn_lt he')
    exact ⟨_, .exp _ _ _ he' hy⟩

/-- Rocq: `Analysis.Hardy.Pn_exists`. -/
theorem Pn_exists (n : Nat) (a : VForm) (ha : a ≠ Z) : ∃ b, Pn n a b :=
  Pn_exists_of_exps n a ha (fun c _ => Pn_exists_exp n c)

/-- `P_0` and `P_1` agree. Rocq: `Analysis.Hardy.Pn_0_1`. -/
theorem Pn_0_1 {a b : VForm} (h : Pn 0 a b) : Pn 1 a b := by
  induction h with
  | one => exact .one
  | tail e x y _ ih => exact .tail _ _ _ ih
  | exp e e' y _ _ ih1 ih2 => exact .exp _ _ _ ih1 ih2

/-- Rocq: `Analysis.Hardy.Pn_vcat`. -/
theorem Pn_vcat {n : Nat} {x y : VForm} (h : Pn n x y) : ∀ g : VForm, Pn n (vcat g x) (vcat g y)
  | Z => h
  | V _ g => .tail _ _ _ (Pn_vcat h g)

/-! ## Reachability: `Reach n β α` is `β ≼_n α` -/

/-- Rocq: `Analysis.Hardy.reach`. -/
inductive Reach (n : Nat) : VForm → VForm → Prop
  /-- Rocq: `reach_refl`. -/
  | refl (a : VForm) : Reach n a a
  /-- Rocq: `reach_step`. -/
  | step (a b c : VForm) : Pn n a b → Reach n c b → Reach n c a

/-- Rocq: `Analysis.Hardy.reach_trans`. -/
theorem reach_trans {n : Nat} {a b c : VForm} (h1 : Reach n a b) (h2 : Reach n b c) : Reach n a c := by
  induction h2 with
  | refl => exact h1
  | step b' d c' hb _ ih => exact .step _ _ _ hb (ih h1)

/-- Rocq: `Analysis.Hardy.reach_one`. -/
theorem reach_one {n : Nat} {a b : VForm} (h : Pn n a b) : Reach n b a := .step _ _ _ h (.refl _)

/-- Rocq: `Analysis.Hardy.reach_vcat`. -/
theorem reach_vcat {n : Nat} (g : VForm) {x y : VForm} (h : Reach n y x) : Reach n (vcat g y) (vcat g x) := by
  induction h with
  | refl => exact .refl _
  | step x x' y hx _ ih => exact .step _ _ _ (Pn_vcat hx g) ih

/-- Rocq: `Analysis.Hardy.reach_le`. -/
theorem reach_le {n : Nat} {b a : VForm} (h : Reach n b a) : sz b ≤ sz a := by
  induction h with
  | refl => exact le_refl _
  | step a b c hab _ ih => exact le_trans ih (le_of_lt (Pn_lt hab))

/-- Rocq: `Analysis.Hardy.reach_Z`. -/
theorem reach_Z (n : Nat) (a : VForm) : Reach n Z a := by
  refine VF_ind (fun a => Reach n Z a) (fun a IH => ?_) a
  match a, IH with
  | Z, _ => exact .refl _
  | V e x, IH =>
    obtain ⟨b, hb⟩ := Pn_exists n (V e x) (fun h => VForm.noConfusion h)
    exact .step _ _ _ hb (IH b (Pn_lt hb))

/-- Rocq: `Analysis.Hardy.reach_prefix`. -/
theorem reach_prefix (n : Nat) (g x : VForm) : Reach n g (vcat g x) := by
  have h := reach_vcat g (reach_Z n x)
  rw [vcat_Z] at h
  exact h

/-- A reachable form is the start or is reached from its predecessor.
Rocq: `Analysis.Hardy.reach_inv`. -/
theorem reach_inv {n : Nat} {c a b : VForm} (h : Reach n c a) (hab : Pn n a b) : c = a ∨ Reach n c b := by
  cases h with
  | refl => exact .inl rfl
  | step _ b' _ hab' hc => exact .inr (Pn_fun hab hab' ▸ hc)

/-! ## The Bachmann property -/

theorem exists_add_two {n : Nat} (h : 2 ≤ n) : ∃ m, n = m + 2 := by
  obtain ⟨m, hm⟩ := Nat.le.dest h
  exact ⟨m, hm.symm.trans (Nat.add_comm 2 m)⟩

/-- Rocq: `Analysis.Hardy.reach_vrep_le`. -/
theorem reach_vrep_le (n : Nat) {j k : Nat} (e x : VForm) (h : j ≤ k) : Reach n (vrep j e Z) (vrep k e x) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [vrep_add, vrep_vcat j e (vrep d e x)]
  exact reach_prefix n _ _

/-- Rocq: `Analysis.Hardy.reach_exp_mono`. -/
theorem reach_exp_mono {n : Nat} (hn : 2 ≤ n) {e f : VForm} (h : Reach n e f) : Reach n (V e Z) (V f Z) := by
  obtain ⟨m, rfl⟩ := exists_add_two hn
  induction h with
  | refl => exact .refl _
  | step f f' e hf _ ih =>
    obtain ⟨y, hy⟩ := Pn_exists_exp (m + 2) f'
    exact .step _ _ _ (.exp _ _ _ hf hy)
      (reach_trans ih (reach_vrep_le (m + 2) (j := 1) (k := m + 1) f' y (Nat.succ_le_succ (Nat.zero_le m))))

/-- `ω^e·(n-1) + P_n(ω^e)` lies below `ω^f` when `e ≼_n P_n f`.
Rocq: `Analysis.Hardy.reach_vrep_exp`. -/
theorem reach_vrep_exp {n : Nat} (hn : 2 ≤ n) {e g : VForm} (h : Reach n e g) :
    ∀ {y f : VForm}, Pn n (V e Z) y → Pn n f g → Reach n (vrep (n - 1) e y) (V f Z) := by
  obtain ⟨m, rfl⟩ := exists_add_two hn
  induction h with
  | refl => intro y f hy hf; exact reach_one (.exp _ _ _ hf hy)
  | step g g' e hg _ ih =>
    intro y f hy hf
    refine reach_trans (ih hy hg) ?_
    obtain ⟨z, hz⟩ := Pn_exists_exp (m + 2) g
    exact .step _ _ _ (.exp _ _ _ hf hz)
      (reach_vrep_le (m + 2) (j := 1) (k := m + 1) g z (Nat.succ_le_succ (Nat.zero_le m)))

/-- Rocq: `Analysis.Hardy.Pn_bachmann`. -/
theorem Pn_bachmann {n : Nat} {a b c : VForm} (hb : Pn n a b) (hc : Pn (n + 1) a c) : Reach (n + 1) b c := by
  cases n with
  | zero => rw [Pn_fun (Pn_0_1 hb) hc]; exact .refl _
  | succ m =>
    induction hb generalizing c with
    | one =>
      cases hc with
      | one => exact .refl _
      | tail _ _ _ h' => exact absurd h' (Pn_Z _ _)
      | exp _ _ _ h' _ => exact absurd h' (Pn_Z _ _)
    | tail e x y h ih =>
      cases hc with
      | one => exact absurd h (Pn_Z _ _)
      | tail _ _ y2 h' => exact reach_vcat (V e Z) (ih h')
      | exp _ _ _ _ _ => exact absurd h (Pn_Z _ _)
    | exp e e' y h1 h2 ih1 ih2 =>
      cases hc with
      | one => exact absurd h1 (Pn_Z _ _)
      | tail _ _ _ h' => exact absurd h' (Pn_Z _ _)
      | exp _ e'' y2 He'' Hy2 =>
        show Reach (m + 2) (vrep m e' y) (vrep (m + 1) e'' y2)
        -- `y` lies below `ω^e' + z` for any `z`, via `P_(m+2)(ω^e')`
        have Hy : ∀ z, Reach (m + 2) y (V e' z) := by
          intro z
          obtain ⟨y', hy'⟩ := Pn_exists_exp (m + 2) e'
          exact reach_trans (ih2 hy') (reach_trans (reach_one hy') (reach_prefix _ (V e' Z) z))
        have Hlow : ∀ w, Reach (m + 2) (vrep m e' y) (vrep (m + 1) e' w) := by
          intro w
          rw [vrep_S_r, vrep_vcat m e' y, vrep_vcat m e' (V e' w)]
          exact reach_vcat _ (Hy w)
        cases ih1 He'' with
        | refl => exact Hlow y2
        | step _ g _ Hg Hrest =>
          obtain ⟨y', hy'⟩ := Pn_exists_exp (m + 2) e'
          exact reach_trans (Hlow y')
            (reach_trans (reach_vrep_exp (n := m + 2) (Nat.le_add_left 2 m) Hrest hy' Hg)
              (reach_prefix _ (V e'' Z) (vrep m e'' y2)))

/-- Hence `≼_n` grows with `n`. Rocq: `Analysis.Hardy.reach_S`. -/
theorem reach_S {n : Nat} {b a : VForm} (h : Reach n b a) : Reach (n + 1) b a := by
  induction h with
  | refl => exact .refl _
  | step a a1 b ha _ ih =>
    obtain ⟨c, hc⟩ := Pn_exists (n + 1) a (Pn_nonzero ha)
    exact .step _ _ _ hc (reach_trans ih (Pn_bachmann ha hc))

/-- Rocq: `Analysis.Hardy.reach_mono`. -/
theorem reach_mono {n m : Nat} {b a : VForm} (hnm : n ≤ m) (h : Reach n b a) : Reach m b a := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact reach_S ih

/-! ## The Hardy functions: `Hardy α n m` is `H_α(n) = m` -/

/-- Rocq: `Analysis.Hardy.hardy`. -/
inductive Hardy : VForm → Nat → Nat → Prop
  /-- Rocq: `hardy_Z`. -/
  | z (n : Nat) : Hardy Z n n
  /-- Rocq: `hardy_P`. -/
  | p (a b : VForm) (n m : Nat) : Pn n a b → Hardy b (n + 1) m → Hardy a n m

/-- Rocq: `Analysis.Hardy.hardy_fun`. -/
theorem hardy_fun {a : VForm} {n m : Nat} (h : Hardy a n m) : ∀ {m'}, Hardy a n m' → m = m' := by
  induction h with
  | z n =>
    intro m' h'
    cases h' with
    | z => rfl
    | p _ _ _ _ hb _ => exact absurd hb (Pn_Z _ _)
  | p a b n m hab _ ih =>
    intro m' h'
    cases h' with
    | z => exact absurd hab (Pn_Z _ _)
    | p _ b0 _ _ hb hm => exact ih (Pn_fun hab hb ▸ hm)

/-- Rocq: `Analysis.Hardy.hardy_exists`. -/
theorem hardy_exists (a : VForm) : ∀ n, ∃ m, Hardy a n m := by
  refine VF_ind (fun a => ∀ n, ∃ m, Hardy a n m) (fun a IH => ?_) a
  intro n
  match a, IH with
  | Z, _ => exact ⟨n, .z n⟩
  | V e x, IH =>
    obtain ⟨b, hb⟩ := Pn_exists n (V e x) (fun h => VForm.noConfusion h)
    obtain ⟨m, hm⟩ := IH b (Pn_lt hb) (n + 1)
    exact ⟨m, .p _ _ _ _ hb hm⟩

/-- Rocq: `Analysis.Hardy.hardy_ge`. -/
theorem hardy_ge {a : VForm} {n m : Nat} (h : Hardy a n m) : n ≤ m := by
  induction h with
  | z => exact Nat.le_refl _
  | p _ _ _ _ _ _ ih => exact Nat.le_of_succ_le ih

/-- Rocq: `Analysis.Hardy.hardy_gt`. -/
theorem hardy_gt {a : VForm} {n m : Nat} (h : Hardy a n m) (ha : a ≠ Z) : n < m := by
  cases h with
  | z => exact absurd rfl ha
  | p _ _ _ _ _ h => exact hardy_ge h

/-- Rocq: `Analysis.Hardy.hardy_P_inv`. -/
theorem hardy_P_inv {a b : VForm} {n m : Nat} (hab : Pn n a b) (h : Hardy a n m) : Hardy b (n + 1) m := by
  cases h with
  | z => exact absurd hab (Pn_Z _ _)
  | p _ b0 _ _ hb hm => exact Pn_fun hb hab ▸ hm

/-- `H_(γ+δ) = H_γ ∘ H_δ`. Rocq: `Analysis.Hardy.hardy_vcat`. -/
theorem hardy_vcat (g : VForm) {x : VForm} {n k m : Nat} (h : Hardy x n k) (hg : Hardy g k m) :
    Hardy (vcat g x) n m := by
  induction h with
  | z => rw [vcat_Z]; exact hg
  | p x y n k hxy _ ih => exact .p _ _ _ _ (Pn_vcat hxy g) (ih hg)

/-- Rocq: `Analysis.Hardy.hardy_vcat_inv`. -/
theorem hardy_vcat_inv (g x : VForm) {n m : Nat} (h : Hardy (vcat g x) n m) :
    ∃ k, Hardy x n k ∧ Hardy g k m := by
  obtain ⟨k, hk⟩ := hardy_exists x n
  obtain ⟨m', hm'⟩ := hardy_exists g k
  exact ⟨k, hk, hardy_fun (hardy_vcat g hk hm') h ▸ hm'⟩

/-- `H_α` is strictly increasing, and monotone along `≼_n`.
Rocq: `Analysis.Hardy.hardy_mono`. -/
theorem hardy_mono (a : VForm) :
    (∀ n m m', Hardy a n m → Hardy a (n + 1) m' → m < m') ∧
    (∀ n b mb ma, Reach n b a → Hardy b n mb → Hardy a n ma → mb ≤ ma) := by
  refine VF_ind (fun a => (∀ n m m', Hardy a n m → Hardy a (n + 1) m' → m < m') ∧
    (∀ n b mb ma, Reach n b a → Hardy b n mb → Hardy a n ma → mb ≤ ma)) (fun a IH => ?_) a
  have Hreach : ∀ n b mb ma, Reach n b a → Hardy b n mb → Hardy a n ma → mb ≤ ma := by
    intro n b mb ma hr hb ha
    cases hr with
    | refl => exact Nat.le_of_eq (hardy_fun hb ha)
    | step _ a1 _ ha1 hr =>
      obtain ⟨m1, hm1⟩ := hardy_exists a1 n
      have ih := IH a1 (Pn_lt ha1)
      exact Nat.le_trans (ih.2 n b mb m1 hr hb hm1) (Nat.le_of_lt (ih.1 n m1 ma hm1 (hardy_P_inv ha1 ha)))
  refine ⟨?_, Hreach⟩
  intro n m m' hm hm'
  match a, IH, hm, hm' with
  | Z, _, hm, hm' =>
    cases hm with
    | z =>
      cases hm' with
      | z => exact Nat.lt_succ_self n
      | p _ _ _ _ hb _ => exact absurd hb (Pn_Z _ _)
    | p _ _ _ _ hb _ => exact absurd hb (Pn_Z _ _)
  | V e x, IH, hm, hm' =>
    obtain ⟨a1, ha1⟩ := Pn_exists n (V e x) (fun h => VForm.noConfusion h)
    obtain ⟨a2, ha2⟩ := Pn_exists (n + 1) (V e x) (fun h => VForm.noConfusion h)
    have hm1 := hardy_P_inv ha1 hm
    have hm2 := hardy_P_inv ha2 hm'
    obtain ⟨k, hk⟩ := hardy_exists a2 (n + 1)
    have ih := IH a2 (Pn_lt ha2)
    exact Nat.lt_of_le_of_lt (ih.2 (n + 1) a1 m k (Pn_bachmann ha1 ha2) hm1 hk) (ih.1 (n + 1) k m' hk hm2)

/-- Rocq: `Analysis.Hardy.hardy_mono_arg`. -/
theorem hardy_mono_arg (a : VForm) {n n' m m' : Nat} (hn : n ≤ n') (hm : Hardy a n m) (hm' : Hardy a n' m') :
    m ≤ m' := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hn
  clear hn
  induction d generalizing m' with
  | zero => exact Nat.le_of_eq (hardy_fun hm hm')
  | succ d ih =>
    obtain ⟨k, hk⟩ := hardy_exists a (n + d)
    exact Nat.le_trans (ih hk) (Nat.le_of_lt ((hardy_mono a).1 (n + d) k m' hk hm'))

/-- Rocq: `Analysis.Hardy.hardy_mono_reach`. -/
theorem hardy_mono_reach {n : Nat} {b a : VForm} {mb ma : Nat} (h : Reach n b a) (hb : Hardy b n mb)
    (ha : Hardy a n ma) : mb ≤ ma :=
  (hardy_mono a).2 n b mb ma h hb ha

/-! ## Domination: `α < β` gives `α ≼_n β` for large `n` -/

/-- Rocq: `Analysis.Hardy.VF_eq_dec`. -/
def VF_eq_dec : (a b : VForm) → Decidable (a = b)
  | Z, Z => isTrue rfl
  | Z, V _ _ => isFalse (fun h => VForm.noConfusion h)
  | V _ _, Z => isFalse (fun h => VForm.noConfusion h)
  | V a x, V b y =>
    match VF_eq_dec a b, VF_eq_dec x y with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isTrue _, isFalse h2 => isFalse (fun h => h2 (VForm.V.inj h).2)
    | isFalse h1, isTrue _ => isFalse (fun h => h1 (VForm.V.inj h).1)
    | isFalse h1, isFalse _ => isFalse (fun h => h1 (VForm.V.inj h).1)

/-- Rocq: `Analysis.Hardy.VF_lt_irrefl`. -/
theorem VF_lt_irrefl (a : VForm) : ¬ sz a < sz a := lt_irrefl _

/-- Rocq: `Analysis.Hardy.VF_not_lt_Z`. -/
theorem VF_not_lt_Z (a : VForm) : ¬ sz a < sz Z := fun h =>
  lt_irrefl _ (lt_of_le_of_lt (zero_least (sz a)) h)

/-- Normal forms are compared by their leading exponents.
Rocq: `Analysis.Hardy.normal_lead_lt`. -/
theorem normal_lead_lt : ∀ (y f g : VForm), IsNormal (V f y) → sz f < sz g → sz (V f y) < sz (V g Z)
  | Z, _, _, _, hfg => exp_lt hfg
  | V h y', f, g, hn, hfg =>
    lt_of_le_of_lt (V_eq f _).le
      (lt_of_lt_of_le
        (below_exp_add g (pow_lt_pow_right omega_gt1 hfg)
          (lt_of_lt_of_le (normal_lead_lt y' h g hn.2.1 (lt_of_le_of_lt hn.2.2 hfg)) (VZ_eq g).le))
        (VZ_eq g).ge)

/-- Rocq: `Analysis.Hardy.VF_trichotomy`. -/
theorem VF_trichotomy (a b : VForm) (ha : IsNormal a) (hb : IsNormal b) :
    sz a < sz b ∨ a = b ∨ sz b < sz a :=
  match compare a b, compare_correct a b with
  | .lt, h => .inl h
  | .eq, h => .inr (.inl (normal_forms_unique a b ha hb h))
  | .gt, h => .inr (.inr h)

/-- Rocq: `Analysis.Hardy.VF_lt_of_le_neq`. -/
theorem VF_lt_of_le_neq {a b : VForm} (ha : IsNormal a) (hb : IsNormal b) (hle : sz a ≤ sz b) (hne : a ≠ b) :
    sz a < sz b :=
  match VF_trichotomy a b ha hb with
  | .inl h => h
  | .inr (.inl h) => absurd h hne
  | .inr (.inr h) => absurd (lt_of_le_of_lt hle h) (lt_irrefl _)

/-- A normal form `ω^g + x` is `ω^g·(k+1) + x'` with `x' < ω^g`.
Rocq: `Analysis.Hardy.normal_split`. -/
theorem normal_split (g : VForm) : ∀ x : VForm, IsNormal (V g x) →
    ∃ k x', V g x = vrep (k + 1) g x' ∧ sz x' < sz (V g Z) ∧ IsNormal x'
  | Z, _ => ⟨0, Z, rfl, lt_of_lt_of_le (pow_pos ω _) (VZ_eq g).ge, trivial⟩
  | V h x, hn =>
    match VF_eq_dec h g with
    | isTrue e => by
      subst e
      obtain ⟨k, x', heq, hlt, hx'⟩ := normal_split h x hn.2.1
      exact ⟨k + 1, x', congrArg (V h) heq, hlt, hx'⟩
    | isFalse ne =>
      ⟨0, V h x, rfl, normal_lead_lt x h g hn.2.1 (VF_lt_of_le_neq hn.2.1.1 hn.1 hn.2.2 ne), hn.2.1⟩

/-- Rocq: `Analysis.Hardy.VF_size_vrep`. -/
theorem VF_size_vrep (g x : VForm) : ∀ k : Nat, k + size x ≤ size (vrep k g x)
  | 0 => by rw [Nat.zero_add]; exact Nat.le_refl _
  | k + 1 => by
    rw [Nat.succ_add]
    exact Nat.succ_le_succ (Nat.le_trans (VF_size_vrep g x k) (Nat.le_add_left _ _))

/-- Everything below `ω^g·(j+1) + P_n(ω^g)` down to `ω^g·j` is reached.
Rocq: `Analysis.Hardy.reach_below_exp`. -/
theorem reach_below_exp {n : Nat} (j : Nat) {g y x : VForm} (hy : Pn n (V g Z) y) (hx : Reach n x y) :
    Reach n x (vrep j g y) :=
  match j with
  | 0 => hx
  | j + 1 => reach_trans (.step _ _ _ hy hx) (reach_vrep_le n (j := 1) (k := j + 1) g y
      (Nat.succ_le_succ (Nat.zero_le j)))

private theorem size_lt_V_left {g x : VForm} {n : Nat} (h : size (V g x) < n) : size g < n :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)) h

private theorem size_lt_V_right {g x : VForm} {n : Nat} (h : size (V g x) < n) : size x < n :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _)) h

/-- Rocq: `Analysis.Hardy.reach_of_lt`. -/
theorem reach_of_lt (b : VForm) : ∀ (a : VForm) (n : Nat), IsNormal a → IsNormal b → sz a < sz b →
    size a < n → Reach n a b := by
  refine VF_ind (fun b => ∀ (a : VForm) (n : Nat), IsNormal a → IsNormal b → sz a < sz b →
    size a < n → Reach n a b) (fun b IH => ?_) b
  intro a n Ha Hb Hab Hn
  match a, b, IH, Ha, Hb, Hab, Hn with
  | Z, _, _, _, _, _, _ => exact reach_Z n _
  | V g x, Z, _, _, _, Hab, _ => exact absurd Hab (VF_not_lt_Z _)
  | V g x, V f y, IH, Ha, Hb, Hab, Hn =>
    match VF_trichotomy g f Ha.1 Hb.1 with
    | .inl Hgf =>
      obtain ⟨k, x', Heq, Hx'lt, Hx'⟩ := normal_split g x Ha
      have Hsz := VF_size_vrep g x' (k + 1)
      rw [← Heq] at Hsz
      have Hrg : Reach n g f := IH f (denote_shrink1 f y) g n Ha.1 Hb.1 Hgf (size_lt_V_left Hn)
      cases Hrg with
      | refl => exact absurd Hgf (lt_irrefl _)
      | step _ f3 _ Hf3 Hgf3 =>
        obtain ⟨yg, Hyg⟩ := Pn_exists_exp n g
        have Hx'r : Reach n x' (V g Z) :=
          IH (V g Z) (lt_of_lt_of_le (exp_lt Hgf) (exp_le_V f y)) x' n Hx' ⟨Ha.1, trivial, trivial⟩ Hx'lt
            (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) Hsz) Hn)
        cases reach_inv Hx'r Hyg with
        | inl e => exact absurd (e ▸ Hx'lt) (lt_irrefl _)
        | inr Hx'yg =>
          -- `n = m + 2` with `k ≤ m`
          have Hk : k + 2 ≤ n := Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) Hsz) Hn
          obtain ⟨m, rfl⟩ := exists_add_two (Nat.le_trans (Nat.le_add_left 2 k) Hk)
          obtain ⟨d, hd⟩ := Nat.le.dest (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ Hk))
          rw [Heq]
          refine reach_trans ?_ (reach_trans (reach_vrep_exp (Nat.le_add_left 2 m) Hgf3 Hyg Hf3)
            (reach_prefix _ (V f Z) y))
          show Reach (m + 2) (vrep (k + 1) g x') (vrep (m + 1) g yg)
          subst hd
          rw [Nat.add_right_comm k d 1, vrep_add (k + 1) d g yg, vrep_vcat (k + 1) g x',
            vrep_vcat (k + 1) g (vrep d g yg)]
          exact reach_vcat _ (reach_below_exp d Hyg Hx'yg)
    | .inr (.inl e) =>
      subst e
      have Hxy : sz x < sz y :=
        match decideOrder x y with
        | .inl h => h
        | .inr h => absurd (lt_of_lt_of_le Hab
            (le_trans (V_eq g y).le (le_trans (add_le_add (le_refl _) h) (V_eq g x).ge))) (lt_irrefl _)
      exact reach_vcat (V g Z) (IH y (denote_shrink2 y g Hb) x n Ha.2.1 Hb.2.1 Hxy (size_lt_V_right Hn))
    | .inr (.inr Hfg) =>
      exact absurd (lt_trans Hab (lt_of_lt_of_le (normal_lead_lt y f g Hb Hfg) (exp_le_V g x))) (lt_irrefl _)

/-- Rocq: `Analysis.Hardy.hardy_dominated`. -/
theorem hardy_dominated {a b : VForm} {n ma mb : Nat} (ha : IsNormal a) (hb : IsNormal b) (hab : sz a < sz b)
    (hn : size a < n) (hma : Hardy a n ma) (hmb : Hardy b n mb) : ma ≤ mb :=
  hardy_mono_reach (reach_of_lt b a n ha hb hab hn) hma hmb

/-! ## The strict relation `β ≺_n α` -/

/-- Rocq: `Analysis.Hardy.olt`. -/
def Olt (n : Nat) (b a : VForm) : Prop := ∃ a1, Pn n a a1 ∧ Reach n b a1

/-- Rocq: `Analysis.Hardy.olt_reach`. -/
theorem olt_reach {n : Nat} {b a : VForm} (h : Olt n b a) : Reach n b a :=
  let ⟨_, h1, h2⟩ := h
  reach_trans h2 (reach_one h1)

/-- Rocq: `Analysis.Hardy.olt_nonzero`. -/
theorem olt_nonzero {n : Nat} {b a : VForm} (h : Olt n b a) : a ≠ Z :=
  let ⟨_, h1, _⟩ := h
  Pn_nonzero h1

/-- Rocq: `Analysis.Hardy.olt_reach_trans`. -/
theorem olt_reach_trans {n : Nat} {b a a' : VForm} (h1 : Olt n b a) (h2 : Reach n a a') : Olt n b a' := by
  cases h2 with
  | refl => exact h1
  | step _ a'1 _ hstep hr => exact ⟨a'1, hstep, reach_trans (olt_reach h1) hr⟩

/-- Rocq: `Analysis.Hardy.reach_olt_trans`. -/
theorem reach_olt_trans {n : Nat} {c b a : VForm} (h1 : Reach n c b) (h2 : Olt n b a) : Olt n c a :=
  let ⟨a1, h3, h4⟩ := h2
  ⟨a1, h3, reach_trans h1 h4⟩

/-- Rocq: `Analysis.Hardy.Pn_reach_mono`. -/
theorem Pn_reach_mono {n m : Nat} {a a1 a2 : VForm} (hnm : n ≤ m) (h1 : Pn n a a1) (h2 : Pn m a a2) :
    Reach m a1 a2 := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hnm
  clear hnm
  induction d generalizing a2 with
  | zero => rw [Pn_fun h1 h2]; exact .refl _
  | succ d ih =>
    obtain ⟨a3, h3⟩ := Pn_exists (n + d) a (Pn_nonzero h1)
    exact reach_trans (reach_S (ih h3)) (Pn_bachmann h3 h2)

/-- Rocq: `Analysis.Hardy.olt_mono`. -/
theorem olt_mono {n m : Nat} {b a : VForm} (hnm : n ≤ m) (h : Olt n b a) : Olt m b a :=
  let ⟨_, h1, h2⟩ := h
  let ⟨a2, h3⟩ := Pn_exists m a (Pn_nonzero h1)
  ⟨a2, h3, reach_trans (reach_mono hnm h2) (Pn_reach_mono hnm h1 h3)⟩

/-- Rocq: `Analysis.Hardy.olt_vcat`. -/
theorem olt_vcat {n : Nat} (g : VForm) {b a : VForm} (h : Olt n b a) : Olt n (vcat g b) (vcat g a) :=
  let ⟨a1, h1, h2⟩ := h
  ⟨vcat g a1, Pn_vcat h1 g, reach_vcat g h2⟩

/-- Rocq: `Analysis.Hardy.olt_Z`. -/
theorem olt_Z (n : Nat) {a : VForm} (ha : a ≠ Z) : Olt n Z a :=
  let ⟨a1, h⟩ := Pn_exists n a ha
  ⟨a1, h, reach_Z n a1⟩

/-- Rocq: `Analysis.Hardy.olt_vcat_r`. -/
theorem olt_vcat_r (n : Nat) (a : VForm) {b : VForm} (hb : b ≠ Z) : Olt n a (vcat a b) := by
  have h := olt_vcat a (olt_Z n hb)
  rw [vcat_Z] at h
  exact h

/-- Rocq: `Analysis.Hardy.olt_exp`. -/
theorem olt_exp {n : Nat} (hn : 2 ≤ n) {b a : VForm} (h : Olt n b a) : Olt n (V b Z) (V a Z) := by
  obtain ⟨a1, h1, h2⟩ := h
  obtain ⟨y, hy⟩ := Pn_exists_exp n a1
  obtain ⟨m, rfl⟩ := exists_add_two hn
  exact ⟨vrep (m + 1) a1 y, .exp _ _ _ h1 hy,
    reach_trans (reach_exp_mono (Nat.le_add_left 2 m) h2)
      (reach_vrep_le (m + 2) (j := 1) (k := m + 1) a1 y (Nat.succ_le_succ (Nat.zero_le m)))⟩

/-- Rocq: `Analysis.Hardy.olt_two`. -/
theorem olt_two {n : Nat} (hn : 3 ≤ n) {a a1 : VForm} (h1 : Pn n a a1) :
    Olt n (vcat (V a1 Z) (V a1 Z)) (V a Z) := by
  obtain ⟨y, hy⟩ := Pn_exists_exp n a1
  obtain ⟨m, hm⟩ := Nat.le.dest hn
  have e : n = m + 3 := hm.symm.trans (Nat.add_comm 3 m)
  subst e
  exact ⟨vrep (m + 2) a1 y, .exp _ _ _ h1 hy, reach_vrep_le (m + 3) (j := 2) (k := m + 2) a1 y (Nat.le_add_left 2 m)⟩

/-- Rocq: `Analysis.Hardy.olt_hardy`. -/
theorem olt_hardy {n : Nat} {b a : VForm} {hb ha : Nat} (h : Olt n b a) (hhb : Hardy b n hb) (hha : Hardy a n ha) :
    hb ≤ ha :=
  hardy_mono_reach (olt_reach h) hhb hha

/-- `H_δ(x) ≥ x`, so a summand on the left only increases `H`.
Rocq: `Analysis.Hardy.hardy_vcat_ge`. -/
theorem hardy_vcat_ge (g x : VForm) {n h hx : Nat} (H : Hardy (vcat g x) n h) (Hx : Hardy x n hx) : hx ≤ h :=
  let ⟨_, hk, hg⟩ := hardy_vcat_inv g x H
  hardy_fun Hx hk ▸ hardy_ge hg

/-- `H_α(n) ≤ H_(ω^α)(n)`. Rocq: `Analysis.Hardy.hardy_exp_ge`. -/
theorem hardy_exp_ge (a : VForm) : ∀ (n h h' : Nat), 2 ≤ n → Hardy a n h → Hardy (V a Z) n h' → h ≤ h' := by
  refine VF_ind (fun a => ∀ (n h h' : Nat), 2 ≤ n → Hardy a n h → Hardy (V a Z) n h' → h ≤ h')
    (fun a IH => ?_) a
  intro n h h' hn ha ha'
  match a, IH, ha, ha' with
  | Z, _, ha, ha' =>
    cases ha with
    | z => exact hardy_ge ha'
    | p _ _ _ _ hb _ => exact absurd hb (Pn_Z _ _)
  | V e x, IH, ha, ha' =>
    obtain ⟨m, rfl⟩ := exists_add_two hn
    obtain ⟨a1, ha1⟩ := Pn_exists (m + 2) (V e x) (fun h => VForm.noConfusion h)
    obtain ⟨y, hy⟩ := Pn_exists_exp (m + 2) a1
    have hh := hardy_P_inv ha1 ha
    have hh' : Hardy (vcat (V a1 Z) (vrep m a1 y)) (m + 3) h' := hardy_P_inv (.exp _ _ _ ha1 hy) ha'
    obtain ⟨k, hk⟩ := hardy_exists (V a1 Z) (m + 3)
    obtain ⟨k', hk', hg⟩ := hardy_vcat_inv _ _ hh'
    exact Nat.le_trans (IH a1 (Pn_lt ha1) (m + 3) h k (Nat.le_add_left 2 (m + 1)) hh hk)
      (hardy_mono_arg (V a1 Z) (hardy_ge hk') hk hg)

end ConstructiveOrdinals.Hardy
