import ConstructiveOrdinals.Notation.ATower

/-!
# Grimm's syntactic presentation of Ackermann's system

Port of `Ordinal/Notation/GrimmT3.v`.

J. Grimm (INRIA RR-8407, 2013; GAIA `theories/schutte/ssete9.v`,
`Module Ackermann`) formalizes Ackermann's 1951 notation system syntactically,
shifted to start from `0`. A term `cons a b c n d` stands for
`ψ(a,b,c)·(n+1) + d`; the comparison is Ackermann's rule G6 (cases a–i) for
brackets, lexicographic on sums.

This file ports Grimm's syntax, comparison and normal forms, and translates
them into `ATowerNotation`'s forms. Ackermann's brackets skip fixed points,
whereas `VForm` uses Veblen's functions and forbids fixed-point arguments, so
the translation shifts indices twice: β-absorption (when `φ(a,b,0) = b` the
γ index starts at `1`) and γ-skipping (when the shifted γ is `λ + m`, with `λ`
a fixed point and `m` finite, it is incremented once more).

Main results:
- `T3lt_total`: Grimm's comparison is total (on all terms);
- `T3_to_VF_normal`: normal forms translate to `VForm` normal forms;
- `T3lt_correct`: on normal forms, Grimm's comparison agrees with the semantic
  order, in both directions;
- `T3_denote_inj`: normal forms are determined by their denotation;
- `T3_AO`: the normal forms have order type `AckermannOrdinal`.

Lean notes:
- Booleans are reasoned about by case analysis (`band_true`, `bor_true`, …),
  since `simp` and `decide` on propositions are not available.
- `shiftOmega` and `shiftGen` are defined through `skip`, so Rocq's
  `shift_omega_skip` and `shift_gen_skip` hold by `rfl`.
- The sanity `Example`s of the Rocq file are `example`s here, checked by `rfl`.
-/

namespace ConstructiveOrdinals.GrimmT3

/-! ## Boolean helpers -/

theorem band_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  revert h; cases a <;> cases b <;> intro h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact ⟨rfl, rfl⟩

theorem band_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

theorem bor_true {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  revert h; cases a <;> cases b <;> intro h
  · exact Bool.noConfusion h
  · exact .inr rfl
  · exact .inl rfl
  · exact .inl rfl

theorem bor_left {a : Bool} (b : Bool) (h : a = true) : (a || b) = true := by rw [h]; rfl

theorem bor_right (a : Bool) {b : Bool} (h : b = true) : (a || b) = true := by
  rw [h]; cases a <;> rfl

theorem nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_refl n

/-! ## Syntax, comparison, normal forms (after Grimm) -/

/-
Third-party notice. The definitions `T3`, `eqb`, `ltPsiRec`, `ltRec`, `lta`,
`lt` and `nf` below are adapted, via `Ordinal/Notation/GrimmT3.v`, from GAIA,
`theories/schutte/ssete9.v`, `Module Ackermann`
(https://github.com/coq-community/gaia), which carries these notices:

  Copyright INRIA (2013-2013) Marelle Team (José Grimm).
  Copyright (c) 2017 Yves Bertot

and is distributed under the MIT License:

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
-/

/-- Grimm's terms: `cons a b c n d` stands for `ψ(a,b,c)·(n+1) + d`.
Rocq: `Notation.GrimmT3.T3`. -/
inductive T3 : Type where
  /-- Rocq: `T3zero`. -/
  | zero : T3
  /-- Rocq: `T3cons`. -/
  | cons : T3 → T3 → T3 → Nat → T3 → T3

namespace T3

/-- Rocq: `Notation.GrimmT3.T3eqb`. -/
def eqb : T3 → T3 → Bool
  | zero, zero => true
  | zero, cons _ _ _ _ _ => false
  | cons _ _ _ _ _, zero => false
  | cons a b c n d, cons a' b' c' n' d' =>
    eqb a a' && eqb b b' && eqb c c' && Nat.beq n n' && eqb d d'

/-- Rocq: `Notation.GrimmT3.T3size`. -/
def size : T3 → Nat
  | zero => 0
  | cons a b c _ d => size a + size b + size c + size d + 1

/-- The bracket `ψ(a,b,c)`. Rocq: `Notation.GrimmT3.T3psi`. -/
def psi (a b c : T3) : T3 := cons a b c 0 zero

end T3

open T3

/-- Rule G6 for brackets, given a comparison `f` for smaller pairs.
Rocq: `Notation.GrimmT3.lt_psi_rec`. -/
def ltPsiRec (f : T3 → T3 → Bool) (a b c a' b' c' : T3) : Bool :=
  (eqb a a' && eqb b b' && f c c') ||
  (eqb a a' && f b b' && f c (psi a' b' c')) ||
  (eqb a a' && f b' b && f (psi a b c) c') ||
  (eqb a a' && f b' b && eqb (psi a b c) c') ||
  (f a a' && f b (psi a' b' c') && f c (psi a' b' c')) ||
  (f a' a && f (psi a b c) b') ||
  (f a' a && eqb (psi a b c) b') ||
  (f a' a && f (psi a b c) c') ||
  (f a' a && eqb (psi a b c) c')

/-- One step of the comparison. Rocq: `Notation.GrimmT3.lt_rec`. -/
def ltRec (f : T3 → T3 → Bool) : T3 → T3 → Bool
  | cons a b c n d, cons a' b' c' n' d' =>
    if ltPsiRec f a b c a' b' c' = true then true
    else if (eqb a a' && eqb b b' && eqb c c') = true then
      if n < n' then true
      else if n = n' then f d d' else false
    else false
  | zero, cons _ _ _ _ _ => true
  | zero, zero => false
  | cons _ _ _ _ _, zero => false

/-- Rocq: `Notation.GrimmT3.T3lta`. -/
def lta : Nat → T3 → T3 → Bool
  | 0 => fun _ _ => false
  | k + 1 => ltRec (lta k)

/-- Grimm's comparison. Rocq: `Notation.GrimmT3.T3lt`. -/
def lt (x y : T3) : Bool := lta (size x + size y + 1) x y

/-! ### Size bounds -/

theorem size_a (a b c : T3) (n : Nat) (d : T3) : size a < size (cons a b c n d) :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _)
    (Nat.le_add_right _ _)))

theorem size_b (a b c : T3) (n : Nat) (d : T3) : size b < size (cons a b c n d) :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _)
    (Nat.le_add_right _ _)))

theorem size_c (a b c : T3) (n : Nat) (d : T3) : size c < size (cons a b c n d) :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))

theorem size_d (a b c : T3) (n : Nat) (d : T3) : size d < size (cons a b c n d) :=
  Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem size_psi (a b c : T3) (n : Nat) (d : T3) : size (psi a b c) ≤ size (cons a b c n d) :=
  Nat.succ_le_succ (Nat.add_le_add_left (Nat.zero_le _) _)

/-- A pair with one strictly smaller and one no larger component is smaller. -/
theorem pair_lt {u v X Y : Nat} (hu : u < X) (hv : v ≤ Y) : u + v < X + Y :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right hu v) (Nat.add_le_add_left hv X)

theorem pair_lt' {u v X Y : Nat} (hu : u ≤ X) (hv : v < Y) : u + v < X + Y :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right hu v) (Nat.add_lt_add_left hv X)

theorem pair_lt_swap {u v X Y : Nat} (h : u + v < Y + X) : u + v < X + Y := by
  rw [Nat.add_comm X Y]; exact h

/-- Rocq: `Notation.GrimmT3.lt_rec_ext`. -/
theorem ltRec_ext (f g : T3 → T3 → Bool) (x y : T3)
    (h : ∀ u v, size u + size v < size x + size y → f u v = g u v) :
    ltRec f x y = ltRec g x y := by
  cases x with
  | zero => cases y <;> rfl
  | cons a b c n d =>
    cases y with
    | zero => rfl
    | cons a' b' c' n' d' =>
      have Sx := size_a a b c n d; have Sb := size_b a b c n d; have Sc := size_c a b c n d
      have Sd := size_d a b c n d; have Sp := size_psi a b c n d
      have Sx' := size_a a' b' c' n' d'; have Sb' := size_b a' b' c' n' d'
      have Sc' := size_c a' b' c' n' d'; have Sd' := size_d a' b' c' n' d'
      have Sp' := size_psi a' b' c' n' d'
      have e1 := h c c' (pair_lt Sc (Nat.le_of_lt Sc'))
      have e2 := h b b' (pair_lt Sb (Nat.le_of_lt Sb'))
      have e3 := h c (psi a' b' c') (pair_lt Sc Sp')
      have e4 := h b' b (pair_lt_swap (pair_lt Sb' (Nat.le_of_lt Sb)))
      have e5 := h (psi a b c) c' (pair_lt' Sp Sc')
      have e6 := h a a' (pair_lt Sx (Nat.le_of_lt Sx'))
      have e7 := h b (psi a' b' c') (pair_lt Sb Sp')
      have e8 := h a' a (pair_lt_swap (pair_lt Sx' (Nat.le_of_lt Sx)))
      have e9 := h (psi a b c) b' (pair_lt' Sp Sb')
      have e10 := h d d' (pair_lt Sd (Nat.le_of_lt Sd'))
      show (if ltPsiRec f a b c a' b' c' = true then true
          else if (eqb a a' && eqb b b' && eqb c c') = true then
            if n < n' then true else if n = n' then f d d' else false
          else false) =
        (if ltPsiRec g a b c a' b' c' = true then true
          else if (eqb a a' && eqb b b' && eqb c c') = true then
            if n < n' then true else if n = n' then g d d' else false
          else false)
      unfold ltPsiRec
      rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

/-- Rocq: `Notation.GrimmT3.T3lta_fuel`. -/
theorem lta_fuel : ∀ (k k' : Nat) (x y : T3), size x + size y < k → k ≤ k' →
    lta k x y = lta k' x y
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, hk => absurd hk (Nat.not_succ_le_zero _)
  | k + 1, k' + 1, x, y, h, hk =>
    ltRec_ext (lta k) (lta k') x y fun u v huv =>
      lta_fuel k k' u v (Nat.lt_of_lt_of_le huv (Nat.le_of_lt_succ h)) (Nat.le_of_succ_le_succ hk)

/-- Fuel independence: `lt` satisfies its defining recursion.
Rocq: `Notation.GrimmT3.T3lt_unfold`. -/
theorem lt_unfold (x y : T3) : lt x y = ltRec lt x y :=
  ltRec_ext _ _ x y fun u v huv =>
    (lta_fuel _ _ u v (Nat.lt_succ_self _) (Nat.succ_le_of_lt huv)).symm

/-- Rocq: `Notation.GrimmT3.T3eqb_eq`. -/
theorem eqb_eq : ∀ x y : T3, eqb x y = true ↔ x = y
  | zero, zero => ⟨fun _ => rfl, fun _ => rfl⟩
  | zero, cons _ _ _ _ _ => ⟨fun h => Bool.noConfusion h, fun h => T3.noConfusion h⟩
  | cons _ _ _ _ _, zero => ⟨fun h => Bool.noConfusion h, fun h => T3.noConfusion h⟩
  | cons a b c n d, cons a' b' c' n' d' => by
    constructor
    · intro h
      obtain ⟨h, hd⟩ := band_true h
      obtain ⟨h, hn⟩ := band_true h
      obtain ⟨h, hc⟩ := band_true h
      obtain ⟨ha, hb⟩ := band_true h
      rw [(eqb_eq a a').1 ha, (eqb_eq b b').1 hb, (eqb_eq c c').1 hc, Nat.eq_of_beq_eq_true hn,
        (eqb_eq d d').1 hd]
    · intro h
      injection h with ha hb hc hn hd
      exact band_intro (band_intro (band_intro (band_intro ((eqb_eq a a').2 ha) ((eqb_eq b b').2 hb))
        ((eqb_eq c c').2 hc)) (by rw [hn]; exact nat_beq_refl n')) ((eqb_eq d d').2 hd)

/-- Rocq: `Notation.GrimmT3.T3eqb_refl`. -/
theorem eqb_refl (x : T3) : eqb x x = true := (eqb_eq x x).2 rfl

/-- Rocq: `Notation.GrimmT3.T3lt_cons`. -/
theorem lt_cons (a b c : T3) (n : Nat) (d a' b' c' : T3) (n' : Nat) (d' : T3) :
    lt (cons a b c n d) (cons a' b' c' n' d') =
      if ltPsiRec lt a b c a' b' c' = true then true
      else if (eqb a a' && eqb b b' && eqb c c') = true then
        if n < n' then true else if n = n' then lt d d' else false
      else false := by
  rw [lt_unfold]; rfl

/-- Rocq: `Notation.GrimmT3.T3lt_zero_cons`. -/
theorem lt_zero_cons (a b c : T3) (n : Nat) (d : T3) : lt zero (cons a b c n d) = true := by
  rw [lt_unfold]; rfl

/-- Rocq: `Notation.GrimmT3.T3lt_zero_r`. -/
theorem lt_zero_r (x : T3) : lt x zero = false := by
  rw [lt_unfold]; cases x <;> rfl

/-! ### The nine cases of rule G6, as introduction rules -/

section ltPsiIntro

variable (f : T3 → T3 → Bool) (a b c a' b' c' : T3)

private theorem ltPsi_or (h1 h2 h3 h4 h5 h6 h7 h8 h9 : Bool)
    (h : h1 = true ∨ h2 = true ∨ h3 = true ∨ h4 = true ∨ h5 = true ∨ h6 = true ∨ h7 = true ∨
      h8 = true ∨ h9 = true) :
    (h1 || h2 || h3 || h4 || h5 || h6 || h7 || h8 || h9) = true := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _
      (bor_left _ h)))))))
  · exact bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _
      (bor_right _ h)))))))
  · exact bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _
      (bor_right _ h))))))
  · exact bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_right _ h)))))
  · exact bor_left _ (bor_left _ (bor_left _ (bor_left _ (bor_right _ h))))
  · exact bor_left _ (bor_left _ (bor_left _ (bor_right _ h)))
  · exact bor_left _ (bor_left _ (bor_right _ h))
  · exact bor_left _ (bor_right _ h)
  · exact bor_right _ h

/-- Rocq: `Notation.GrimmT3.lt_psi_a`. -/
theorem ltPsi_a (ha : a = a') (hb : b = b') (hc : f c c' = true) :
    ltPsiRec f a b c a' b' c' = true := by
  subst ha hb
  exact ltPsi_or _ _ _ _ _ _ _ _ _ (.inl (band_intro (band_intro (eqb_refl a) (eqb_refl b)) hc))

/-- Rocq: `Notation.GrimmT3.lt_psi_b`. -/
theorem ltPsi_b (ha : a = a') (hb : f b b' = true) (hc : f c (psi a' b' c') = true) :
    ltPsiRec f a b c a' b' c' = true := by
  subst ha
  exact ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inl (band_intro (band_intro (eqb_refl a) hb) hc)))

/-- Rocq: `Notation.GrimmT3.lt_psi_c`. -/
theorem ltPsi_c (ha : a = a') (hb : f b' b = true) (hc : f (psi a b c) c' = true) :
    ltPsiRec f a b c a' b' c' = true := by
  subst ha
  exact ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inl (band_intro (band_intro (eqb_refl a) hb) hc))))

/-- Rocq: `Notation.GrimmT3.lt_psi_d`. -/
theorem ltPsi_d (ha : a = a') (hb : f b' b = true) (hc : psi a b c = c') :
    ltPsiRec f a b c a' b' c' = true := by
  subst ha
  exact ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inl
    (band_intro (band_intro (eqb_refl a) hb) ((eqb_eq _ _).2 hc))))))

/-- Rocq: `Notation.GrimmT3.lt_psi_e`. -/
theorem ltPsi_e (ha : f a a' = true) (hb : f b (psi a' b' c') = true)
    (hc : f c (psi a' b' c') = true) : ltPsiRec f a b c a' b' c' = true :=
  ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inr (.inl (band_intro (band_intro ha hb) hc))))))

/-- Rocq: `Notation.GrimmT3.lt_psi_f`. -/
theorem ltPsi_f (ha : f a' a = true) (hb : f (psi a b c) b' = true) :
    ltPsiRec f a b c a' b' c' = true :=
  ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inr (.inr (.inl (band_intro ha hb)))))))

/-- Rocq: `Notation.GrimmT3.lt_psi_g`. -/
theorem ltPsi_g (ha : f a' a = true) (hb : psi a b c = b') : ltPsiRec f a b c a' b' c' = true :=
  ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl
    (band_intro ha ((eqb_eq _ _).2 hb)))))))))

/-- Rocq: `Notation.GrimmT3.lt_psi_h`. -/
theorem ltPsi_h (ha : f a' a = true) (hc : f (psi a b c) c' = true) :
    ltPsiRec f a b c a' b' c' = true :=
  ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
    (band_intro ha hc)))))))))

/-- Rocq: `Notation.GrimmT3.lt_psi_i`. -/
theorem ltPsi_i (ha : f a' a = true) (hc : psi a b c = c') : ltPsiRec f a b c a' b' c' = true :=
  ltPsi_or _ _ _ _ _ _ _ _ _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
    (band_intro ha ((eqb_eq _ _).2 hc))))))))))

end ltPsiIntro

/-! ### Totality of Grimm's comparison (on all terms) -/

/-- Rocq: `Notation.GrimmT3.T3trich`. -/
def Trich (x y : T3) : Prop := lt x y = true ∨ x = y ∨ lt y x = true

/-- Rocq: `Notation.GrimmT3.lt_psi_total`. -/
theorem ltPsi_total (a b c a' b' c' : T3) (Ha : Trich a a') (Hb : Trich b b') (Hc : Trich c c')
    (Hby : Trich b (psi a' b' c')) (Hcy : Trich c (psi a' b' c'))
    (Hbx : Trich b' (psi a b c)) (Hcx : Trich c' (psi a b c)) :
    ltPsiRec lt a b c a' b' c' = true ∨ (a = a' ∧ b = b' ∧ c = c') ∨
      ltPsiRec lt a' b' c' a b c = true := by
  rcases Ha with Ha | Ha | Ha
  · rcases Hby with Hby | Hby | Hby
    · rcases Hcy with Hcy | Hcy | Hcy
      · exact .inl (ltPsi_e _ _ _ _ _ _ _ Ha Hby Hcy)
      · exact .inr (.inr (ltPsi_i _ _ _ _ _ _ _ Ha Hcy.symm))
      · exact .inr (.inr (ltPsi_h _ _ _ _ _ _ _ Ha Hcy))
    · exact .inr (.inr (ltPsi_g _ _ _ _ _ _ _ Ha Hby.symm))
    · exact .inr (.inr (ltPsi_f _ _ _ _ _ _ _ Ha Hby))
  · subst Ha
    rcases Hb with Hb | Hb | Hb
    · rcases Hcy with Hcy | Hcy | Hcy
      · exact .inl (ltPsi_b _ _ _ _ _ _ _ rfl Hb Hcy)
      · exact .inr (.inr (ltPsi_d _ _ _ _ _ _ _ rfl Hb Hcy.symm))
      · exact .inr (.inr (ltPsi_c _ _ _ _ _ _ _ rfl Hb Hcy))
    · subst Hb
      rcases Hc with Hc | Hc | Hc
      · exact .inl (ltPsi_a _ _ _ _ _ _ _ rfl rfl Hc)
      · exact .inr (.inl ⟨rfl, rfl, Hc⟩)
      · exact .inr (.inr (ltPsi_a _ _ _ _ _ _ _ rfl rfl Hc))
    · rcases Hcx with Hcx | Hcx | Hcx
      · exact .inr (.inr (ltPsi_b _ _ _ _ _ _ _ rfl Hb Hcx))
      · exact .inl (ltPsi_d _ _ _ _ _ _ _ rfl Hb Hcx.symm)
      · exact .inl (ltPsi_c _ _ _ _ _ _ _ rfl Hb Hcx)
  · rcases Hbx with Hbx | Hbx | Hbx
    · rcases Hcx with Hcx | Hcx | Hcx
      · exact .inr (.inr (ltPsi_e _ _ _ _ _ _ _ Ha Hbx Hcx))
      · exact .inl (ltPsi_i _ _ _ _ _ _ _ Ha Hcx.symm)
      · exact .inl (ltPsi_h _ _ _ _ _ _ _ Ha Hcx)
    · exact .inl (ltPsi_g _ _ _ _ _ _ _ Ha Hbx.symm)
    · exact .inl (ltPsi_f _ _ _ _ _ _ _ Ha Hbx)

private theorem lt_cons_psi {a b c : T3} {n : Nat} {d a' b' c' : T3} {n' : Nat} {d' : T3}
    (h : ltPsiRec lt a b c a' b' c' = true) : lt (cons a b c n d) (cons a' b' c' n' d') = true := by
  rw [lt_cons, h]; rfl

private theorem lt_cons_same (a b c : T3) {n : Nat} {d : T3} {n' : Nat} {d' : T3}
    (h : n < n' ∨ (n = n' ∧ lt d d' = true)) : lt (cons a b c n d) (cons a b c n' d') = true := by
  rw [lt_cons]
  cases hp : ltPsiRec lt a b c a b c with
  | true => rfl
  | false =>
    show (if (eqb a a && eqb b b && eqb c c) = true then
      if n < n' then true else if n = n' then lt d d' else false else false) = true
    rw [eqb_refl, eqb_refl, eqb_refl]
    show (if n < n' then true else if n = n' then lt d d' else false) = true
    rcases h with h | ⟨h, hd⟩
    · rw [ite_eq_left h]
    · rw [ite_eq_right (h ▸ Nat.lt_irrefl n), ite_eq_left h, hd]

/-- Rocq: `Notation.GrimmT3.T3lt_total`. -/
theorem lt_total : ∀ x y : T3, Trich x y := by
  intro x y
  induction h : size x + size y using Nat.strongRecOn generalizing x y with
  | ind k IH =>
    cases x with
    | zero =>
      cases y with
      | zero => exact .inr (.inl rfl)
      | cons _ _ _ _ _ => exact .inl (lt_zero_cons _ _ _ _ _)
    | cons a b c n d =>
      cases y with
      | zero => exact .inr (.inr (lt_zero_cons _ _ _ _ _))
      | cons a' b' c' n' d' =>
        have H : ∀ u v, size u + size v < size (cons a b c n d) + size (cons a' b' c' n' d') →
            Trich u v := fun u v huv => IH _ (h ▸ huv) u v rfl
        have Sx := size_a a b c n d; have Sb := size_b a b c n d; have Sc := size_c a b c n d
        have Sd := size_d a b c n d; have Sp := size_psi a b c n d
        have Sx' := size_a a' b' c' n' d'; have Sb' := size_b a' b' c' n' d'
        have Sc' := size_c a' b' c' n' d'; have Sd' := size_d a' b' c' n' d'
        have Sp' := size_psi a' b' c' n' d'
        rcases ltPsi_total a b c a' b' c' (H a a' (pair_lt Sx (Nat.le_of_lt Sx')))
            (H b b' (pair_lt Sb (Nat.le_of_lt Sb'))) (H c c' (pair_lt Sc (Nat.le_of_lt Sc')))
            (H b _ (pair_lt Sb Sp')) (H c _ (pair_lt Sc Sp'))
            (H b' _ (pair_lt_swap (pair_lt Sb' Sp))) (H c' _ (pair_lt_swap (pair_lt Sc' Sp)))
          with Hl | ⟨rfl, rfl, rfl⟩ | Hr
        · exact .inl (lt_cons_psi Hl)
        · rcases Nat.lt_trichotomy n n' with hn | rfl | hn
          · exact .inl (lt_cons_same a b c (.inl hn))
          · rcases H d d' (pair_lt Sd (Nat.le_of_lt Sd')) with hd | rfl | hd
            · exact .inl (lt_cons_same a b c (.inr ⟨rfl, hd⟩))
            · exact .inr (.inl rfl)
            · exact .inr (.inr (lt_cons_same a b c (.inr ⟨rfl, hd⟩)))
          · exact .inr (.inr (lt_cons_same a b c (.inl hn)))
        · exact .inr (.inr (lt_cons_psi Hr))

/-- Grimm's normal forms. Rocq: `Notation.GrimmT3.T3nf`. -/
def nf : T3 → Bool
  | zero => true
  | cons a b c _ d => nf a && nf b && nf c && nf d && lt d (psi a b c)

/-! ## The translation into `ATowerNotation` -/

open Ordinal
open ATowerNotation
open ATowerNotation.VForm hiding size succ add mul exp

/-- Rocq: `Notation.GrimmT3.vf_leb`. -/
def vfLeb (x y : VForm) : Bool :=
  match compare x y with
  | .lt => true
  | .eq => true
  | .gt => false

/-- Rocq: `Notation.GrimmT3.vf_leb_sound`. -/
theorem vfLeb_sound (x y : VForm) : vfLeb x y = true → denote x ≤ denote y := by
  have hc := compare_correct x y
  show (match compare x y with | .lt => true | .eq => true | .gt => false) = true → _
  revert hc
  cases compare x y with
  | lt => exact fun hc _ => le_of_lt hc
  | eq => exact fun hc _ => hc.le
  | gt => exact fun _ h => Bool.noConfusion h

/-- Rocq: `Notation.GrimmT3.vf_one`. -/
def vfOne : VForm := V Z Z Z

/-- Rocq: `Notation.GrimmT3.vf_finiteb`. -/
def vfFinite : VForm → Bool
  | Z => true
  | V Z Z r => vfFinite r
  | V Z (V _ _ _) _ => false
  | V (V _ _ _) _ _ => false

/-- `x + 1`, for `x` in normal form. Rocq: `Notation.GrimmT3.vf_plus_one`. -/
def vfPlusOne : VForm → VForm
  | Z => vfOne
  | V Z e r => V Z e (vfPlusOne r)
  | V (V m1 m2 m3) a r => V Z (V (V m1 m2 m3) a r) vfOne

/-- `-1 + x`: removes one from a finite `x`; fixes infinite `x`.
Rocq: `Notation.GrimmT3.vf_minus_one`. -/
def vfMinusOne : VForm → VForm
  | Z => Z
  | V Z Z r => r
  | V Z (V a1 a2 a3) r => V Z (V a1 a2 a3) r
  | V (V m1 m2 m3) a r => V (V m1 m2 m3) a r

/-- If `x = λ + m` with `λ` a strongly critical term (`V n _ _`, `n ≠ Z`)
and `m` finite, return `λ`. Rocq: `Notation.GrimmT3.vf_split_fin`. -/
def vfSplitFin : VForm → Option VForm
  | Z => none
  | V Z Z _ => none
  | V Z (V Z _ _) _ => none
  | V Z (V (V p1 p2 p3) x1 x2) r => bif vfFinite r then some (V (V p1 p2 p3) x1 x2) else none
  | V (V n1 n2 n3) x y => some (V (V n1 n2 n3) x y)

/-- Whether `V L B ξ` satisfies the top-level normality condition, i.e. `ξ`
is not a fixed point of `φ_{L,B}` (and, for `ξ = Z`, `B` is not absorbed).
Rocq: `Notation.GrimmT3.vf_top_ok`. -/
def vfTopOk (L B xi : VForm) : Bool :=
  match xi with
  | Z =>
    match B with
    | Z => true
    | V n _ _ => vfLeb n L
  | V n x _ =>
    match compare L n with
    | .lt => vfLeb xi B
    | .eq => vfLeb x B
    | .gt => true

/-- The common shape of both shifts: `skip test C1` adds one exactly when
`C1 = λ + m` with `λ` a fixed point (decided by `test`).
Rocq: `Notation.GrimmT3.skip`. -/
def skip (test : VForm → Bool) (C1 : VForm) : VForm :=
  match vfSplitFin C1 with
  | some lam => bif test lam then C1 else vfPlusOne C1
  | none => C1

/-- The γ index of the `ω^·` family: skip the ε-numbers. Defined through
`skip`, which Rocq's `shift_omega_skip` shows equivalent.
Rocq: `Notation.GrimmT3.shift_omega`. -/
def shiftOmega (C : VForm) : VForm := skip (fun _ => false) C

/-- The β-absorption step of `shiftGen`: start the γ index at `1` when
`φ_{L,B}(0) = B`. -/
def absorb (L B C : VForm) : VForm := bif vfTopOk L B Z then C else onePlus C

/-- The γ index of the family `φ_{L,B}`: β-absorption, then γ-skipping.
Defined through `skip`, as in Rocq's `shift_gen_skip`.
Rocq: `Notation.GrimmT3.shift_gen`. -/
def shiftGen (L B C : VForm) : VForm := skip (vfTopOk L B) (absorb L B C)

/-- The bracket `ψ(a,b,c)`, from the translations of its components.
Rocq: `Notation.GrimmT3.vf_psi`. -/
def vfPsi (A B C : VForm) : VForm :=
  match A, B with
  | Z, Z => V Z (shiftOmega C) Z
  | Z, V b1 b2 b3 =>
    V vfOne (vfMinusOne (V b1 b2 b3)) (shiftGen vfOne (vfMinusOne (V b1 b2 b3)) C)
  | V a1 a2 a3, _ => V (onePlus (V a1 a2 a3)) B (shiftGen (onePlus (V a1 a2 a3)) B C)

/-- The `ω`-exponent of an additive principal term.
Rocq: `Notation.GrimmT3.vf_exponent`. -/
def vfExponent : VForm → VForm
  | Z => Z
  | V Z e Z => e
  | V Z e (V x y z) => V Z e (V x y z)
  | V (V m1 m2 m3) e r => V (V m1 m2 m3) e r

/-- Rocq: `Notation.GrimmT3.vf_rep`. -/
def vfRep : Nat → VForm → VForm → VForm
  | 0, _, t => t
  | n + 1, E, t => V Z E (vfRep n E t)

/-- Rocq: `Notation.GrimmT3.T3_to_VF`. -/
def T3.toVF : T3 → VForm
  | .zero => Z
  | .cons a b c n d =>
    match toVF d with
    | Z => vfRep n (vfExponent (vfPsi (toVF a) (toVF b) (toVF c))) (vfPsi (toVF a) (toVF b) (toVF c))
    | V m x y => vfRep (n + 1) (vfExponent (vfPsi (toVF a) (toVF b) (toVF c))) (V m x y)

/-- Rocq: `Notation.GrimmT3.T3_denote`. -/
def T3.denote (x : T3) : Ordinal.{0} := VForm.denote (T3.toVF x)

theorem toVF_cons (a b c : T3) (n : Nat) (d : T3) :
    T3.toVF (cons a b c n d) =
      match T3.toVF d with
      | Z => vfRep n (vfExponent (vfPsi a.toVF b.toVF c.toVF)) (vfPsi a.toVF b.toVF c.toVF)
      | V m x y => vfRep (n + 1) (vfExponent (vfPsi a.toVF b.toVF c.toVF)) (V m x y) := rfl

/-! ### Computing the shifts -/

theorem skip_none {test : VForm → Bool} {C1 : VForm} (h : vfSplitFin C1 = none) :
    skip test C1 = C1 := by
  unfold skip; rw [h]

theorem skip_some_true {test : VForm → Bool} {C1 lam : VForm} (h : vfSplitFin C1 = some lam)
    (ht : test lam = true) : skip test C1 = C1 := by
  unfold skip; rw [h]; show (bif test lam then C1 else vfPlusOne C1) = C1; rw [ht]; rfl

theorem skip_some_false {test : VForm → Bool} {C1 lam : VForm} (h : vfSplitFin C1 = some lam)
    (ht : test lam = false) : skip test C1 = vfPlusOne C1 := by
  unfold skip; rw [h]; show (bif test lam then C1 else vfPlusOne C1) = vfPlusOne C1; rw [ht]; rfl

theorem skip_cases (test : VForm → Bool) (C1 : VForm) :
    (vfSplitFin C1 = none ∧ skip test C1 = C1) ∨
    (∃ lam, vfSplitFin C1 = some lam ∧ test lam = true ∧ skip test C1 = C1) ∨
    (∃ lam, vfSplitFin C1 = some lam ∧ test lam = false ∧ skip test C1 = vfPlusOne C1) := by
  cases h : vfSplitFin C1 with
  | none => exact .inl ⟨rfl, skip_none h⟩
  | some lam =>
    cases ht : test lam with
    | true => exact .inr (.inl ⟨lam, rfl, ht, skip_some_true h ht⟩)
    | false => exact .inr (.inr ⟨lam, rfl, ht, skip_some_false h ht⟩)

theorem absorb_true {L B : VForm} (C : VForm) (h : vfTopOk L B Z = true) : absorb L B C = C := by
  unfold absorb; rw [h]; rfl

theorem absorb_false {L B : VForm} (C : VForm) (h : vfTopOk L B Z = false) :
    absorb L B C = onePlus C := by
  unfold absorb; rw [h]; rfl

/-! ## Semantics of sums -/

/-- `repOrd n e t` is `ω^e + (ω^e + ... (ω^e + t))` with `n` copies.
Rocq: `Notation.GrimmT3.rep_ord`. -/
def repOrd : Nat → Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  | 0, _, t => t
  | n + 1, e, t => ω ^ e + repOrd n e t

/-- Rocq: `Notation.GrimmT3.vf_rep_denote`. -/
theorem vfRep_denote (n : Nat) (E t : VForm) :
    denote (vfRep n E t) ≈ repOrd n (denote E) (denote t) := by
  induction n with
  | zero => exact equiv_refl _
  | succ n ih =>
    exact equiv_trans (veblen_ack0 _ _ (complete E) (complete _)) (add_congr (equiv_refl _) ih)

/-- Rocq: `Notation.GrimmT3.rep_ord_monotone`. -/
theorem repOrd_monotone (n : Nat) (e : Ordinal.{0}) :
    ∀ t t', t ≤ t' → repOrd n e t ≤ repOrd n e t' := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun t t' h => add_le_add (le_refl _) (ih t t' h)

/-- Rocq: `Notation.GrimmT3.rep_ord_increasing`. -/
theorem repOrd_increasing (n : Nat) (e : Ordinal.{0}) :
    ∀ t t', t < t' → repOrd n e t < repOrd n e t' := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun t t' h => add_lt_add_left _ (ih t t' h)

/-- Rocq: `Notation.GrimmT3.rep_ord_ge`. -/
theorem repOrd_ge (n : Nat) (e t : Ordinal.{0}) : t ≤ repOrd n e t := by
  induction n with
  | zero => exact le_refl t
  | succ n ih => exact le_trans ih (le_add_left _ _)

/-- Rocq: `Notation.GrimmT3.rep_ord_head`. -/
theorem repOrd_head (n : Nat) (e t : Ordinal.{0}) : ω ^ e ≤ repOrd (n + 1) e t :=
  le_add_right _ _

/-- Below an additively closed bound. Rocq: `Notation.GrimmT3.rep_ord_bounded`. -/
theorem repOrd_bounded (n : Nat) (e t z : Ordinal.{0}) (hz : AdditivelyClosed z) (he : ω ^ e < z)
    (ht : t < z) : repOrd n e t < z := by
  induction n with
  | zero => exact ht
  | succ n ih => exact hz _ _ he ih

private theorem repOrd_congr (n : Nat) (e : Ordinal.{0}) {t t' : Ordinal.{0}} (h : t ≈ t') :
    repOrd n e t ≈ repOrd n e t' :=
  equiv_intro (repOrd_monotone n e _ _ h.le) (repOrd_monotone n e _ _ h.ge)

private theorem repOrd_shift (e u : Ordinal.{0}) :
    ∀ k : Nat, repOrd k e (ω ^ e + u) ≈ repOrd (k + 1) e u
  | 0 => equiv_refl _
  | k + 1 => add_congr (equiv_refl _) (repOrd_shift e u k)

private theorem repOrd_add (k : Nat) (e t : Ordinal.{0}) :
    ∀ j : Nat, repOrd (k + j) e t = repOrd j e (repOrd k e t)
  | 0 => rfl
  | j + 1 => congrArg (ω ^ e + ·) (repOrd_add k e t j)

/-- The shape of a translated bracket: either `ω^e` or a bracket of nonzero
level, which is an ε-number. Rocq: `Notation.GrimmT3.vf_principal_shape`. -/
def PrincipalShape : VForm → Prop
  | Z => False
  | V Z _ Z => True
  | V Z _ (V _ _ _) => False
  | V (V _ _ _) _ _ => True

/-- Rocq: `Notation.GrimmT3.VF_onePlus_V`. -/
theorem onePlus_V (x : VForm) (hx : x ≠ Z) : ∃ m a b, onePlus x = V m a b := by
  cases x with
  | Z => exact absurd rfl hx
  | V m a b =>
    cases m with
    | Z =>
      cases a with
      | Z => exact ⟨_, _, _, rfl⟩
      | V _ _ _ => exact ⟨_, _, _, rfl⟩
    | V _ _ _ => exact ⟨_, _, _, rfl⟩

/-- Rocq: `Notation.GrimmT3.vf_psi_shape`. -/
theorem vfPsi_shape (A B C : VForm) : PrincipalShape (vfPsi A B C) := by
  cases A with
  | Z =>
    cases B with
    | Z => exact trivial
    | V _ _ _ => exact trivial
  | V a1 a2 a3 =>
    obtain ⟨m, a, b, heq⟩ := onePlus_V (V a1 a2 a3) (fun h => VForm.noConfusion h)
    show PrincipalShape (V (onePlus (V a1 a2 a3)) B (shiftGen (onePlus (V a1 a2 a3)) B C))
    rw [heq]; exact trivial

/-- Rocq: `Notation.GrimmT3.vf_exponent_correct`. -/
theorem vfExponent_correct (P : VForm) (hP : PrincipalShape P) :
    ω ^ denote (vfExponent P) ≈ denote P :=
  match P, hP with
  | V Z e Z, _ =>
    equiv_symm (equiv_trans (veblen_ack0 _ _ (complete e) zero_complete) (add_zero _))
  | V (V m a b) x y, _ =>
    veblen_tower_epsilon _ _ _ (complete (V m a b)) (complete x) (complete y)
      (veblen_nonzero (TV_normal m) _ _)

/-- The denotation of a sum: `ψ(a,b,c)·(n+1) + d`.
Rocq: `Notation.GrimmT3.T3_denote_cons`. -/
theorem T3_denote_cons (a b c : T3) (n : Nat) (d : T3) :
    T3.denote (cons a b c n d) ≈
      repOrd (n + 1) (denote (vfExponent (vfPsi a.toVF b.toVF c.toVF))) (T3.denote d) := by
  have HP := vfExponent_correct _ (vfPsi_shape a.toVF b.toVF c.toVF)
  show denote (T3.toVF (cons a b c n d)) ≈ _
  rw [toVF_cons]
  show _ ≈ repOrd (n + 1) _ (denote d.toVF)
  cases d.toVF with
  | Z =>
    exact equiv_trans (vfRep_denote _ _ _) (equiv_trans
      (repOrd_congr n _ (equiv_symm (equiv_trans (add_zero _) HP))) (repOrd_shift _ _ n))
  | V m x y => exact vfRep_denote (n + 1) _ (V m x y)

/-- Rocq: `Notation.GrimmT3.T3_exp`. -/
def T3exp (a b c : T3) : Ordinal.{0} := denote (vfExponent (vfPsi a.toVF b.toVF c.toVF))

/-- Rocq: `Notation.GrimmT3.T3_denote_psi`. -/
theorem T3_denote_psi (a b c : T3) : T3.denote (psi a b c) ≈ ω ^ T3exp a b c :=
  equiv_trans (T3_denote_cons a b c 0 .zero) (add_zero _)

/-- Rocq: `Notation.GrimmT3.sum_lt_head`. -/
theorem sum_lt_head (e e' : Ordinal.{0}) (n n' : Nat) (t t' : Ordinal.{0}) (he' : Complete e')
    (hee : ω ^ e < ω ^ e') (ht : t < ω ^ e) : repOrd (n + 1) e t < repOrd (n' + 1) e' t' :=
  lt_of_lt_of_le
    (repOrd_bounded (n + 1) e t _ (powOmega_additively_closed he') hee (lt_trans ht hee))
    (repOrd_head n' e' t')

private theorem nat_lt_split {n n' : Nat} (h : n < n') : ∃ k, n' = n + k + 1 := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | step _ ih => obtain ⟨k, rfl⟩ := ih; exact ⟨k + 1, rfl⟩

/-- Rocq: `Notation.GrimmT3.sum_lt_count`. -/
theorem sum_lt_count (e : Ordinal.{0}) (n n' : Nat) (t t' : Ordinal.{0}) (hn : n < n')
    (ht : t < ω ^ e) : repOrd (n + 1) e t < repOrd (n' + 1) e t' := by
  obtain ⟨k, rfl⟩ := nat_lt_split hn
  have hk : n + k + 1 + 1 = (k + 1) + (n + 1) := by
    rw [Nat.add_comm (k + 1) (n + 1), ← Nat.add_assoc, Nat.add_right_comm n 1 k]
  rw [hk, repOrd_add (k + 1) e t' (n + 1)]
  exact lt_of_lt_of_le (repOrd_increasing (n + 1) e _ _ ht)
    (repOrd_monotone (n + 1) e _ _ (le_add_right _ _))

/-- Rocq: `Notation.GrimmT3.sum_lt_tail`. -/
theorem sum_lt_tail (e : Ordinal.{0}) (n : Nat) (t t' : Ordinal.{0}) (h : t < t') :
    repOrd n e t < repOrd n e t' :=
  repOrd_increasing n e t t' h

/-! ## Semantic toolkit for brackets -/

/-- Rocq: `Notation.GrimmT3.VF_V_increasing`. -/
theorem VF_V_increasing (m a x y : VForm) (h : denote x < denote y) :
    denote (V m a x) < denote (V m a y) :=
  veblen_increasing (TV_normal m) _ (complete a) _ _ (complete y) h

/-- Rocq: `Notation.GrimmT3.VF_V_inflationary`. -/
theorem VF_V_inflationary (m a x : VForm) : denote x ≤ denote (V m a x) :=
  veblen_inflationary (TV_normal m) _ _ (complete x)

/-- Rocq: `Notation.GrimmT3.VF_V_pos`. -/
theorem VF_V_pos (m a x : VForm) : 0 < denote (V m a x) := veblen_nonzero (TV_normal m) _ _

/-- Comparison across levels: the target is a fixed point of the lower level.
Rocq: `Notation.GrimmT3.vf_lt_cross`. -/
theorem vf_lt_cross (L b x n b' x' : VForm) (hL : denote L < denote n)
    (hb : denote b < denote (V n b' x')) (hx : denote x < denote (V n b' x')) :
    denote (V L b x) < denote (V n b' x') :=
  lt_of_lt_of_le (VF_V_increasing L b _ _ hx) (Vmn_collapse n L b b' x' hL hb).le

/-- Comparison within a level. Rocq: `Notation.GrimmT3.vf_lt_same`. -/
theorem vf_lt_same (L b x b' x' : VForm) (hb : denote b < denote b')
    (hx : denote x < denote (V L b' x')) : denote (V L b x) < denote (V L b' x') :=
  lt_of_lt_of_le (VF_V_increasing L b _ _ hx) (V_collapse L b b' x' hb).le

/-- Rocq: `Notation.GrimmT3.VF_one_denote`. -/
theorem VF_one_denote : denote vfOne ≈ 1 :=
  equiv_trans (veblen_ack0 0 0 zero_complete zero_complete) (equiv_trans (add_zero _) (pow_zero ω))

/-- Rocq: `Notation.GrimmT3.VF_sum_denote`. -/
theorem VF_sum_denote (e r : VForm) : denote (V Z e r) ≈ ω ^ denote e + denote r :=
  veblen_ack0 _ _ (complete e) (complete r)

/-- Terms of nonzero level are ε-numbers. Rocq: `Notation.GrimmT3.VF_high_epsilon`. -/
theorem VF_high_epsilon (m a b x y : VForm) :
    ω ^ denote (V (V m a b) x y) ≈ denote (V (V m a b) x y) :=
  veblen_tower_epsilon _ _ _ (complete _) (complete x) (complete y) (VF_V_pos m a b)

/-- Rocq: `Notation.GrimmT3.vf_plus_one_succ`. -/
theorem vfPlusOne_succ : ∀ x : VForm, denote (vfPlusOne x) ≈ Ordinal.succ (denote x)
  | Z => VF_one_denote
  | V Z e r =>
    equiv_trans (VF_sum_denote e _) (equiv_trans (add_congr (equiv_refl _) (vfPlusOne_succ r))
      (equiv_trans (add_succ _ _) (succ_congruence (equiv_symm (VF_sum_denote e r)))))
  | V (V m1 m2 m3) a r =>
    equiv_trans (VF_sum_denote _ vfOne) (equiv_trans
      (add_congr (VF_high_epsilon m1 m2 m3 a r) VF_one_denote)
      (equiv_trans (add_succ _ 0) (succ_congruence (add_zero _))))

/-- Rocq: `Notation.GrimmT3.vf_minus_one_le`. -/
theorem vfMinusOne_le (x : VForm) : denote (vfMinusOne x) ≤ denote x :=
  match x with
  | Z => le_refl _
  | V Z Z r => VF_V_inflationary Z Z r
  | V Z (V _ _ _) _ => le_refl _
  | V (V _ _ _) _ _ => le_refl _

/-- One plus an infinite additively closed ordinal.
Rocq: `Notation.GrimmT3.onePlus_closed`. -/
theorem onePlus_closed (z : Ordinal.{0}) (hz : AdditivelyClosed z) (h1 : 1 < z) : 1 + z ≈ z :=
  equiv_intro (additively_closed_collapse hz h1) (le_add_left 1 z)

/-- Rocq: `Notation.GrimmT3.omega_pow_gt1`. -/
theorem omega_pow_gt1 (e : Ordinal.{0}) (he : 0 < e) (_hc : Complete e) : 1 < ω ^ e :=
  lt_of_lt_of_le omega_gt1 (le_trans (pow_one' omega_gt0).ge (pow_le_pow_right ω (succ_least he)))

/-- Rocq: `Notation.GrimmT3.onePlus_minus_one`. -/
theorem onePlus_minus_one (x : VForm) (hx : x ≠ Z) : denote x ≈ 1 + denote (vfMinusOne x) :=
  match x, hx with
  | Z, hx => absurd rfl hx
  | V Z Z r, _ => equiv_trans (VF_sum_denote Z r) (add_congr (pow_zero ω) (equiv_refl _))
  | V Z (V a1 a2 a3) r, _ =>
    equiv_trans (VF_sum_denote _ r) (equiv_symm (equiv_trans
      (add_congr (equiv_refl 1) (VF_sum_denote _ r)) (equiv_trans (add_assoc 1 _ _)
        (add_congr (onePlus_closed _ (powOmega_additively_closed (complete _))
          (omega_pow_gt1 _ (VF_V_pos a1 a2 a3) (complete _))) (equiv_refl _)))))
  | V (V m1 m2 m3) a r, _ =>
    equiv_symm (onePlus_closed _
      (AdditivelyClosed.congr (VF_high_epsilon m1 m2 m3 a r)
        (powOmega_additively_closed (complete _)))
      (lt_of_lt_of_le (omega_pow_gt1 _ (VF_V_pos _ _ _) (complete _))
        (VF_high_epsilon m1 m2 m3 a r).le))

/-- Rocq: `Notation.GrimmT3.skip_ge`. -/
theorem skip_ge (test : VForm → Bool) (C1 : VForm) : denote C1 ≤ denote (skip test C1) := by
  rcases skip_cases test C1 with ⟨_, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩
  · rw [he]
  · rw [he]
  · rw [he]; exact le_trans (le_of_lt (succ_lt _)) (vfPlusOne_succ C1).ge

private theorem skip_le (test : VForm → Bool) (C1 : VForm) :
    denote (skip test C1) ≤ Ordinal.succ (denote C1) := by
  rcases skip_cases test C1 with ⟨_, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he]
  · exact le_of_lt (succ_lt _)
  · exact le_of_lt (succ_lt _)
  · exact (vfPlusOne_succ C1).le

/-- Bounds on the shifted index. Rocq: `Notation.GrimmT3.shift_omega_bounds`. -/
theorem shiftOmega_bounds (C : VForm) :
    denote C ≤ denote (shiftOmega C) ∧ denote (shiftOmega C) ≤ Ordinal.succ (denote C) :=
  ⟨skip_ge _ C, skip_le _ C⟩

private theorem absorb_bounds (L B C : VForm) :
    denote C ≤ denote (absorb L B C) ∧ denote (absorb L B C) ≤ 1 + denote C := by
  cases h : vfTopOk L B Z with
  | true => rw [absorb_true C h]; exact ⟨le_refl _, le_add_left 1 _⟩
  | false =>
    rw [absorb_false C h]
    exact ⟨le_trans (le_add_left 1 _) (onePlus_equal C).ge, (onePlus_equal C).le⟩

/-- Rocq: `Notation.GrimmT3.shift_gen_bounds`. -/
theorem shiftGen_bounds (L B C : VForm) :
    denote C ≤ denote (shiftGen L B C) ∧ denote (shiftGen L B C) ≤ Ordinal.succ (1 + denote C) :=
  ⟨le_trans (absorb_bounds L B C).1 (skip_ge _ _),
    le_trans (skip_le _ _) (succ_monotone (absorb_bounds L B C).2)⟩

/-- Rocq: `Notation.GrimmT3.below_closed_succ_onePlus`. -/
theorem below_closed_succ_onePlus (z c : Ordinal.{0}) (hz : AdditivelyClosed z) (h1 : 1 < z)
    (hc : c < z) : Ordinal.succ (1 + c) < z :=
  lt_of_le_of_lt (le_trans (succ_monotone (add_zero _).ge) (add_succ (1 + c) 0).ge)
    (hz _ _ (hz _ _ h1 hc) h1)

/-! ## Normality of the translation -/

private theorem some_ne_none {a : VForm} (h : some a = none) : False := nomatch h

private theorem none_ne_some {a : VForm} (h : none = some a) : False := nomatch h

private theorem tail_same (m a x y : VForm) (h : denote x ≤ denote a) : NormalTail m a (V m x y) :=
  (normalTail_V_iff m m a x y).2 ⟨fun hl => absurd hl (lt_irrefl _), fun _ => h⟩

/-- Rocq: `Notation.GrimmT3.VF_one_normal`. -/
theorem VF_one_normal : IsNormal vfOne := ⟨trivial, trivial, trivial, trivial⟩

/-- Rocq: `Notation.GrimmT3.vf_plus_one_normal`. -/
theorem vfPlusOne_normal : ∀ x : VForm, IsNormal x → IsNormal (vfPlusOne x)
  | Z, _ => VF_one_normal
  | V Z a Z, ⟨_, hna, _, _⟩ => ⟨trivial, hna, VF_one_normal, tail_same Z a Z Z (zero_least _)⟩
  | V Z a (V Z x y), ⟨_, hna, hnr, htop⟩ =>
    ⟨trivial, hna, vfPlusOne_normal (V Z x y) hnr,
      tail_same Z a x _ (((normalTail_V_iff Z Z a x y).1 htop).2 (equiv_refl _))⟩
  | V Z a (V (V n1 n2 n3) x y), ⟨_, hna, hnr, htop⟩ =>
    ⟨trivial, hna, vfPlusOne_normal (V (V n1 n2 n3) x y) hnr,
      tail_same Z a _ _ (((normalTail_V_iff Z _ a x y).1 htop).1 (VF_V_pos n1 n2 n3))⟩
  | V (V _ _ _) _ _, hx =>
    ⟨trivial, hx, VF_one_normal, tail_same Z _ Z Z (zero_least _)⟩

/-- Rocq: `Notation.GrimmT3.vf_minus_one_normal`. -/
theorem vfMinusOne_normal (x : VForm) (h : IsNormal x) : IsNormal (vfMinusOne x) :=
  match x, h with
  | Z, h => h
  | V Z Z _, h => h.2.2.1
  | V Z (V _ _ _) _, h => h
  | V (V _ _ _) _ _, h => h

/-- Rocq: `Notation.GrimmT3.vf_top_ok_sound`. -/
theorem vfTopOk_sound (L B xi : VForm) : vfTopOk L B xi = true → NormalTail L B xi := by
  cases xi with
  | Z =>
    cases B with
    | Z => exact fun _ => trivial
    | V n _ _ => exact vfLeb_sound n L
  | V n x y =>
    show (match compare L n with
      | .lt => vfLeb (V n x y) B
      | .eq => vfLeb x B
      | .gt => true) = true →
      (match compare L n with
      | .lt => denote (V n x y) ≤ denote B
      | .eq => denote x ≤ denote B
      | .gt => True)
    cases compare L n with
    | lt => exact vfLeb_sound _ _
    | eq => exact vfLeb_sound _ _
    | gt => exact fun _ => trivial

/-- After the shift, the index is never a fixed point.
Rocq: `Notation.GrimmT3.skip_top`. -/
theorem skip_top (m1 m2 m3 B C1 : VForm) (HC1 : C1 = Z → vfTopOk (V m1 m2 m3) B Z = true) :
    vfTopOk (V m1 m2 m3) B (skip (vfTopOk (V m1 m2 m3) B) C1) = true := by
  rcases skip_cases (vfTopOk (V m1 m2 m3) B) C1 with ⟨hs, he⟩ | ⟨lam, hs, ht, he⟩ | ⟨_, _, _, he⟩
  · rw [he]
    cases C1 with
    | Z => exact HC1 rfl
    | V m _ _ =>
      cases m with
      | Z => rfl
      | V _ _ _ => exact (some_ne_none hs).elim
  · rw [he]
    cases C1 with
    | Z => exact (none_ne_some hs).elim
    | V m x y =>
      cases m with
      | Z => rfl
      | V n1 n2 n3 =>
        have e : V (V n1 n2 n3) x y = lam := Option.some.inj hs
        rw [e]; exact ht
  · rw [he]
    cases C1 with
    | Z => rfl
    | V m _ _ =>
      cases m with
      | Z => rfl
      | V _ _ _ => rfl

private theorem onePlus_ne_Z (C : VForm) : onePlus C ≠ Z := by
  cases C with
  | Z => exact fun h => VForm.noConfusion h
  | V m a _ =>
    cases m with
    | Z =>
      cases a with
      | Z => exact fun h => VForm.noConfusion h
      | V _ _ _ => exact fun h => VForm.noConfusion h
    | V _ _ _ => exact fun h => VForm.noConfusion h

/-- Rocq: `Notation.GrimmT3.shift_gen_top`. -/
theorem shiftGen_top (m1 m2 m3 B C : VForm) :
    vfTopOk (V m1 m2 m3) B (shiftGen (V m1 m2 m3) B C) = true := by
  refine skip_top m1 m2 m3 B _ ?_
  cases h : vfTopOk (V m1 m2 m3) B Z with
  | true => exact fun _ => rfl
  | false => rw [absorb_false C h]; exact fun e => absurd e (onePlus_ne_Z C)

/-- Rocq: `Notation.GrimmT3.shift_omega_top`. -/
theorem shiftOmega_top (C : VForm) :
    match shiftOmega C with
    | Z => True
    | V n _ _ => n = Z := by
  rcases skip_cases (fun _ => false) C with ⟨hs, he⟩ | ⟨_, _, ht, _⟩ | ⟨_, _, _, he⟩
  · show match skip (fun _ => false) C with | Z => True | V n _ _ => n = Z
    rw [he]
    cases C with
    | Z => trivial
    | V m _ _ =>
      cases m with
      | Z => rfl
      | V _ _ _ => exact (some_ne_none hs).elim
  · exact Bool.noConfusion ht
  · show match skip (fun _ => false) C with | Z => True | V n _ _ => n = Z
    rw [he]
    cases C with
    | Z => rfl
    | V m _ _ =>
      cases m with
      | Z => rfl
      | V _ _ _ => rfl

/-- Rocq: `Notation.GrimmT3.skip_normal`. -/
theorem skip_normal (test : VForm → Bool) (C1 : VForm) (h : IsNormal C1) :
    IsNormal (skip test C1) := by
  rcases skip_cases test C1 with ⟨_, he⟩ | ⟨_, _, _, he⟩ | ⟨_, _, _, he⟩ <;> rw [he]
  · exact h
  · exact h
  · exact vfPlusOne_normal C1 h

/-- Rocq: `Notation.GrimmT3.shift_omega_normal`. -/
theorem shiftOmega_normal (C : VForm) (h : IsNormal C) : IsNormal (shiftOmega C) :=
  skip_normal _ C h

/-- Rocq: `Notation.GrimmT3.shift_gen_normal`. -/
theorem shiftGen_normal (L B C : VForm) (h : IsNormal C) : IsNormal (shiftGen L B C) := by
  refine skip_normal _ _ ?_
  cases hz : vfTopOk L B Z with
  | true => rw [absorb_true C hz]; exact h
  | false => rw [absorb_false C hz]; exact onePlus_isNormal C h

/-- Rocq: `Notation.GrimmT3.vf_psi_normal`. -/
theorem vfPsi_normal (A B C : VForm) (HA : IsNormal A) (HB : IsNormal B) (HC : IsNormal C) :
    IsNormal (vfPsi A B C) := by
  cases A with
  | Z =>
    cases B with
    | Z =>
      refine ⟨trivial, shiftOmega_normal C HC, trivial, ?_⟩
      show NormalTail Z (shiftOmega C) Z
      have ht := shiftOmega_top C
      revert ht
      cases shiftOmega C with
      | Z => exact fun _ => trivial
      | V n _ _ => exact fun (h : n = Z) => by subst h; exact le_refl _
    | V b1 b2 b3 =>
      exact ⟨VF_one_normal, vfMinusOne_normal _ HB, shiftGen_normal _ _ _ HC,
        vfTopOk_sound _ _ _ (shiftGen_top Z Z Z _ C)⟩
  | V a1 a2 a3 =>
    obtain ⟨m1, m2, m3, heq⟩ := onePlus_V (V a1 a2 a3) (fun h => VForm.noConfusion h)
    refine ⟨onePlus_isNormal _ HA, HB, shiftGen_normal _ _ _ HC, ?_⟩
    show NormalTail (onePlus (V a1 a2 a3)) B (shiftGen (onePlus (V a1 a2 a3)) B C)
    rw [heq]; exact vfTopOk_sound _ _ _ (shiftGen_top m1 m2 m3 B C)

/-- Rocq: `Notation.GrimmT3.expOmega_reflect`. -/
theorem expOmega_reflect (x y : VForm) (h : ω ^ denote x < ω ^ denote y) : denote x < denote y := by
  have hc := compare_correct x y
  revert hc
  cases compare x y with
  | lt => exact id
  | eq =>
    exact fun hc => absurd (lt_of_lt_of_le h (pow_le_pow_right ω hc.ge)) (lt_irrefl _)
  | gt => exact fun hc => absurd (lt_trans h (pow_lt_pow_right omega_gt1 hc)) (lt_irrefl _)

/-- Rocq: `Notation.GrimmT3.VF_rep_normal`. -/
theorem VF_rep_normal (E T : VForm) (H : IsNormal (V Z E T)) :
    ∀ k : Nat, IsNormal (vfRep (k + 1) E T)
  | 0 => H
  | k + 1 => ⟨trivial, H.2.1, VF_rep_normal E T H k, tail_same Z E E _ (le_refl _)⟩

/-- Rocq: `Notation.GrimmT3.vf_exponent_normal`. -/
theorem vfExponent_normal (P : VForm) (hs : PrincipalShape P) (h : IsNormal P) :
    IsNormal (vfExponent P) :=
  match P, hs, h with
  | V Z _ Z, _, h => h.2.1
  | V (V _ _ _) _ _, _, h => h

private theorem cons_normal_aux (P T : VForm) (n : Nat) (hs : PrincipalShape P)
    (HP : IsNormal P) (Hd : IsNormal T) (Hlt : denote T < denote P) :
    IsNormal (match (generalizing := false) T with
      | Z => vfRep n (vfExponent P) P
      | V m x y => vfRep (n + 1) (vfExponent P) (V m x y)) := by
  have HE := vfExponent_correct P hs
  have HEn := vfExponent_normal P hs HP
  cases T with
  | Z =>
    cases n with
    | zero => exact HP
    | succ k =>
      refine VF_rep_normal _ _ ?_ k
      match P, hs, HP with
      | V Z pb Z, _, HP => exact ⟨trivial, HP.2.1, HP, tail_same Z pb pb Z (le_refl _)⟩
      | V (V p1 p2 p3) pb pc, _, HP =>
        exact ⟨trivial, HP, HP, (normalTail_V_iff _ _ _ _ _).2 ⟨fun _ => le_refl _,
          fun e => absurd (lt_of_lt_of_le (VF_V_pos p1 p2 p3) e.ge) (lt_irrefl _)⟩⟩
  | V m x y =>
    refine VF_rep_normal _ _ ⟨trivial, HEn, Hd, ?_⟩ n
    cases m with
    | Z =>
      exact tail_same Z _ x y (le_of_lt (expOmega_reflect x _ (lt_of_le_of_lt
        (le_trans (le_add_right _ _) (VF_sum_denote x y).ge) (lt_of_lt_of_le Hlt HE.ge))))
    | V m1 m2 m3 =>
      exact (normalTail_V_iff _ _ _ _ _).2
        ⟨fun _ => le_of_lt (expOmega_reflect _ _ (lt_of_le_of_lt (VF_high_epsilon m1 m2 m3 x y).le
            (lt_of_lt_of_le Hlt HE.ge))),
          fun e => absurd (lt_of_lt_of_le (VF_V_pos m1 m2 m3) e.ge) (lt_irrefl _)⟩

/-- Rocq: `Notation.GrimmT3.T3_to_VF_cons_normal`. -/
theorem T3_to_VF_cons_normal (a b c : T3) (n : Nat) (d : T3) :
    let P := vfPsi a.toVF b.toVF c.toVF
    IsNormal P → IsNormal d.toVF → T3.denote d < denote P → IsNormal (T3.toVF (cons a b c n d)) :=
  fun HP Hd Hlt => cons_normal_aux _ d.toVF n (vfPsi_shape _ _ _) HP Hd Hlt

/-- Every bracket lies strictly above its `c` argument.
Rocq: `Notation.GrimmT3.psi_gt_c`. -/
theorem psi_gt_c (A B C : VForm) (HP : IsNormal (vfPsi A B C)) : denote C < denote (vfPsi A B C) := by
  have hs := normal_subterm_shrink _ HP
  cases A with
  | Z =>
    cases B with
    | Z => exact lt_of_le_of_lt (shiftOmega_bounds C).1 hs.2.1
    | V _ _ _ => exact lt_of_le_of_lt (shiftGen_bounds _ _ C).1 hs.2.2
  | V _ _ _ => exact lt_of_le_of_lt (shiftGen_bounds _ _ C).1 hs.2.2

/-- Every bracket lies strictly above its `b` argument.
Rocq: `Notation.GrimmT3.psi_gt_b`. -/
theorem psi_gt_b (A B C : VForm) (HP : IsNormal (vfPsi A B C)) : denote B < denote (vfPsi A B C) := by
  have hs := normal_subterm_shrink _ HP
  cases A with
  | Z =>
    cases B with
    | Z => exact VF_V_pos _ _ _
    | V b1 b2 b3 =>
      have hcl := AdditivelyClosed.congr (VF_high_epsilon Z Z Z (vfMinusOne (V b1 b2 b3))
        (shiftGen vfOne (vfMinusOne (V b1 b2 b3)) C)) (powOmega_additively_closed (complete _))
      have h1 := lt_of_lt_of_le (omega_pow_gt1 _ (VF_V_pos _ _ _) (complete _))
        (VF_high_epsilon Z Z Z (vfMinusOne (V b1 b2 b3))
          (shiftGen vfOne (vfMinusOne (V b1 b2 b3)) C)).le
      exact lt_of_le_of_lt (onePlus_minus_one _ (fun h => VForm.noConfusion h)).le
        (hcl _ _ h1 hs.2.1)
  | V _ _ _ => exact hs.2.1

/-! ## Strict monotonicity of the shifted index -/

/-- Rocq: `Notation.GrimmT3.vf_plus_one_finite`. -/
theorem vfPlusOne_finite : ∀ r : VForm, vfFinite r = true → vfFinite (vfPlusOne r) = true
  | Z, _ => rfl
  | V Z Z r, h => vfPlusOne_finite r h
  | V Z (V _ _ _) _, h => Bool.noConfusion h
  | V (V _ _ _) _ _, h => Bool.noConfusion h

/-- Rocq: `Notation.GrimmT3.split_plus_one`. -/
theorem split_plus_one (C lam : VForm) (h : vfSplitFin C = some lam) :
    vfSplitFin (vfPlusOne C) = some lam :=
  match C, h with
  | Z, h => (none_ne_some h).elim
  | V Z Z _, h => (none_ne_some h).elim
  | V Z (V Z _ _) _, h => (none_ne_some h).elim
  | V Z (V (V p1 p2 p3) x1 x2) y, h => by
    have h' : (bif vfFinite y then some (V (V p1 p2 p3) x1 x2) else none) = some lam := h
    cases hy : vfFinite y with
    | false => rw [hy] at h'; exact (none_ne_some h').elim
    | true =>
      rw [hy] at h'
      show (bif vfFinite (vfPlusOne y) then some (V (V p1 p2 p3) x1 x2) else none) = some lam
      rw [vfPlusOne_finite y hy]; exact h'
  | V (V _ _ _) _ _, h => h

/-- Rocq: `Notation.GrimmT3.lt_succ_le`. -/
theorem lt_succ_le (x y : Ordinal.{0}) (h : x < Ordinal.succ y) : x ≤ y := by
  obtain ⟨_, h⟩ := lt_elim h; exact h

/-- Rocq: `Notation.GrimmT3.skip_mono`. -/
theorem skip_mono (test : VForm → Bool) (C1 C1' : VForm) (Hn : IsNormal C1) (Hn' : IsNormal C1')
    (Hlt : denote C1 < denote C1') : denote (skip test C1) < denote (skip test C1') := by
  rcases skip_cases test C1 with ⟨_, he⟩ | ⟨_, _, _, he⟩ | ⟨lam, hs, ht, he⟩
  · rw [he]; exact lt_of_lt_of_le Hlt (skip_ge _ _)
  · rw [he]; exact lt_of_lt_of_le Hlt (skip_ge _ _)
  · rw [he]
    have hc := compare_correct (vfPlusOne C1) C1'
    revert hc
    cases compare (vfPlusOne C1) C1' with
    | lt => exact fun hc => lt_of_lt_of_le hc (skip_ge _ _)
    | eq =>
      intro hc
      have HE := normal_forms_unique _ _ (vfPlusOne_normal _ Hn) Hn' hc
      subst HE
      rw [skip_some_false (split_plus_one _ _ hs) ht]
      exact lt_of_lt_of_le (succ_lt _) (vfPlusOne_succ (vfPlusOne C1)).ge
    | gt =>
      intro hc
      exact absurd (lt_of_lt_of_le Hlt
        (lt_succ_le _ _ (lt_of_lt_of_le hc (vfPlusOne_succ C1).le))) (lt_irrefl _)

/-- Rocq: `Notation.GrimmT3.shift_omega_skip`. -/
theorem shiftOmega_skip (C : VForm) : shiftOmega C = skip (fun _ => false) C := rfl

/-- Rocq: `Notation.GrimmT3.shift_gen_skip`. -/
theorem shiftGen_skip (L B C : VForm) :
    shiftGen L B C = skip (vfTopOk L B) (bif vfTopOk L B Z then C else onePlus C) := rfl

/-- Rocq: `Notation.GrimmT3.shift_omega_mono`. -/
theorem shiftOmega_mono (C C' : VForm) (Hn : IsNormal C) (Hn' : IsNormal C')
    (Hlt : denote C < denote C') : denote (shiftOmega C) < denote (shiftOmega C') :=
  skip_mono _ C C' Hn Hn' Hlt

/-- Rocq: `Notation.GrimmT3.shift_gen_mono`. -/
theorem shiftGen_mono (L B C C' : VForm) (Hn : IsNormal C) (Hn' : IsNormal C')
    (Hlt : denote C < denote C') : denote (shiftGen L B C) < denote (shiftGen L B C') := by
  show denote (skip _ (absorb L B C)) < denote (skip _ (absorb L B C'))
  cases hz : vfTopOk L B Z with
  | true => rw [absorb_true C hz, absorb_true C' hz]; exact skip_mono _ _ _ Hn Hn' Hlt
  | false =>
    rw [absorb_false C hz, absorb_false C' hz]
    exact skip_mono _ _ _ (onePlus_isNormal _ Hn) (onePlus_isNormal _ Hn')
      (lt_of_le_of_lt (onePlus_equal C).le (lt_of_lt_of_le (add_lt_add_left 1 Hlt)
        (onePlus_equal C').ge))

/-! ## Comparing brackets -/

/-- Rocq: `Notation.GrimmT3.vf_psi_nonzero`. -/
theorem vfPsi_nonzero (A B C : VForm) : vfPsi A B C ≠ Z := by
  intro h
  have hs := vfPsi_shape A B C
  rw [h] at hs
  exact hs

/-- Rocq: `Notation.GrimmT3.vf_psi_high`. -/
theorem vfPsi_high (A B C : VForm) (H : A ≠ Z ∨ B ≠ Z) :
    ∃ m1 m2 m3 x y, vfPsi A B C = V (V m1 m2 m3) x y := by
  cases A with
  | Z =>
    cases B with
    | Z => exact H.elim (fun h => absurd rfl h) (fun h => absurd rfl h)
    | V _ _ _ => exact ⟨Z, Z, Z, _, _, rfl⟩
  | V a1 a2 a3 =>
    obtain ⟨m1, m2, m3, heq⟩ := onePlus_V (V a1 a2 a3) (fun h => VForm.noConfusion h)
    refine ⟨m1, m2, m3, B, shiftGen (onePlus (V a1 a2 a3)) B C, ?_⟩
    show V (onePlus (V a1 a2 a3)) B (shiftGen (onePlus (V a1 a2 a3)) B C) = _
    rw [heq]

/-- Rocq: `Notation.GrimmT3.high_facts`. -/
theorem high_facts (P : VForm) (h : ∃ m1 m2 m3 x y, P = V (V m1 m2 m3) x y) :
    AdditivelyClosed (denote P) ∧ 1 < denote P := by
  obtain ⟨m1, m2, m3, x, y, rfl⟩ := h
  exact ⟨AdditivelyClosed.congr (VF_high_epsilon m1 m2 m3 x y)
      (powOmega_additively_closed (complete _)),
    lt_of_lt_of_le (omega_pow_gt1 _ (VF_V_pos _ _ _) (complete _)) (VF_high_epsilon m1 m2 m3 x y).le⟩

/-- Rocq: `Notation.GrimmT3.below_high_shift`. -/
theorem below_high_shift (P L B C : VForm) (HP : ∃ m1 m2 m3 x y, P = V (V m1 m2 m3) x y)
    (HC : denote C < denote P) :
    denote (shiftGen L B C) < denote P ∧ denote (shiftOmega C) < denote P := by
  obtain ⟨hcl, h1⟩ := high_facts P HP
  have hs := below_closed_succ_onePlus _ _ hcl h1 HC
  exact ⟨lt_of_le_of_lt (shiftGen_bounds L B C).2 hs,
    lt_of_le_of_lt (shiftOmega_bounds C).2 (lt_of_le_of_lt (succ_monotone (le_add_left 1 _)) hs)⟩

/-- Rocq: `Notation.GrimmT3.VF_onePlus_pos`. -/
theorem VF_onePlus_pos (A : VForm) (hA : A ≠ Z) : 1 < denote (onePlus A) := by
  have hpos : 0 < denote A := by
    cases A with
    | Z => exact absurd rfl hA
    | V m a b => exact VF_V_pos m a b
  exact lt_of_le_of_lt (add_zero 1).ge (lt_of_lt_of_le (add_lt_add_left 1 hpos) (onePlus_equal A).ge)

/-- Case a: same `a` and `b`, larger `c`. Rocq: `Notation.GrimmT3.psi_mono_c`. -/
theorem psi_mono_c (A B C C' : VForm) (Hn : IsNormal C) (Hn' : IsNormal C')
    (Hlt : denote C < denote C') : denote (vfPsi A B C) < denote (vfPsi A B C') := by
  cases A with
  | Z =>
    cases B with
    | Z =>
      exact lt_of_le_of_lt (le_trans (VF_sum_denote _ Z).le (add_zero _).le)
        (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 (shiftOmega_mono C C' Hn Hn' Hlt))
          (le_trans (add_zero _).ge (VF_sum_denote _ Z).ge))
    | V _ _ _ => exact VF_V_increasing _ _ _ _ (shiftGen_mono _ _ _ _ Hn Hn' Hlt)
  | V _ _ _ => exact VF_V_increasing _ _ _ _ (shiftGen_mono _ _ _ _ Hn Hn' Hlt)

/-- Case b: same `a`, larger `b`, and `c` below the larger bracket.
Rocq: `Notation.GrimmT3.psi_lt_same_a`. -/
theorem psi_lt_same_a (A B B' C C' : VForm) (HB : denote B < denote B')
    (HC : denote C < denote (vfPsi A B' C')) : denote (vfPsi A B C) < denote (vfPsi A B' C') := by
  have HB' : B' ≠ Z := fun e => by
    subst e; exact absurd (lt_of_le_of_lt (zero_least _) HB) (lt_irrefl _)
  have Hhigh := vfPsi_high A B' C' (.inr HB')
  cases A with
  | Z =>
    cases B' with
    | Z => exact absurd rfl HB'
    | V mb' ab' bb' =>
      cases B with
      | Z =>
        exact vf_lt_cross Z _ Z vfOne _ _ (VF_V_pos Z Z Z) (below_high_shift _ Z Z C Hhigh HC).2
          (VF_V_pos _ _ _)
      | V mb ab bb =>
        refine vf_lt_same vfOne _ _ _ _ ?_ (below_high_shift _ vfOne _ C Hhigh HC).1
        exact onePlus_lt_cancel _ _ (lt_of_le_of_lt (onePlus_minus_one _ (fun h => VForm.noConfusion h)).ge
          (lt_of_lt_of_le HB (onePlus_minus_one _ (fun h => VForm.noConfusion h)).le))
  | V _ _ _ => exact vf_lt_same _ _ _ _ _ HB (below_high_shift _ _ B C Hhigh HC).1

/-- Case e: larger `a`, with `b` and `c` below the larger bracket.
Rocq: `Notation.GrimmT3.psi_lt_cross`. -/
theorem psi_lt_cross (A A' B B' C C' : VForm) (HA : denote A < denote A')
    (HB : denote B < denote (vfPsi A' B' C')) (HC : denote C < denote (vfPsi A' B' C')) :
    denote (vfPsi A B C) < denote (vfPsi A' B' C') := by
  have HA' : A' ≠ Z := fun e => by
    subst e; exact absurd (lt_of_le_of_lt (zero_least _) HA) (lt_irrefl _)
  have Hhigh := vfPsi_high A' B' C' (.inl HA')
  cases A' with
  | Z => exact absurd rfl HA'
  | V ma' aa' ba' =>
    have hne : V ma' aa' ba' ≠ Z := fun h => VForm.noConfusion h
    cases A with
    | Z =>
      cases B with
      | Z =>
        exact vf_lt_cross Z _ Z (onePlus (V ma' aa' ba')) _ _
          (lt_trans (succ_lt 0) (VF_onePlus_pos _ hne)) (below_high_shift _ Z Z C Hhigh HC).2
          (VF_V_pos _ _ _)
      | V _ _ _ =>
        exact vf_lt_cross vfOne _ _ (onePlus (V ma' aa' ba')) _ _
          (lt_of_le_of_lt VF_one_denote.le (VF_onePlus_pos _ hne))
          (lt_of_le_of_lt (vfMinusOne_le _) HB) (below_high_shift _ vfOne _ C Hhigh HC).1
    | V _ _ _ =>
      exact vf_lt_cross _ _ _ (onePlus (V ma' aa' ba')) _ _
        (lt_of_le_of_lt (onePlus_equal _).le (lt_of_lt_of_le (add_lt_add_left 1 HA)
          (onePlus_equal _).ge)) HB (below_high_shift _ _ B C Hhigh HC).1

/-- Rocq: `Notation.GrimmT3.T3_denote_psi_vf`. -/
theorem T3_denote_psi_vf (a b c : T3) :
    T3.denote (psi a b c) ≈ denote (vfPsi a.toVF b.toVF c.toVF) :=
  equiv_trans (T3_denote_psi a b c) (vfExponent_correct _ (vfPsi_shape _ _ _))

private theorem and3 {p q r : Bool} (h : (p && q && r) = true) : p = true ∧ q = true ∧ r = true :=
  let ⟨h, hr⟩ := band_true h
  let ⟨hp, hq⟩ := band_true h
  ⟨hp, hq, hr⟩

/-- Rocq: `Notation.GrimmT3.lt_psi_cases`. -/
theorem lt_psi_cases (f : T3 → T3 → Bool) (a b c a' b' c' : T3)
    (H : ltPsiRec f a b c a' b' c' = true) :
    (a = a' ∧ b = b' ∧ f c c' = true) ∨
    (a = a' ∧ f b b' = true ∧ f c (psi a' b' c') = true) ∨
    (a = a' ∧ f b' b = true ∧ f (psi a b c) c' = true) ∨
    (a = a' ∧ f b' b = true ∧ psi a b c = c') ∨
    (f a a' = true ∧ f b (psi a' b' c') = true ∧ f c (psi a' b' c') = true) ∨
    (f a' a = true ∧ f (psi a b c) b' = true) ∨
    (f a' a = true ∧ psi a b c = b') ∨
    (f a' a = true ∧ f (psi a b c) c' = true) ∨
    (f a' a = true ∧ psi a b c = c') := by
  rcases bor_true H with H | H9
  · rcases bor_true H with H | H8
    · rcases bor_true H with H | H7
      · rcases bor_true H with H | H6
        · rcases bor_true H with H | H5
          · rcases bor_true H with H | H4
            · rcases bor_true H with H | H3
              · rcases bor_true H with H1 | H2
                · obtain ⟨ha, hb, hc⟩ := and3 H1
                  exact .inl ⟨(eqb_eq _ _).1 ha, (eqb_eq _ _).1 hb, hc⟩
                · obtain ⟨ha, hb, hc⟩ := and3 H2
                  exact .inr (.inl ⟨(eqb_eq _ _).1 ha, hb, hc⟩)
              · obtain ⟨ha, hb, hc⟩ := and3 H3
                exact .inr (.inr (.inl ⟨(eqb_eq _ _).1 ha, hb, hc⟩))
            · obtain ⟨ha, hb, hc⟩ := and3 H4
              exact .inr (.inr (.inr (.inl ⟨(eqb_eq _ _).1 ha, hb, (eqb_eq _ _).1 hc⟩)))
          · obtain ⟨ha, hb, hc⟩ := and3 H5
            exact .inr (.inr (.inr (.inr (.inl ⟨ha, hb, hc⟩))))
        · obtain ⟨ha, hb⟩ := band_true H6
          exact .inr (.inr (.inr (.inr (.inr (.inl ⟨ha, hb⟩)))))
      · obtain ⟨ha, hb⟩ := band_true H7
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨ha, (eqb_eq _ _).1 hb⟩))))))
    · obtain ⟨ha, hc⟩ := band_true H8
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨ha, hc⟩)))))))
  · obtain ⟨ha, hc⟩ := band_true H9
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨ha, (eqb_eq _ _).1 hc⟩)))))))

/-- Rocq: `Notation.GrimmT3.T3nf_psi_inv`. -/
theorem nf_psi_inv (a b c : T3) (H : nf (psi a b c) = true) :
    nf a = true ∧ nf b = true ∧ nf c = true :=
  let ⟨H, _⟩ := band_true H
  let ⟨H, _⟩ := band_true H
  and3 H

/-- Rocq: `Notation.GrimmT3.T3nf_psi`. -/
theorem nf_psi (a b c : T3) (Ha : nf a = true) (Hb : nf b = true) (Hc : nf c = true) :
    nf (psi a b c) = true :=
  band_intro (band_intro (band_intro (band_intro Ha Hb) Hc) rfl) (lt_zero_cons a b c 0 .zero)

/-- Rocq: `Notation.GrimmT3.T3_to_VF_cons_nonzero`. -/
theorem T3_to_VF_cons_nonzero (a b c : T3) (n : Nat) (d : T3) : T3.toVF (cons a b c n d) ≠ Z := by
  rw [toVF_cons]
  cases d.toVF with
  | Z =>
    cases n with
    | zero => exact vfPsi_nonzero _ _ _
    | succ _ => exact fun h => VForm.noConfusion h
  | V _ _ _ => exact fun h => VForm.noConfusion h

/-- Rocq: `Notation.GrimmT3.T3_denote_cons_pos`. -/
theorem T3_denote_cons_pos (a b c : T3) (n : Nat) (d : T3) : 0 < T3.denote (cons a b c n d) :=
  match isZero (T3.toVF (cons a b c n d)) with
  | .inl h => absurd h (T3_to_VF_cons_nonzero a b c n d)
  | .inr h => h

/-- Rocq: `Notation.GrimmT3.bracket_sound`. -/
theorem bracket_sound (a b c a' b' c' : T3) (Hx : nf (psi a b c) = true)
    (Hy : nf (psi a' b' c') = true) (_Na : IsNormal a.toVF) (_Nb : IsNormal b.toVF)
    (Nc : IsNormal c.toVF) (Na' : IsNormal a'.toVF) (Nb' : IsNormal b'.toVF)
    (Nc' : IsNormal c'.toVF)
    (IH : ∀ u v : T3, size u + size v < size (psi a b c) + size (psi a' b' c') →
      nf u = true → nf v = true → lt u v = true → T3.denote u < T3.denote v)
    (H : ltPsiRec lt a b c a' b' c' = true) : T3.denote (psi a b c) < T3.denote (psi a' b' c') := by
  obtain ⟨Fa, Fb, Fc⟩ := nf_psi_inv a b c Hx
  obtain ⟨Fa', Fb', Fc'⟩ := nf_psi_inv a' b' c' Hy
  have HP' := vfPsi_normal _ _ _ Na' Nb' Nc'
  have Ex := T3_denote_psi_vf a b c
  have Ey := T3_denote_psi_vf a' b' c'
  have Sa := size_a a b c 0 .zero; have Sb := size_b a b c 0 .zero
  have Sc := size_c a b c 0 .zero
  have Sa' := size_a a' b' c' 0 .zero; have Sb' := size_b a' b' c' 0 .zero
  have Sc' := size_c a' b' c' 0 .zero
  have wrap : denote (vfPsi a.toVF b.toVF c.toVF) < denote (vfPsi a'.toVF b'.toVF c'.toVF) →
      T3.denote (psi a b c) < T3.denote (psi a' b' c') := fun h =>
    lt_of_le_of_lt Ex.le (lt_of_lt_of_le h Ey.ge)
  rcases lt_psi_cases _ _ _ _ _ _ _ H with
    ⟨rfl, rfl, Hc⟩ | ⟨rfl, Hb, Hc⟩ | ⟨rfl, _, Hc⟩ | ⟨rfl, _, Hc⟩ | ⟨Ha, Hb, Hc⟩ |
    ⟨_, Hb⟩ | ⟨_, Hb⟩ | ⟨_, Hc⟩ | ⟨_, Hc⟩
  · -- a
    exact wrap (psi_mono_c _ _ _ _ Nc Nc' (IH c c' (pair_lt Sc (Nat.le_of_lt Sc')) Fc Fc' Hc))
  · -- b
    exact wrap (psi_lt_same_a _ _ _ _ _ (IH b b' (pair_lt Sb (Nat.le_of_lt Sb')) Fb Fb' Hb)
      (lt_of_lt_of_le (IH c _ (pair_lt Sc (Nat.le_refl _)) Fc Hy Hc) Ey.le))
  · -- c
    exact lt_trans (IH _ c' (pair_lt' (Nat.le_refl _) Sc') Hx Fc' Hc)
      (lt_of_lt_of_le (psi_gt_c _ _ _ HP') Ey.ge)
  · -- d
    subst Hc; exact lt_of_lt_of_le (psi_gt_c _ _ _ HP') Ey.ge
  · -- e
    exact wrap (psi_lt_cross _ _ _ _ _ _ (IH a a' (pair_lt Sa (Nat.le_of_lt Sa')) Fa Fa' Ha)
      (lt_of_lt_of_le (IH b _ (pair_lt Sb (Nat.le_refl _)) Fb Hy Hb) Ey.le)
      (lt_of_lt_of_le (IH c _ (pair_lt Sc (Nat.le_refl _)) Fc Hy Hc) Ey.le))
  · -- f
    exact lt_trans (IH _ b' (pair_lt' (Nat.le_refl _) Sb') Hx Fb' Hb)
      (lt_of_lt_of_le (psi_gt_b _ _ _ HP') Ey.ge)
  · -- g
    subst Hb; exact lt_of_lt_of_le (psi_gt_b _ _ _ HP') Ey.ge
  · -- h
    exact lt_trans (IH _ c' (pair_lt' (Nat.le_refl _) Sc') Hx Fc' Hc)
      (lt_of_lt_of_le (psi_gt_c _ _ _ HP') Ey.ge)
  · -- i
    subst Hc; exact lt_of_lt_of_le (psi_gt_c _ _ _ HP') Ey.ge

/-! ## The main theorem -/

/-- Rocq: `Notation.GrimmT3.T3nf_cons_inv`. -/
theorem nf_cons_inv (a b c : T3) (n : Nat) (d : T3) (H : nf (cons a b c n d) = true) :
    nf a = true ∧ nf b = true ∧ nf c = true ∧ nf d = true ∧ lt d (psi a b c) = true :=
  let ⟨H, hl⟩ := band_true H
  let ⟨H, hd⟩ := band_true H
  let ⟨ha, hb, hc⟩ := and3 H
  ⟨ha, hb, hc, hd, hl⟩

/-- Rocq: `Notation.GrimmT3.T3_denote_head_bound`. -/
theorem T3_denote_head_bound (a b c d : T3) (H : T3.denote d < T3.denote (psi a b c)) :
    T3.denote d < ω ^ denote (vfExponent (vfPsi a.toVF b.toVF c.toVF)) :=
  lt_of_lt_of_le H (le_trans (T3_denote_psi_vf a b c).le (vfExponent_correct _ (vfPsi_shape _ _ _)).ge)

private theorem size_d_psi (a b c : T3) (n : Nat) (d : T3) :
    size d + size (psi a b c) ≤ size (cons a b c n d) := by
  show size d + (size a + size b + size c) + 1 ≤ size a + size b + size c + size d + 1
  rw [Nat.add_comm (size d) (size a + size b + size c)]
  exact Nat.le_refl _

/-- Rocq: `Notation.GrimmT3.GrimmT3_main`. -/
theorem GrimmT3_main : ∀ m : Nat,
    (∀ t : T3, size t ≤ m → nf t = true → IsNormal t.toVF) ∧
    (∀ u v : T3, size u + size v ≤ m → nf u = true → nf v = true → lt u v = true →
      T3.denote u < T3.denote v) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
  have Hnorm : ∀ t : T3, size t < m → nf t = true → IsNormal t.toVF := fun t ht hnf =>
    (IH (size t) ht).1 t (Nat.le_refl _) hnf
  have Hsound : ∀ u v : T3, size u + size v ≤ m → nf u = true → nf v = true → lt u v = true →
      T3.denote u < T3.denote v := by
    intro u v Hm Hu Hv Huv
    cases u with
    | zero =>
      cases v with
      | zero => rw [lt_zero_r] at Huv; exact Bool.noConfusion Huv
      | cons _ _ _ _ _ => exact T3_denote_cons_pos _ _ _ _ _
    | cons a b c n d =>
      cases v with
      | zero => rw [lt_zero_r] at Huv; exact Bool.noConfusion Huv
      | cons a' b' c' n' d' =>
        have Hsmall : ∀ u' v' : T3, size u' + size v' < size (cons a b c n d) + size (cons a' b' c' n' d') →
            nf u' = true → nf v' = true → lt u' v' = true → T3.denote u' < T3.denote v' :=
          fun u' v' hs => (IH _ (Nat.lt_of_lt_of_le hs Hm)).2 u' v' (Nat.le_refl _)
        obtain ⟨Fa, Fb, Fc, Fd, Hd⟩ := nf_cons_inv _ _ _ _ _ Hu
        obtain ⟨Fa', Fb', Fc', Fd', _⟩ := nf_cons_inv _ _ _ _ _ Hv
        have hU : size (cons a b c n d) ≤ m := Nat.le_trans (Nat.le_add_right _ _) Hm
        have hV : size (cons a' b' c' n' d') ≤ m := Nat.le_trans (Nat.le_add_left _ _) Hm
        have Hdb : T3.denote d < T3.denote (psi a b c) :=
          Hsmall d _ (Nat.lt_of_le_of_lt (size_d_psi a b c n d)
            (Nat.lt_add_of_pos_right (Nat.succ_pos _))) Fd (nf_psi a b c Fa Fb Fc) Hd
        rw [lt_cons] at Huv
        refine lt_of_le_of_lt (T3_denote_cons a b c n d).le
          (lt_of_lt_of_le ?_ (T3_denote_cons a' b' c' n' d').ge)
        cases hpsi : ltPsiRec lt a b c a' b' c' with
        | true =>
          refine sum_lt_head _ _ n n' _ _ (complete _) ?_ (T3_denote_head_bound _ _ _ _ Hdb)
          refine lt_of_le_of_lt (vfExponent_correct _ (vfPsi_shape _ _ _)).le
            (lt_of_lt_of_le ?_ (vfExponent_correct _ (vfPsi_shape _ _ _)).ge)
          refine lt_of_le_of_lt (T3_denote_psi_vf a b c).ge
            (lt_of_lt_of_le ?_ (T3_denote_psi_vf a' b' c').le)
          exact bracket_sound a b c a' b' c' (nf_psi a b c Fa Fb Fc) (nf_psi a' b' c' Fa' Fb' Fc')
            (Hnorm a (Nat.lt_of_lt_of_le (size_a a b c n d) hU) Fa)
            (Hnorm b (Nat.lt_of_lt_of_le (size_b a b c n d) hU) Fb)
            (Hnorm c (Nat.lt_of_lt_of_le (size_c a b c n d) hU) Fc)
            (Hnorm a' (Nat.lt_of_lt_of_le (size_a a' b' c' n' d') hV) Fa')
            (Hnorm b' (Nat.lt_of_lt_of_le (size_b a' b' c' n' d') hV) Fb')
            (Hnorm c' (Nat.lt_of_lt_of_le (size_c a' b' c' n' d') hV) Fc')
            (fun u' v' hs => Hsmall u' v' (Nat.lt_of_lt_of_le hs
              (Nat.add_le_add (size_psi a b c n d) (size_psi a' b' c' n' d'))))
            hpsi
        | false =>
          have Huv : (if (eqb a a' && eqb b b' && eqb c c') = true then
              (if n < n' then true else if n = n' then lt d d' else false) else false) = true := by
            rw [hpsi] at Huv; exact Huv
          cases heq : (eqb a a' && eqb b b' && eqb c c') with
          | false => rw [heq] at Huv; exact Bool.noConfusion Huv
          | true =>
            rw [heq] at Huv
            have Huv : (if n < n' then true else if n = n' then lt d d' else false) = true := Huv
            obtain ⟨ha, hb, hc⟩ := and3 heq
            rw [(eqb_eq _ _).1 ha, (eqb_eq _ _).1 hb, (eqb_eq _ _).1 hc] at Hdb ⊢
            cases Nat.decLt n n' with
            | isTrue hn => exact sum_lt_count _ n n' _ _ hn (T3_denote_head_bound _ _ _ _ Hdb)
            | isFalse hn =>
              rw [ite_eq_right hn] at Huv
              cases Nat.decEq n n' with
              | isTrue e =>
                subst e
                rw [ite_eq_left rfl] at Huv
                exact sum_lt_tail _ (n + 1) _ _
                  (Hsmall d d' (pair_lt (size_d _ _ _ _ _) (Nat.le_of_lt (size_d _ _ _ _ _))) Fd Fd' Huv)
              | isFalse e => rw [ite_eq_right e] at Huv; exact Bool.noConfusion Huv
  refine ⟨fun t Ht Hnf => ?_, Hsound⟩
  cases t with
  | zero => exact trivial
  | cons a b c n d =>
    obtain ⟨Fa, Fb, Fc, Fd, Hd⟩ := nf_cons_inv _ _ _ _ _ Hnf
    exact T3_to_VF_cons_normal a b c n d
      (vfPsi_normal _ _ _ (Hnorm a (Nat.lt_of_lt_of_le (size_a a b c n d) Ht) Fa)
        (Hnorm b (Nat.lt_of_lt_of_le (size_b a b c n d) Ht) Fb)
        (Hnorm c (Nat.lt_of_lt_of_le (size_c a b c n d) Ht) Fc))
      (Hnorm d (Nat.lt_of_lt_of_le (size_d a b c n d) Ht) Fd)
      (lt_of_lt_of_le (Hsound d _ (Nat.le_trans (size_d_psi a b c n d) Ht) Fd
        (nf_psi a b c Fa Fb Fc) Hd) (T3_denote_psi_vf a b c).le)

/-- Grimm's normal forms translate to normal forms of `ATowerNotation`.
Rocq: `Notation.GrimmT3.T3_to_VF_normal`. -/
theorem T3_to_VF_normal (t : T3) (h : nf t = true) : IsNormal t.toVF :=
  (GrimmT3_main (size t)).1 t (Nat.le_refl _) h

/-- Grimm's comparison is sound and complete for the semantic order.
Rocq: `Notation.GrimmT3.T3lt_correct`. -/
theorem T3lt_correct (t u : T3) (Ht : nf t = true) (Hu : nf u = true) :
    lt t u = true ↔ T3.denote t < T3.denote u :=
  ⟨(GrimmT3_main _).2 t u (Nat.le_refl _) Ht Hu, fun hlt =>
    match lt_total t u with
    | .inl h => h
    | .inr (.inl e) => by subst e; exact absurd hlt (lt_irrefl _)
    | .inr (.inr h) =>
      absurd (lt_trans hlt ((GrimmT3_main _).2 u t (Nat.le_refl _) Hu Ht h)) (lt_irrefl _)⟩

/-- Normal forms are unique: equal denotations mean equal terms.
Rocq: `Notation.GrimmT3.T3_denote_inj`. -/
theorem T3_denote_inj (t u : T3) (Ht : nf t = true) (Hu : nf u = true)
    (Heq : T3.denote t ≈ T3.denote u) : t = u :=
  match lt_total t u with
  | .inl h => absurd (lt_of_lt_of_le ((T3lt_correct t u Ht Hu).1 h) Heq.ge) (lt_irrefl _)
  | .inr (.inl e) => e
  | .inr (.inr h) => absurd (lt_of_lt_of_le ((T3lt_correct u t Hu Ht).1 h) Heq.le) (lt_irrefl _)

/-! ## Sanity checks -/

/-- Rocq: `Notation.GrimmT3.t_one`. -/
def tOne : T3 := psi .zero .zero .zero
/-- Rocq: `Notation.GrimmT3.t_two`. -/
def tTwo : T3 := cons .zero .zero .zero 1 .zero
/-- Rocq: `Notation.GrimmT3.t_omega`. -/
def tOmega : T3 := psi .zero .zero tOne
/-- Rocq: `Notation.GrimmT3.t_eps0`. -/
def tEps0 : T3 := psi .zero tOne .zero
/-- Rocq: `Notation.GrimmT3.t_Gamma0`. -/
def tGamma0 : T3 := psi tOne .zero .zero

example : tOne.toVF = V Z Z Z := rfl
example : tOmega.toVF = V Z vfOne Z := rfl
example : tEps0.toVF = V vfOne Z Z := rfl
example : tGamma0.toVF = V (V Z Z vfOne) Z Z := rfl
/-- Ackermann's `(1,1,ε₀)` is `ω^(ε₀+1)`, not `ω^ε₀ = ε₀`. -/
example : (psi .zero .zero tEps0).toVF = V Z (V Z (V vfOne Z Z) vfOne) Z := rfl
/-- Grimm's `ψ(0,Γ₀,0)` lies above `Γ₀`: β-absorption. -/
example : (psi .zero tGamma0 .zero).toVF = V vfOne (V (V Z Z vfOne) Z Z) vfOne := rfl

/-! ## Order type: `AckermannOrdinal` -/

/-- Rocq: `Notation.GrimmT3.VF_V_monotone`. -/
theorem VF_V_monotone (m a b m' a' b' : VForm) (hm : denote m ≤ denote m')
    (ha : denote a ≤ denote a') (hb : denote b ≤ denote b') :
    denote (V m a b) ≤ denote (V m' a' b') :=
  veblen_level_le hm ha hb

/-- A nonzero level: `t_one` in place of `T3zero`. The inner `match` of Rocq's
`vf_up`. -/
def upLevel : T3 → T3
  | .zero => tOne
  | .cons a b c n d => .cons a b c n d

/-- An upper translation: every `VForm` lies below the denotation of a Grimm
bracket. Rocq: `Notation.GrimmT3.vf_up`. -/
def vfUp : VForm → T3
  | Z => .zero
  | V m a b => psi (upLevel (vfUp m)) (vfUp a) (vfUp b)

/-- Rocq: `Notation.GrimmT3.vf_up_nf`. -/
theorem vfUp_nf : ∀ x : VForm, nf (vfUp x) = true
  | Z => rfl
  | V m a b => by
    refine nf_psi _ _ _ ?_ (vfUp_nf a) (vfUp_nf b)
    have hm := vfUp_nf m
    revert hm
    cases vfUp m with
    | zero => exact fun _ => rfl
    | cons _ _ _ _ _ => exact id

private theorem vfUp_step (m a b : VForm) (am ua ub : T3) (hnz : am.toVF ≠ Z)
    (hle : denote m ≤ 1 + T3.denote am) (ha : denote a ≤ T3.denote ua)
    (hb : denote b ≤ T3.denote ub) : denote (V m a b) ≤ T3.denote (psi am ua ub) := by
  refine le_trans ?_ (T3_denote_psi_vf am ua ub).ge
  revert hnz hle
  show am.toVF ≠ Z → denote m ≤ 1 + denote am.toVF →
    denote (V m a b) ≤ denote (vfPsi am.toVF ua.toVF ub.toVF)
  cases am.toVF with
  | Z => exact fun h => absurd rfl h
  | V _ _ _ =>
    exact fun _ hle => VF_V_monotone _ _ _ _ _ _ (le_trans hle (onePlus_equal _).ge) ha
      (le_trans hb (shiftGen_bounds _ _ _).1)

/-- Rocq: `Notation.GrimmT3.vf_up_ge`. -/
theorem vfUp_ge : ∀ x : VForm, denote x ≤ T3.denote (vfUp x)
  | Z => zero_least _
  | V m a b => by
    refine vfUp_step m a b _ _ _ ?_ ?_ (vfUp_ge a) (vfUp_ge b)
    · cases vfUp m with
      | zero => exact fun h => VForm.noConfusion h
      | cons _ _ _ _ _ => exact T3_to_VF_cons_nonzero _ _ _ _ _
    · have hm := vfUp_ge m
      revert hm
      cases vfUp m with
      | zero => exact fun hm => le_trans hm (zero_least _)
      | cons _ _ _ _ _ => exact fun hm => le_trans hm (le_add_left 1 _)

/-- The ordinal of Grimm's normal forms. Rocq: `Notation.GrimmT3.T3ord`. -/
def T3ord : Ordinal.{0} := mk {t : T3 // nf t = true} fun t => T3.denote t.1

/-- Grimm's (that is, Ackermann's) normal forms, ordered by `lt`
(`T3lt_correct`), have order type `AckermannOrdinal`.
Rocq: `Notation.GrimmT3.T3_AO`. -/
theorem T3_AO : T3ord ≈ AckermannOrdinal :=
  equiv_intro (le_intro fun t => below_AO t.1.toVF)
    (le_trans VF_AO.ge (le_intro fun x =>
      lt_of_le_of_lt (vfUp_ge x) (index_lt T3ord ⟨vfUp x, vfUp_nf x⟩)))

end ConstructiveOrdinals.GrimmT3
