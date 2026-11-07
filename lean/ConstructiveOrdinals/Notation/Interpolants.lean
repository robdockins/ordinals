import ConstructiveOrdinals.Reflection
import ConstructiveOrdinals.Veblen.Constructive
import ConstructiveOrdinals.Classical

/-!
# Interpolants

Port of `Ordinal/Notation/Interpolants.v`.

An ordinal `z` has interpolants in a notation system `f : A → Ordinal`
(with well-formedness predicate `P`) when everything below `z` is bounded by a
notation below `z` which itself has interpolants. With the excluded middle,
interpolants for every notation are equivalent to every ordinal below a
notation being denoted by a notation (`has_interpolants_has_enough_notations`);
without it they are a constructive substitute, and are preserved by the usual
ways of building notation systems: sums, fixpoints and Veblen hierarchies.

The only fact needed about the notation system is that notations denote
complete ordinals (`hcomplete`, Rocq's `f_complete`).
-/

namespace ConstructiveOrdinals.Interpolants

open Ordinal

variable {A : Type} {f : A → Ordinal.{0}} {P : A → Prop} (hcomplete : ∀ a, Complete (f a))


/-- `z` has interpolants when every `i < z` is bounded by a well-formed term
below `z` that itself has interpolants. The recursion is on the
accessibility of `z`. Rocq: `Notation.Interpolants.has_interpolants_rec`. -/
def HasInterpolantsRec (f : A → Ordinal.{0}) (P : A → Prop) {z : Ordinal.{0}}
    (h : Acc (· < ·) z) : Prop :=
  Acc.rec (motive := fun _ _ => Prop)
    (fun z _ ih => ∀ i, i < z → ∃ (y : A) (hlt : f y < z), P y ∧ i ≤ f y ∧ ih (f y) hlt) h

/-- The accessibility proof does not matter. In Lean this holds by definitional
proof irrelevance. Rocq: `Notation.Interpolants.has_interpolants_rec_H_irrelevant`. -/
theorem has_interpolants_rec_H_irrelevant (z : Ordinal.{0}) (H1 H2 : Acc (· < ·) z) :
    HasInterpolantsRec f P H1 → HasInterpolantsRec f P H2 := id

/-- Rocq: `Notation.Interpolants.has_interpolants_rec_eq_mor`. -/
theorem has_interpolants_rec_eq_mor (x y : Ordinal.{0}) (H1 : Acc (· < ·) x)
    (H2 : Acc (· < ·) y) (hxy : x ≈ y) :
    HasInterpolantsRec f P H1 → HasInterpolantsRec f P H2 := by
  cases H1 with
  | intro _ h1 =>
    cases H2 with
    | intro _ h2 =>
      intro hx i hi
      obtain ⟨z, hz, hPz, hiz, hrec⟩ := hx i (lt_of_lt_of_le hi hxy.ge)
      exact ⟨z, lt_of_lt_of_le hz hxy.le, hPz, hiz, hrec⟩

/-- Rocq: `Notation.Interpolants.has_interpolants`. -/
def HasInterpolants (f : A → Ordinal.{0}) (P : A → Prop) (z : Ordinal.{0}) : Prop :=
  HasInterpolantsRec f P (lt_wf.apply z)

private theorem has_interpolants_rec_unfold {z : Ordinal.{0}} (H : Acc (· < ·) z) :
    HasInterpolantsRec f P H ↔
      ∀ i, i < z → ∃ y : A, P y ∧ i ≤ f y ∧ f y < z ∧ HasInterpolants f P (f y) := by
  cases H with
  | intro _ h =>
    show (∀ i, i < z → ∃ (y : A) (hlt : f y < z), P y ∧ i ≤ f y ∧
        HasInterpolantsRec f P (h (f y) hlt)) ↔ _
    exact ⟨fun hz i hi => let ⟨y, hlt, hPy, hiy, hrec⟩ := hz i hi; ⟨y, hPy, hiy, hlt, hrec⟩,
      fun hz i hi => let ⟨y, hPy, hiy, hlt, hrec⟩ := hz i hi; ⟨y, hlt, hPy, hiy, hrec⟩⟩

/-- Rocq: `Notation.Interpolants.has_interpolants_unfold`. -/
theorem has_interpolants_unfold (z : Ordinal.{0}) :
    HasInterpolants f P z ↔
      ∀ i, i < z → ∃ y : A, P y ∧ i ≤ f y ∧ f y < z ∧ HasInterpolants f P (f y) :=
  has_interpolants_rec_unfold _

/-- Rocq: `Notation.Interpolants.has_interpolants_eq_mor`. -/
theorem has_interpolants_eq_mor {x y : Ordinal.{0}} (h : x ≈ y) :
    HasInterpolants f P x ↔ HasInterpolants f P y :=
  ⟨has_interpolants_rec_eq_mor x y _ _ h, has_interpolants_rec_eq_mor y x _ _ (equiv_symm h)⟩

/-- Every well-formed term has interpolants.
Rocq: `Notation.Interpolants.has_all_interpolants`. -/
def HasAllInterpolants (f : A → Ordinal.{0}) (P : A → Prop) : Prop :=
  ∀ a, P a → HasInterpolants f P (f a)

/-- Every ordinal below a well-formed term has a notation.
Rocq: `Notation.Interpolants.has_enough_notations`. -/
def HasEnoughNotations (f : A → Ordinal.{0}) (P : A → Prop) : Prop :=
  ∀ (a : A) (x : Ordinal.{0}), P a → x ≤ f a → ∃ b, P b ∧ f b ≈ x

/-- Induction on the denotation of a term. -/
private theorem measure_ind (f : A → Ordinal.{0}) {motive : A → Prop}
    (h : ∀ a, (∀ b, f b < f a → motive b) → motive a) (a : A) : motive a :=
  ltRec (motive := fun o => ∀ a, f a ≤ o → motive a)
    (fun _ ih a ha => h a fun b hb => ih (f b) (lt_of_lt_of_le hb ha) b (le_refl _))
    (f a) a (le_refl _)

/-- Rocq: `Notation.Interpolants.has_enough_notations_has_all_interpolants`. -/
theorem has_enough_notations_has_all_interpolants (H : HasEnoughNotations f P) :
    HasAllInterpolants f P :=
  measure_ind f fun a ih ha => (has_interpolants_unfold _).2 fun i hi =>
    let ⟨x, hx₁, hx₂⟩ := H a i ha (le_of_lt hi)
    have hxa : f x < f a := lt_of_le_of_lt hx₂.le hi
    ⟨x, hx₁, hx₂.ge, hxa, ih x hxa hx₁⟩

/-- Rocq: `Notation.Interpolants.has_interpolants_has_enough_notations`. -/
theorem has_interpolants_has_enough_notations (em : ExcludedMiddle)
    (Hinterp : HasAllInterpolants f P) : HasEnoughNotations f P := by
  intro a i ha hi
  let Q := fun o => ∃ v : A, P v ∧ i ≤ f v ∧ o ≈ f v
  obtain ⟨z, ⟨v, hv₁, hv₂, hv₃⟩, hz⟩ := ord_well_ordered em Q (f a) ⟨a, ha, hi, equiv_refl _⟩
  refine ⟨v, hv₁, equiv_intro ?_ hv₂⟩
  cases order_total em (f v) i with
  | inl h => exact h
  | inr h =>
    obtain ⟨q, hq₁, hq₂, hq₃, _⟩ := (has_interpolants_unfold _).1 (Hinterp v hv₁) i h
    exact (lt_irrefl z (lt_of_le_of_lt (hz (f q) ⟨q, hq₁, hq₂, equiv_refl _⟩)
      (lt_of_lt_of_le hq₃ hv₃.ge))).elim

/-- Rocq: `Notation.Interpolants.has_interpolants_lub`. -/
theorem has_interpolants_lub (p q : Ordinal.{0}) (hp : HasInterpolants f P p)
    (hq : HasInterpolants f P q) : HasInterpolants f P (p ⊔ q) :=
  (has_interpolants_unfold _).2 fun i hi =>
    match lub_lt hi with
    | .inl hi =>
      let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hp i hi
      ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (lub_le1 p q), hy₄⟩
    | .inr hi =>
      let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hq i hi
      ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (lub_le2 p q), hy₄⟩

/-- Rocq: `Notation.Interpolants.has_interpolants_sup`. -/
theorem has_interpolants_sup (B : Type) (g : B → Ordinal.{0})
    (hg : ∀ b, HasInterpolants f P (g b)) : HasInterpolants f P (sup g) :=
  (has_interpolants_unfold _).2 fun i hi =>
    let ⟨b, hi⟩ := sup_lt hi
    let ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg b) i hi
    ⟨y, hy₁, hy₂, lt_of_lt_of_le hy₃ (sup_le g b), hy₄⟩

/-- Rocq: `Notation.Interpolants.has_interpolants_add`. -/
theorem has_interpolants_add (add : A → A → A)
    (hadd : Reflects A f P (.ord ==> .ord ==> .ord) (· + ·) add) (p : A) :
    ∀ q : Ordinal.{0}, P p → HasInterpolants f P (f p) → HasInterpolants f P q →
      HasInterpolants f P (f p + q) := by
  intro q
  refine ltRec (motive := fun q => P p → HasInterpolants f P (f p) → HasInterpolants f P q →
    HasInterpolants f P (f p + q)) (fun q ih hp₁ hp₂ hq => ?_) q
  rw [add_unfold]
  refine has_interpolants_lub _ _ hp₂ ((has_interpolants_unfold _).2 fun i hi => ?_)
  obtain ⟨q', hi⟩ := sup_lt hi
  obtain ⟨_, hi⟩ := lt_elim hi
  obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hq (q q') (index_lt q q')
  obtain ⟨hadd₁, hadd₂⟩ := hadd (f p) p ⟨equiv_refl _, hp₁⟩ (f y) y ⟨equiv_refl _, hy₁⟩
  refine ⟨add p y, hadd₂, le_trans hi (le_trans (add_le_add (le_refl _) hy₂) hadd₁.le), ?_,
    (has_interpolants_eq_mor hadd₁).1 (ih (f y) hy₃ hp₁ hp₂ hy₄)⟩
  obtain ⟨q'', hq''⟩ := lt_elim hy₃
  exact lt_of_le_of_lt hadd₁.ge (lt_of_lt_of_le (succ_lt _)
    (le_trans (succ_monotone (add_le_add (le_refl _) hq''))
      (sup_le (fun i : q => succ (f p + q i)) q'')))

section fix_interpolants

variable (g : Ordinal.{0} → Ordinal.{0})

/-- Rocq: `Notation.Interpolants.iter_has_interpolants`. -/
theorem iter_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b)) :
    ∀ (m : Nat) (b : Ordinal.{0}), Complete b → HasInterpolants f P b →
      HasInterpolants f P (iterF g b m)
  | 0, _, _, hb => hb
  | m + 1, b, hb₁, hb₂ =>
    hg₂ _ (iterF_complete m b hb₁ hg₁) (iter_has_interpolants hg₁ hg₂ m b hb₁ hb₂)

/-- Rocq: `Notation.Interpolants.fix_has_interpolants`. -/
theorem fix_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
    (b : Ordinal.{0}) (hb₁ : Complete b) (hb₂ : HasInterpolants f P b) :
    HasInterpolants f P (fixOrd g b) :=
  has_interpolants_sup _ _ fun n => iter_has_interpolants g hg₁ hg₂ n.down b hb₁ hb₂

include hcomplete in
/-- Rocq: `Notation.Interpolants.enum_fix_has_interpolants`. -/
theorem enum_fix_has_interpolants (hg₁ : ∀ b, Complete b → Complete (g b))
    (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
    (hg₃ : ∀ x y, x ≤ y → g x ≤ g y) (hg₄ : ∀ x, Complete x → x ≤ g x)
    (enum_gr : A → A) (hgr : Reflects A f P (.ord ==> .ord) (enumFixpoints g) enum_gr) :
    ∀ b : Ordinal.{0}, Complete b → HasInterpolants f P b →
      HasInterpolants f P (enumFixpoints g b) := by
  intro b
  refine ltRec (motive := fun b => Complete b → HasInterpolants f P b →
    HasInterpolants f P (enumFixpoints g b)) (fun b ih hb₁ hb₂ => ?_) b
  rw [enumFixpoints_unfold]
  refine fix_has_interpolants g hg₁ hg₂ _ ?_ ((has_interpolants_unfold _).2 fun i hi => ?_)
  · exact lim_complete (fun a => enumFixpoints_complete hg₄ hg₃ hg₁ _ (complete_subord hb₁ a))
      (directed_monotone b _ (fun x y hxy => enumFixpoints_monotone hg₃ _ _ hxy) hb₁)
      (cast (complete_unfold b) hb₁).2.1
  obtain ⟨k, hi⟩ := lt_elim hi
  obtain ⟨br, hbr₁, hbr₂, hbr₃, hbr₄⟩ := (has_interpolants_unfold _).1 hb₂ (b k) (index_lt b k)
  obtain ⟨h₁, h₂⟩ := hgr (f br) br ⟨equiv_refl _, hbr₁⟩
  obtain ⟨b', hb'⟩ := lt_elim hbr₃
  exact ⟨enum_gr br, h₂, le_trans hi (le_trans (enumFixpoints_monotone hg₃ _ _ hbr₂) h₁.le),
    lt_intro (show (mk b.Carrier fun b' => enumFixpoints g (b b')).Carrier from b')
      (le_trans h₁.ge (enumFixpoints_monotone hg₃ _ _ hb')),
    (has_interpolants_eq_mor h₁).1 (ih (f br) hbr₃ (hcomplete br) hbr₄)⟩

end fix_interpolants

/-- Rocq: `Notation.Interpolants.onePlus_interpolants`. -/
theorem onePlus_interpolants (zr : A) (hzr : Reflects A f P .ord 0 zr) (pr : A → A)
    (hpr : Reflects A f P (.ord ==> .ord) (fun x => 1 + x) pr) :
    ∀ b : Ordinal.{0}, HasInterpolants f P b → HasInterpolants f P (1 + b) := by
  intro b
  refine ltRec (motive := fun b => HasInterpolants f P b → HasInterpolants f P (1 + b))
    (fun b ih hb => (has_interpolants_unfold _).2 fun i hi => ?_) b
  rw [add_unfold] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨_, hi⟩ := lt_elim hi
    refine ⟨zr, hzr.2, le_trans hi hzr.1.le,
      lt_of_le_of_lt hzr.1.ge (lt_of_lt_of_le (succ_lt 0) (le_add_right _ _)),
      (has_interpolants_unfold _).2 fun i' hi' => ?_⟩
    exact (lt_irrefl i' (lt_of_lt_of_le (lt_of_lt_of_le hi' hzr.1.ge) (zero_least _))).elim
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    obtain ⟨_, hi⟩ := lt_elim hi
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hb (b j) (index_lt b j)
    obtain ⟨hp₁, hp₂⟩ := hpr (f y) y ⟨equiv_refl _, hy₁⟩
    exact ⟨pr y, hp₂, le_trans hi (le_trans (add_le_add (le_refl _) hy₂) hp₁.le),
      lt_of_le_of_lt hp₁.ge (add_lt_add_left 1 hy₃), (has_interpolants_eq_mor hp₁).1 (ih _ hy₃ hy₄)⟩

section veblen_interpolants

variable (g : Ordinal.{0} → Ordinal.{0}) (hg₁ : NormalFunction g)
  (hg₂ : ∀ b, Complete b → HasInterpolants f P b → HasInterpolants f P (g b))
  (vr : A → A → A) (hvr : Reflects A f P (.ord ==> .ord ==> .ord) (veblen g) vr)

include hcomplete hg₁ hg₂ hvr in
/-- Rocq: `Notation.Interpolants.veblen_interpolants`. -/
theorem veblen_interpolants : ∀ (a : A) (b : Ordinal.{0}), P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b) := by
  have mono := hg₁.monotone
  intro a
  refine measure_ind f (motive := fun a => ∀ b : Ordinal.{0}, P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b))
    (fun a iha => ?_) a
  intro b
  refine ltRec (motive := fun b => P a → HasInterpolants f P (f a) →
    Complete b → HasInterpolants f P b → HasInterpolants f P (veblen g (f a) b))
    (fun b ihb ha₁ ha₂ hb₁ hb₂ => (has_interpolants_unfold _).2 fun i hi => ?_) b
  rw [veblen_unroll] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg₂ b hb₁ hb₂) i hi
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    rw [veblen_unroll]
    exact lt_of_lt_of_le hy₃ (lub_le1 _ _)
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    -- the limit of `veblen g (f a)` below `b`
    have hb' : HasInterpolants f P (lim fun x : b => veblen g (f a) (b x)) := by
      refine (has_interpolants_unfold _).2 fun i₀ hi₀ => ?_
      obtain ⟨k, hi₀⟩ := lt_elim hi₀
      obtain ⟨q, hq₁, hq₂, hq₃, hq₄⟩ := (has_interpolants_unfold _).1 hb₂ (b k) (index_lt b k)
      obtain ⟨hv₁, hv₂⟩ := hvr (f a) a ⟨equiv_refl _, ha₁⟩ (f q) q ⟨equiv_refl _, hq₁⟩
      obtain ⟨k', hk'⟩ := lt_elim hq₃
      exact ⟨vr a q, hv₂, le_trans hi₀ (le_trans (veblen_monotone mono _ _ _ hq₂) hv₁.le),
        lt_intro (show (lim fun x : b => veblen g (f a) (b x)).Carrier from k')
          (le_trans hv₁.ge (veblen_monotone mono _ _ _ hk')),
        (has_interpolants_eq_mor hv₁).1 (ihb (f q) hq₃ ha₁ ha₂ (hcomplete q) hq₄)⟩
    have hb'c : Complete (lim fun x : b => veblen g (f a) (b x)) :=
      lim_complete (fun x => veblen_complete hg₁ hg₁.complete _ (hcomplete a) _
          (complete_subord hb₁ x))
        (directed_monotone b _ (fun x y hxy => veblen_monotone mono _ _ _ hxy) hb₁)
        (cast (complete_unfold b) hb₁).2.1
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ :=
      (has_interpolants_unfold _).1 ha₂ ((f a) j) (index_lt (f a) j)
    have hi' : i < fixOrd (veblen g (f y)) (lim fun x : b => veblen g (f a) (b x)) :=
      lt_of_lt_of_le hi (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hy₂)
        (fun x y hxy => veblen_monotone mono _ _ _ hxy) _)
    have hfix := fix_has_interpolants (veblen g (f y))
      (fun x hx => (veblen_normal hg₁ _ (hcomplete y)).complete x hx)
      (fun x hx₁ hx₂ => iha y hy₃ x hy₁ hy₄ hx₁ hx₂) _ hb'c hb'
    obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    refine ⟨z, hz₁, hz₂, ?_, hz₄⟩
    obtain ⟨zq, hzq⟩ := lt_elim hy₃
    rw [veblen_unroll]
    refine lt_of_lt_of_le hz₃ (le_trans ?_ (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun α : (f a).Carrier =>
      fixOrd (veblen g ((f a) α)) (lim fun x : b => veblen g (f a) (b x))) zq)
    exact fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hzq)
      (fun x y hxy => veblen_monotone mono _ _ _ hxy) _

include hcomplete hg₁ hg₂ hvr in
/-- Rocq: `Notation.Interpolants.veblen_interpolants_first`. -/
theorem veblen_interpolants_first (a : Ordinal.{0}) (_ha₁ : Complete a)
    (ha₂ : HasInterpolants f P a) : HasInterpolants f P (veblen g a 0) := by
  have mono := hg₁.monotone
  have h0 : HasInterpolants f P 0 :=
    (has_interpolants_unfold _).2 fun j hj =>
      (lt_irrefl j (lt_of_lt_of_le hj (zero_least j))).elim
  refine (has_interpolants_unfold _).2 fun i hi => ?_
  rw [veblen_unroll] at hi
  match lub_lt hi with
  | .inl hi =>
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 (hg₂ 0 zero_complete h0) i hi
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    rw [veblen_unroll]
    exact lt_of_lt_of_le hy₃ (lub_le1 _ _)
  | .inr hi =>
    obtain ⟨j, hi⟩ := sup_lt hi
    obtain ⟨k, hk₁, hk₂, hk₃, hk₄⟩ := (has_interpolants_unfold _).1 ha₂ (a j) (index_lt a j)
    have hL : (lim fun x : (0 : Ordinal.{0}).Carrier => veblen g a ((0 : Ordinal.{0}) x)) ≤ 0 :=
      le_intro fun x => nomatch x
    have hi' : i < fixOrd (veblen g (f k)) 0 :=
      lt_of_lt_of_le hi (le_trans (fixOrd_monotone (veblen_monotone mono _) hL)
        (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hk₂)
          (fun x y hxy => veblen_monotone mono _ _ _ hxy) _))
    have hfix := fix_has_interpolants (veblen g (f k))
      (fun x hx => veblen_complete hg₁ hg₁.complete _ (hcomplete k) x hx)
      (fun x hx₁ hx₂ => veblen_interpolants hcomplete g hg₁ hg₂ vr hvr k x hk₁ hk₄ hx₁ hx₂) 0
      zero_complete h0
    obtain ⟨y, hy₁, hy₂, hy₃, hy₄⟩ := (has_interpolants_unfold _).1 hfix i hi'
    refine ⟨y, hy₁, hy₂, ?_, hy₄⟩
    obtain ⟨q, hq⟩ := lt_elim hk₃
    rw [veblen_unroll]
    refine lt_of_lt_of_le hy₃ (le_trans ?_ (lub_le2 _ _))
    refine le_trans ?_ (sup_le (fun α : a.Carrier =>
      fixOrd (veblen g (a α)) (lim fun x : (0 : Ordinal.{0}).Carrier =>
        veblen g a ((0 : Ordinal.{0}) x))) q)
    exact le_trans (fixOrd_monotone (veblen_monotone mono _) (zero_least _))
      (fixOrd_monotone_func (fun x => veblen_monotone_first mono _ _ x hq)
        (fun x y hxy => veblen_monotone mono _ _ _ hxy) _)

end veblen_interpolants

end ConstructiveOrdinals.Interpolants
