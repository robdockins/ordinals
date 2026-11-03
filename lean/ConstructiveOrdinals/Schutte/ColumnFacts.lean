import ConstructiveOrdinals.Schutte.Column
import ConstructiveOrdinals.AckermannTower
import ConstructiveOrdinals.Prelude.List

/-!
# Facts about Schütte columns

The relationship between `schutteColumn` and the Veblen hierarchy and the
Ackermann tower. Also: critical and unreachable ordinals and the E-numbers;
the small and large Veblen ordinals; and Schütte's Klammersymbole as stacks and
matrices of columns.

Ported from the Rocq file `SchutteColumnFacts.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

private theorem one_complete : Complete (1 : Ordinal.{u}) := succ_complete zero_complete

private theorem zero_lt_one' : (0 : Ordinal.{u}) < 1 := succ_lt 0

private theorem lim_zero_le' {g : (0 : Ordinal.{u}).Carrier → Ordinal.{u}} (z : Ordinal.{u}) : lim g ≤ z :=
  limit_least fun e => PEmpty.elim e

private theorem lim_zero_complete' {g : (0 : Ordinal.{u}).Carrier → Ordinal.{u}} : Complete (lim g) :=
  lim_complete (fun e => PEmpty.elim e) (fun e _ => PEmpty.elim e) (.inr fun ⟨e⟩ => PEmpty.elim e)

/-- `δ ↦ schutteColumn (schutteColumn f β a) b δ 0` is normal. -/
private theorem normal_col_arg {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {β a b : Ordinal.{u}}
    (hβ : Complete β) (ha : Complete a) (hb : Complete b) :
    NormalFunction fun δ => schutteColumn (schutteColumn f β a) b δ 0 :=
  schutte_column_normal_arg b _ hb (schutte_column_normal β a f hβ ha hf)

/-- Rocq: `SchutteColumnFacts.schutte_column_veblen`. -/
theorem schutte_column_veblen (α : Ordinal.{u}) :
    ∀ (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}), NormalFunction f → Complete α → Complete x →
      schutteColumn f 1 α x ≈ veblen f α x := by
  induction α using ltRec with
  | ind α ihα =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro f hf hα hx
  have hV := veblen_complete hf hf.complete α hα x hx
  have hY := (schutte_column_normal 1 α f one_complete hα hf).complete x hx
  refine equiv_intro ?_ ?_
  · rw [schutte_column_unroll]
    refine lub_least (veblen_fax hf α x hα hx) (sup_least fun _ => sup_least fun a => ?_)
    have hαa := complete_subord hα a
    refine normal_fix_least (normal_col_arg hf one_complete hαa zero_complete) _ _ hV
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) f hf hα (complete_subord hx i)).le
        (veblen_increasing hf α hα _ _ hx (index_lt x i))) ?_
    refine le_trans (schutte_column0 _ _ 0).le ?_
    refine le_trans (ihα (α a) (index_lt α a) _ f hf hαa (add_complete hV zero_complete)).le ?_
    exact le_trans (veblen_monotone hf.monotone (α a) _ _ (add_zero _).le)
      (veblen_fixpoints hf (α a) α x hαa hα hx (index_lt α a)).le
  · rw [veblen_unroll]
    refine lub_least (le_trans (hf.monotone _ _ (le_add_left α x)) (schutte_column_le_f 1 α x f hf.monotone))
      (sup_least fun a => ?_)
    have hαa := complete_subord hα a
    refine normal_fix_least (veblen_normal hf (α a) hαa) _ _ hY
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) f hf hα (complete_subord hx i)).ge
        ((schutte_column_normal 1 α f one_complete hα hf).increasing _ _ hx (index_lt x i))) ?_
    refine le_trans (ihα (α a) (index_lt α a) _ f hf hαa hY).ge ?_
    refine le_trans (schutte_column_monotone f 1 _ _ _ _ hf.monotone (le_refl _) (add_zero _).ge) ?_
    refine le_trans (schutte_column0 _ _ 0).ge ?_
    exact schutte_column_fixpoint 1 α x f 0 (α a) one_complete hα hf zero_lt_one' (index_lt α a) zero_complete
      hαa hx

/-- Rocq: `SchutteColumnFacts.schutte_column_add_closed`. -/
theorem schutte_column_add_closed (f : Ordinal.{u} → Ordinal.{u}) (β α x p q : Ordinal.{u})
    (hf : NormalFunction f) (hβ : Complete β) (hα : Complete α) (hx : Complete x) (h1β : 1 < β) (hα₀ : 0 < α)
    (hp : p < schutteColumn f β α x) (hq : q < schutteColumn f β α x) : p + q < schutteColumn f β α x := by
  have hY := (schutte_column_normal β α f hβ hα hf).complete x hx
  have h0 := schutte_column_normal β 0 f hβ zero_complete hf
  have hpow : ω ^ schutteColumn f β α x ≤ schutteColumn f β α x :=
    le_trans (add_zero _).ge (le_trans (veblen_onePlus _ hY 0 zero_complete).ge
      (le_trans (veblen_monotone_func onePlus_normal h0 (fun z hz => onePlus_least_normal h0 z hz) _ 0 hY
        zero_complete) (le_trans (schutte_column_veblen _ 0 _ h0 hY zero_complete).ge
          (schutte_column_fixpoint β α x f 1 0 hβ hα hf h1β hα₀ one_complete zero_complete hx))))
  have hinf : schutteColumn f β α x ≤ ω ^ schutteColumn f β α x :=
    le_trans (normal_inflationary (veblen_first_normal onePlus_normal) _ hY)
      (le_trans (veblen_onePlus _ hY 0 zero_complete).le (add_zero _).le)
  exact lt_of_lt_of_le (powOmega_additively_closed hY p q (lt_of_lt_of_le hp hinf) (lt_of_lt_of_le hq hinf)) hpow

/-- Rocq: `SchutteColumnFacts.schutte_column_preserves_add_closed`. -/
theorem schutte_column_preserves_add_closed (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hf₂ : ∀ x p q, Complete x → p < f x → q < f x → p + q < f x) :
    ∀ x β α p q, Complete x → Complete β → Complete α →
      p < schutteColumn f β α x → q < schutteColumn f β α x → p + q < schutteColumn f β α x := by
  intro x β α p q hx hβ hα hp hq
  have transfer : ∀ z, Complete z → schutteColumn f β α x ≈ f z → p + q < schutteColumn f β α x :=
    fun z hz heq => lt_of_lt_of_le (hf₂ z p q hz (lt_of_lt_of_le hp heq.le) (lt_of_lt_of_le hq heq.le)) heq.ge
  match complete_zeroDec hβ, complete_zeroDec hα with
  | .inl hβ₀, _ =>
    exact transfer _ (add_complete hα hx) (equiv_intro
      (le_trans (schutte_column_monotoneβ β 0 α x f hf.monotone hβ₀) (schutte_column0 f α x).le)
      (schutte_column_le_f β α x f hf.monotone))
  | _, .inl hα₀ =>
    exact transfer _ hx (equiv_intro
      (le_trans (schutte_column_monotone f β α x 0 x hf.monotone hα₀ (le_refl x))
        (schutte_column_arg0 β x f hf.monotone).le)
      (le_trans (hf.monotone _ _ (le_add_left α x)) (schutte_column_le_f β α x f hf.monotone)))
  | .inr hβ₀, .inr hα₀ =>
    have hY := (schutte_column_normal β α f hβ hα hf).complete x hx
    exact transfer _ hY (equiv_intro (normal_inflationary hf _ hY)
      (le_trans (hf.monotone _ _ (add_zero _).ge) (le_trans (schutte_column_arg0 β _ f hf.monotone).ge
        (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint β α x f 0 0 hβ hα hf hβ₀ hα₀
          zero_complete zero_complete hx)))))

/-- `x` is a common fixpoint of the columns below `(β, α)`.
Rocq: `SchutteColumnFacts.schutte_critical`. -/
def SchutteCritical (f : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) : Prop :=
  ∀ b a, Complete b → Complete a → b < β → a < α → schutteColumn (schutteColumn f β a) b x 0 ≈ x

/-- Rocq: `SchutteColumnFacts.schutte_supercritical`. -/
def SchutteSupercritical (f : Ordinal.{u} → Ordinal.{u}) (β α : Ordinal.{u}) : Prop :=
  0 < α ∧ SchutteCritical f β α α

/-- Rocq: `SchutteColumnFacts.schutte_hypercritical`. -/
def SchutteHypercritical (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  0 < β ∧ SchutteCritical f β 1 β

/-- `E` cannot be reached from below by `schutteColumn f`.
Rocq: `SchutteColumnFacts.schutte_unreachable`. -/
def SchutteUnreachable (f : Ordinal.{u} → Ordinal.{u}) (E : Ordinal.{u}) : Prop :=
  0 < E ∧ ∀ β α x, Complete β → Complete α → Complete x → β < E → α < E → x < E → schutteColumn f β α x < E

/-- Rocq: `SchutteColumnFacts.schutte_supercritical_alt`. -/
theorem schutte_supercritical_alt (f : Ordinal.{u} → Ordinal.{u}) (β α : Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) (hα : Complete α) (hβ₀ : 0 < β) :
    SchutteSupercritical f β α ↔ schutteColumn f β α 0 ≈ α := by
  refine ⟨fun ⟨hα₀, h⟩ => ?_, fun h => ?_⟩
  · refine equiv_intro (le_trans (schutte_column_gt0 β α f 0 hβ hα zero_complete hf hβ₀ hα₀).le
      (sup_least fun b => sup_least fun a => ?_))
      (schutte_column_inflationary1 β α 0 f (normal_inflationary hf) hα zero_complete)
    exact normal_fix_least (normal_col_arg hf hβ (complete_subord hα a) (complete_subord hβ b)) _ _ hα
      (lim_zero_le' _) (h _ _ (complete_subord hβ b) (complete_subord hα a) (index_lt β b) (index_lt α a)).le
  · refine ⟨lt_of_lt_of_le (schutte_column_nonzero f β α 0 hf) h.le, fun b a hb ha hbβ haα => ?_⟩
    have hN := schutte_column_normal β a f hβ ha hf
    exact equiv_intro (le_trans (schutte_column_monotone _ b _ 0 _ 0 hN.monotone h.ge (le_refl 0))
        (le_trans (schutte_column_fixpoint β α 0 f b a hβ hα hf hbβ haα hb ha zero_complete) h.le))
      (schutte_column_inflationary1 b α 0 _ (normal_inflationary hN) hα zero_complete)

/-- Rocq: `SchutteColumnFacts.schutte_hypercritical_alt`. -/
theorem schutte_hypercritical_alt (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) : SchutteHypercritical f β ↔ schutteColumn f β 1 0 ≈ β := by
  refine ⟨fun ⟨hβ₀, h⟩ => ?_, fun h => ?_⟩
  · refine equiv_intro (le_trans (schutte_column_gt0 β 1 f 0 hβ one_complete zero_complete hf hβ₀ zero_lt_one').le
      (sup_least fun b => sup_least fun a => ?_)) (normal_inflationary (schutte_column_normalβ f hf) β hβ)
    exact normal_fix_least (normal_col_arg hf hβ zero_complete (complete_subord hβ b)) _ _ hβ
      (lim_zero_le' _) (h _ _ (complete_subord hβ b) zero_complete (index_lt β b) (index_lt 1 a)).le
  · refine ⟨lt_of_lt_of_le (schutte_column_nonzero f β 1 0 hf) h.le, fun b a hb ha hbβ ha1 => ?_⟩
    have hN := schutte_column_normal β a f hβ ha hf
    exact equiv_intro (le_trans (schutte_column_monotone _ b _ 0 _ 0 hN.monotone h.ge (le_refl 0))
        (le_trans (schutte_column_fixpoint β 1 0 f b a hβ one_complete hf hbβ ha1 hb ha zero_complete) h.le))
      (schutte_column_inflationary1 b β 0 _ (normal_inflationary hN) hβ zero_complete)

/-- Rocq: `SchutteColumnFacts.schutte_column_enumerates`. -/
theorem schutte_column_enumerates (f : Ordinal.{u} → Ordinal.{u}) (β α : Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) (hα : Complete α) (hβ₀ : 0 < β) (hα₀ : 0 < α) :
    Con.Enumerates (schutteColumn f β α) (SchutteCritical f β α) where
  included x hx := fun b a hb ha hbβ haα =>
    equiv_intro (schutte_column_fixpoint β α x f b a hβ hα hf hbβ haα hb ha hx)
      (schutte_column_inflationary1 b _ 0 _ (normal_inflationary (schutte_column_normal β a f hβ ha hf))
        ((schutte_column_normal β α f hβ hα hf).complete x hx) zero_complete)
  monotone x y h := schutte_column_monotone f β α x α y hf.monotone (le_refl α) h
  increasing x y hy h := schutte_column_increasing β α y x f hf hβ hα hy h
  least := by
    intro x z hx hz hfix hlt
    obtain ⟨b, _⟩ := lt_elim hβ₀
    have hfixba : ∀ a : α, schutteColumn (schutteColumn f β (α a)) (β b) z 0 ≈ z := fun a =>
      hfix _ _ (complete_subord hβ b) (complete_subord hα a) (index_lt β b) (index_lt α a)
    rw [schutte_column_unroll]
    refine lub_least ?_ (sup_least fun b' => sup_least fun a => ?_)
    · obtain ⟨a, _⟩ := lt_elim hα₀
      have hz₀ : 0 < z := lt_of_lt_of_le (schutte_column_nonzero _ _ _ 0
        (schutte_column_normal β _ f hβ (complete_subord hα a) hf)) (hfixba a).le
      have hαz : α ≤ z := le_intro fun a' => by
        have hN := schutte_column_normal β (α a') f hβ (complete_subord hα a') hf
        refine lt_of_le_of_lt (schutte_column_inflationary1 β (α a') 0 f (normal_inflationary hf)
          (complete_subord hα a') zero_complete) (lt_of_lt_of_le (hN.increasing 0 z hz hz₀) ?_)
        exact le_trans (hN.monotone _ _ (add_zero z).ge) (le_trans (schutte_column_le_f (β b) z 0 _ hN.monotone)
          (hfixba a').le)
      have hxz : α + x ≤ z := by
        rw [add_unfold]
        exact lub_least hαz (sup_least fun i => succ_least (lt_of_le_of_lt
          (le_trans (normal_inflationary hf _ (add_complete hα (complete_subord hx i)))
            (schutte_column_le_f β α (x i) f hf.monotone)) (hlt _ (index_lt x i))))
      have hN := schutte_column_normal β (α a) f hβ (complete_subord hα a) hf
      refine le_trans (hf.monotone _ _ (le_trans hxz (le_trans (add_zero z).ge (le_add_left (α a) _)))) ?_
      exact le_trans (schutte_column_le_f β (α a) _ f hf.monotone)
        (le_trans (schutte_column_le_f (β b) z 0 _ hN.monotone) (hfixba a).le)
    · exact normal_fix_least (normal_col_arg hf hβ (complete_subord hα a) (complete_subord hβ b')) _ _ hz
        (limit_least fun i => hlt _ (index_lt x i))
        (hfix _ _ (complete_subord hβ b') (complete_subord hα a) (index_lt β b') (index_lt α a)).le

/-- Rocq: `SchutteColumnFacts.enum_supercritical`. -/
theorem enum_supercritical (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) (hβ₀ : 0 < β) :
    Con.Enumerates (enumFixpoints fun α => schutteColumn f β α 0) (SchutteSupercritical f β) :=
  have hN := schutte_column_normal_arg β f hβ hf
  have hE := enum_fixpoints_normal hN
  { included := fun x hx => (schutte_supercritical_alt f β _ hf hβ (hE.complete x hx) hβ₀).2
      (equiv_symm (Con.enum_are_fixpoints hN x hx))
    monotone := hE.monotone
    increasing := hE.increasing
    least := fun x z _ hz hP hlt =>
      enum_least hN x z hz ((schutte_supercritical_alt f β z hf hβ hz hβ₀).1 hP).le hlt }

/-- Rocq: `SchutteColumnFacts.enum_hypercritical`. -/
theorem enum_hypercritical (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    Con.Enumerates (eNumber f) (SchutteHypercritical f) :=
  have hN := schutte_column_normalβ f hf
  have hE := enum_fixpoints_normal hN
  { included := fun x hx => (schutte_hypercritical_alt f _ hf (hE.complete x hx)).2
      (equiv_symm (Con.enum_are_fixpoints hN x hx))
    monotone := hE.monotone
    increasing := hE.increasing
    least := fun x z _ hz hP hlt => enum_least hN x z hz ((schutte_hypercritical_alt f z hf hz).1 hP).le hlt }

/-- Rocq: `SchutteColumnFacts.schutte_column_unreachable`. -/
theorem schutte_column_unreachable (f : Ordinal.{u} → Ordinal.{u}) (b a x β α y : Ordinal.{u})
    (hf : NormalFunction f) (hb : Complete b) (ha : Complete a) (hβ : Complete β) (hα : Complete α)
    (hy : Complete y) (h1β : 1 < β) (hα₀ : 0 < α) (hbβ : b < β) (haY : a < schutteColumn f β α y)
    (hxY : x < schutteColumn f β α y) : schutteColumn f b a x < schutteColumn f β α y := by
  have hβ₀ : 0 < β := lt_trans zero_lt_one' h1β
  have hY := (schutte_column_normal β α f hβ hα hf).complete y hy
  match complete_zeroDec hb with
  | .inl hb₀ =>
    refine lt_of_le_of_lt (b := f (a + x)) ?_ ?_
    · rw [schutte_column_unroll]
      exact lub_least (le_refl _) (sup_least fun b' => (zero_lt _ (lt_of_lt_of_le (index_lt b b') hb₀)).elim)
    · refine lt_of_lt_of_le ?_ (le_trans (schutte_column_arg0 β _ f hf.monotone).ge
        (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint β α y f 0 0 hβ hα hf hβ₀ hα₀
          zero_complete zero_complete hy)))
      exact hf.increasing _ _ (add_complete hY zero_complete) (lt_of_lt_of_le
        (schutte_column_add_closed f β α y a x hf hβ hα hy h1β hα₀ haY hxY) (add_zero _).ge)
  | .inr hb₀ =>
    have hW := (schutte_column_normal b _ f hb hY hf).complete 0 zero_complete
    have hNa := schutte_column_normal b a f hb ha hf
    refine lt_of_lt_of_le ?_ (le_trans (schutte_column_monotone_func f _ b _ 0 _ 0 hf.monotone
      (fun _ _ h => schutte_column_monotone f β 0 _ 0 _ hf.monotone (le_refl 0) h)
      (fun z => (schutte_column_arg0 β z f hf.monotone).ge) (le_refl _) (le_refl 0))
      (schutte_column_fixpoint β α y f b 0 hβ hα hf hbβ hα₀ hb zero_complete hy))
    refine lt_of_lt_of_le ?_ (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint b _ 0 f 0 a hb hY hf
      hb₀ haY zero_complete ha zero_complete))
    exact hNa.increasing _ _ (add_complete hW zero_complete) (lt_of_lt_of_le hxY
      (le_trans (schutte_column_inflationary1 b _ 0 f (normal_inflationary hf) hY zero_complete) (add_zero _).ge))

/-- Rocq: `SchutteColumnFacts.schutte_column_unreachable_apex`. -/
theorem schutte_column_unreachable_apex (f : Ordinal.{u} → Ordinal.{u}) (β α x b : Ordinal.{u})
    (hf : NormalFunction f) (hb : Complete b) (hα : Complete α) (hβ : Complete β) (h1β : 1 < β) (hbβ : b < β)
    (hα' : α < schutteColumn f β 1 0) (hx' : x < schutteColumn f β 1 0) :
    schutteColumn f b α x < schutteColumn f β 1 0 :=
  schutte_column_unreachable f b α x β 1 0 hf hb hα hβ one_complete zero_complete h1β zero_lt_one' hbβ hα' hx'

/-- Rocq: `SchutteColumnFacts.schutte_column_fix_unreachable`. -/
theorem schutte_column_fix_unreachable (E : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u})
    (hf : NormalFunction f) (hE : Complete E) (hβ : Complete β) (hα : Complete α)
    (hfix : schutteColumn f E 1 0 ≤ E) (hβE : β < E) (hαE : α < E) (hxE : x < E) :
    schutteColumn f β α x < E := by
  have hN := schutte_column_normalβ f hf
  have hE₀ : 0 < E := lt_of_lt_of_le (schutte_column_nonzero f E 1 0 hf) hfix
  have h1E : 1 < E := lt_of_lt_of_le (lt_of_le_of_lt (add_zero 1).ge (add_lt_add_left 1 hE₀))
    (le_trans (onePlus_least_normal hN E hE) hfix)
  exact lt_of_lt_of_le (schutte_column_unreachable_apex f E α x β hf hβ hα hE h1E hβE
    (lt_of_lt_of_le hαE (normal_inflationary hN E hE)) (lt_of_lt_of_le hxE (normal_inflationary hN E hE))) hfix

/-- Rocq: `SchutteColumnFacts.unreachable_E_number`. -/
theorem unreachable_E_number (E : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hE : Complete E)
    (hf : NormalFunction f) (h : SchutteUnreachable f E) : schutteColumn f E 1 0 ≤ E := by
  obtain ⟨hE₀, H⟩ := h
  have h1E : 1 < E := lt_of_le_of_lt (succ_least (schutte_column_nonzero f 0 0 0 hf))
    (H 0 0 0 zero_complete zero_complete zero_complete hE₀ hE₀ hE₀)
  rw [schutte_column_unroll]
  refine lub_least (le_of_lt (lt_of_le_of_lt (schutte_column_le_f 0 1 0 f hf.monotone)
    (H 0 1 0 zero_complete one_complete zero_complete hE₀ h1E hE₀))) (sup_least fun b => sup_least fun _ => ?_)
  have hEb := complete_subord hE b
  have hNb := schutte_column_normal_arg (E b) f hEb hf
  refine normal_fix_least (normal_col_arg hf hE zero_complete hEb) _ _ hE (lim_zero_le' _) ?_
  refine le_trans (schutte_column_monotone_func _ f (E b) E 0 E 0
    (fun _ _ h => schutte_column_monotone f E 0 _ 0 _ hf.monotone (le_refl 0) h) hf.monotone
    (fun z => (schutte_column_arg0 E z f hf.monotone).le) (le_refl E) (le_refl 0)) ?_
  refine le_trans (normal_ord_decompose E (fun x => schutteColumn f (E b) x 0) hE hE₀ hNb).le
    (sup_least fun i => le_of_lt ?_)
  have hEi := complete_subord hE i
  refine H _ _ 0 hEb (succ_complete hEi) zero_complete (index_lt E b) ?_ hE₀
  refine lt_of_le_of_lt (succ_le_add_one _) (lt_of_le_of_lt ?_ (H 1 (E i) 1 one_complete hEi one_complete h1E
    (index_lt E i) h1E))
  exact le_trans (normal_inflationary hf _ (add_complete hEi one_complete)) (schutte_column_le_f 1 (E i) 1 f hf.monotone)

/-- Rocq: `SchutteColumnFacts.E_number_iff_unreachable`. -/
theorem E_number_iff_unreachable (E : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hE : Complete E) : schutteColumn f E 1 0 ≈ E ↔ SchutteUnreachable f E :=
  ⟨fun h => ⟨lt_of_lt_of_le (schutte_column_nonzero f E 1 0 hf) h.le,
      fun _ _ _ hβ hα _ h₁ h₂ h₃ => schutte_column_fix_unreachable E f _ _ _ hf hE hβ hα h.le h₁ h₂ h₃⟩,
    fun h => equiv_intro (unreachable_E_number E f hE hf h) (normal_inflationary (schutte_column_normalβ f hf) E hE)⟩

/-- Rocq: `SchutteColumnFacts.hypercritical_iff_unreachable`. -/
theorem hypercritical_iff_unreachable (E : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hE : Complete E) : SchutteHypercritical f E ↔ SchutteUnreachable f E :=
  (schutte_hypercritical_alt f E hf hE).trans (E_number_iff_unreachable E f hf hE)

/-- Rocq: `SchutteColumnFacts.E_number_enumerates_unreachable`. -/
theorem E_number_enumerates_unreachable (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    Con.Enumerates (eNumber f) (SchutteUnreachable f) :=
  Con.enumerates_equiv_pred (E_number_normal f hf) (fun x hx => hypercritical_iff_unreachable x f hf hx)
    (enum_hypercritical f hf)

/-- Rocq: `SchutteColumnFacts.schutte_column_omega_sup`. -/
theorem schutte_column_omega_sup (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    schutteColumn f ω 1 0 ≈ sup fun i : (ω : Ordinal.{u}).Carrier => schutteColumn f (ω i) 1 0 := by
  refine equiv_intro (le_trans (schutte_column_gt0 ω 1 f 0 omega_complete one_complete zero_complete hf
    omega_gt0 zero_lt_one').le (sup_least fun i => sup_least fun _ => ?_))
    (sup_least fun i => schutte_column_monotoneβ _ _ 1 0 f hf.monotone (le_of_lt (index_lt ω i)))
  refine le_trans ?_ (sup_le (fun i : (ω : Ordinal.{u}).Carrier => schutteColumn f (ω i) 1 0) ⟨i.down + 1⟩)
  have hY := (schutte_column_normal (ofNat (i.down + 1)) 1 f (ofNat_complete _) one_complete hf).complete 0
    zero_complete
  have hm : ∀ β : Ordinal.{u}, ∀ p q, p ≤ q → schutteColumn f β 0 p ≤ schutteColumn f β 0 q :=
    fun β _ _ h => schutte_column_monotone f β 0 _ 0 _ hf.monotone (le_refl 0) h
  refine normal_fix_least (normal_col_arg hf omega_complete zero_complete (ofNat_complete i.down)) _ _ hY
    (lim_zero_le' _) ?_
  refine le_trans (schutte_column_monotone_full _ (schutteColumn f (ofNat (i.down + 1)) 0) _ _ 0 _ _ 0 (hm _) (hm _)
    (fun z => le_trans (schutte_column_arg0 _ z f hf.monotone).le
      (schutte_column_arg0 (ofNat (i.down + 1)) z f hf.monotone).ge)
    (le_refl _) (le_refl _) (le_refl 0)) ?_
  exact schutte_column_fixpoint (ofNat (i.down + 1)) 1 0 f (ofNat i.down) 0 (ofNat_complete _) one_complete hf
    (succ_lt _) zero_lt_one' (ofNat_complete _) zero_complete zero_complete

/-- Rocq: `SchutteColumnFacts.fixpoint_schutte_unreachable`. -/
theorem fixpoint_schutte_unreachable (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) (hf : NormalFunction f)
    (hx : Complete x) : SchutteUnreachable f (fixOrd (fun β => schutteColumn f β 1 0) x) := by
  have hN := schutte_column_normalβ f hf
  have hΦ : Complete (fixOrd (fun β => schutteColumn f β 1 0) x) :=
    normal_fix_complete x hx (normal_inflationary hN) hN.monotone hN.complete
  exact ⟨lt_of_lt_of_le (schutte_column_nonzero f _ 1 0 hf) (normal_fixpoint hN x hx).ge,
    fun _ _ _ hβ hα _ h₁ h₂ h₃ => schutte_column_fix_unreachable _ f _ _ _ hf hΦ hβ hα
      (normal_prefixpoint hN x hx) h₁ h₂ h₃⟩

/-- Rocq: `SchutteColumnFacts.fixpoint_schutte_least_unreachable`. -/
theorem fixpoint_schutte_least_unreachable (f : Ordinal.{u} → Ordinal.{u}) (E : Ordinal.{u})
    (hf : NormalFunction f) (hE : Complete E) (h : SchutteUnreachable f E) :
    fixOrd (fun β => schutteColumn f β 1 0) 0 ≤ E :=
  normal_fix_least (schutte_column_normalβ f hf) 0 E hE (zero_least E) (unreachable_E_number E f hE hf h)

/-- The small Veblen ordinal. Rocq: `SchutteColumnFacts.SmallVeblenOrdinal`. -/
def SmallVeblenOrdinal : Ordinal.{u} := schutteColumn powOmega ω 1 0

/-- The large Veblen ordinal. Rocq: `SchutteColumnFacts.LargeVeblenOrdinal`. -/
def LargeVeblenOrdinal : Ordinal.{u} := fixOrd (fun β => schutteColumn powOmega β 1 0) 0

/-- Rocq: `SchutteColumnFacts.SVO_nonzero`. -/
theorem SVO_nonzero : (0 : Ordinal.{u}) < SmallVeblenOrdinal :=
  schutte_column_nonzero _ _ _ _ powOmega_normal

/-- Rocq: `SchutteColumnFacts.SVO_complete`. -/
theorem SVO_complete : Complete (SmallVeblenOrdinal.{u}) :=
  (schutte_column_normal ω 1 powOmega omega_complete one_complete powOmega_normal).complete 0 zero_complete

/-- Rocq: `SchutteColumnFacts.SVO_sup`. -/
theorem SVO_sup : SmallVeblenOrdinal.{u} ≈ sup fun i : (ω : Ordinal.{u}).Carrier => schutteColumn powOmega (ω i) 1 0 :=
  schutte_column_omega_sup powOmega powOmega_normal

/-- Rocq: `SchutteColumnFacts.SVO_finite_unreachable`. -/
theorem SVO_finite_unreachable (i : Nat) (α x : Ordinal.{u}) (hα : Complete α) (_hx : Complete x)
    (hαS : α < SmallVeblenOrdinal) (hxS : x < SmallVeblenOrdinal) :
    schutteColumn powOmega (ofNat i) α x < SmallVeblenOrdinal :=
  schutte_column_unreachable_apex powOmega ω α x (ofNat i) powOmega_normal (ofNat_complete i) hα omega_complete
    omega_gt1 (index_lt ω ⟨i⟩) hαS hxS

/-- Rocq: `SchutteColumnFacts.SVO_least_finite_unreachable`. -/
theorem SVO_least_finite_unreachable (X : Ordinal.{u}) (_hX : Complete X) (hX₀ : 0 < X)
    (h : ∀ (i : Nat) (α x : Ordinal.{u}), Complete α → Complete x → α < X → x < X →
      schutteColumn powOmega (ofNat i) α x < X) : SmallVeblenOrdinal ≤ X := by
  have h1X : 1 < X := lt_of_le_of_lt (succ_least (schutte_column_nonzero powOmega (ofNat 0) 0 0 powOmega_normal))
    (h 0 0 0 zero_complete zero_complete hX₀ hX₀)
  exact le_trans SVO_sup.le (sup_least fun i => le_of_lt (h i.down 1 0 one_complete zero_complete h1X hX₀))

/-- Rocq: `SchutteColumnFacts.LVO_nonzero`. -/
theorem LVO_nonzero : (0 : Ordinal.{u}) < LargeVeblenOrdinal :=
  lt_of_lt_of_le (schutte_column_nonzero powOmega 0 1 0 powOmega_normal)
    (sup_le (fun n : ULift Nat => iterF (fun β => schutteColumn powOmega β 1 0) 0 n.down) ⟨1⟩)

/-- Rocq: `SchutteColumnFacts.LVO_complete`. -/
theorem LVO_complete : Complete (LargeVeblenOrdinal.{u}) :=
  have hN := schutte_column_normalβ powOmega powOmega_normal
  normal_fix_complete 0 zero_complete (normal_inflationary hN) hN.monotone hN.complete

/-- Rocq: `SchutteColumnFacts.LVO_unreachable`. -/
theorem LVO_unreachable : SchutteUnreachable powOmega (LargeVeblenOrdinal.{u}) :=
  fixpoint_schutte_unreachable powOmega 0 powOmega_normal zero_complete

/-- Rocq: `SchutteColumnFacts.LVO_least_unreachable`. -/
theorem LVO_least_unreachable (E : Ordinal.{u}) (hE : Complete E) (h : SchutteUnreachable powOmega E) :
    LargeVeblenOrdinal ≤ E :=
  fixpoint_schutte_least_unreachable powOmega E powOmega_normal hE h

private theorem two_complete : Complete (2 : Ordinal.{u}) := ofNat_complete 2

private theorem one_lt_two : (1 : Ordinal.{u}) < 2 := succ_lt 1

private theorem zero_lt_two : (0 : Ordinal.{u}) < 2 := lt_trans zero_lt_one' one_lt_two

/-- Rocq: `SchutteColumnFacts.schutte_column_2_ackermann_tower`. -/
theorem schutte_column_2_ackermann_tower (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ∀ x, NormalFunction f → Complete a → Complete x → schutteColumn f 2 a x ≈ ackermannTower f a x := by
  induction a using ltRec with
  | ind a iha =>
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro hf ha hx
  have hA := ackermann_tower_normal f a hf ha
  have hS := schutte_column_normal 2 a f two_complete ha hf
  refine equiv_intro ?_ ?_
  · rw [schutte_column_unroll]
    refine lub_least (ackermann_tower_fax f a x hf ha hx) (sup_least fun _ => sup_least fun a' => ?_)
    have ha' := complete_subord ha a'
    have hZ := hA.complete x hx
    refine normal_fix_least (normal_col_arg hf two_complete ha' one_complete) _ _ hZ
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) hf ha (complete_subord hx i)).le
        (hA.increasing _ _ hx (index_lt x i))) ?_
    refine le_trans (schutte_column_veblen _ 0 _ (schutte_column_normal 2 _ f two_complete ha' hf) hZ
      zero_complete).le ?_
    exact le_trans (veblen_monotone_func (schutte_column_normal 2 _ f two_complete ha' hf)
        (ackermann_tower_normal f _ hf ha') (fun z hz => (iha (a a') (index_lt a a') z hf ha' hz).le) _ 0 hZ
        zero_complete)
      (ackermann_tower_fixpoint f a (a a') x hf ha ha' hx (index_lt a a'))
  · rw [ackermann_tower_unroll]
    refine lub_least (le_trans (hf.monotone _ _ (le_add_left a x)) (schutte_column_le_f 2 a x f hf.monotone))
      (sup_least fun a' => ?_)
    have ha' := complete_subord ha a'
    have hY := hS.complete x hx
    refine normal_fix_least (veblen_first_normal (ackermann_tower_normal f _ hf ha')) _ _ hY
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) hf ha (complete_subord hx i)).ge
        (hS.increasing _ _ hx (index_lt x i))) ?_
    refine le_trans (veblen_monotone_func (ackermann_tower_normal f _ hf ha')
      (schutte_column_normal 2 _ f two_complete ha' hf) (fun z hz => (iha (a a') (index_lt a a') z hf ha' hz).ge)
      _ 0 hY zero_complete) ?_
    exact le_trans (schutte_column_veblen _ 0 _ (schutte_column_normal 2 _ f two_complete ha' hf) hY
      zero_complete).ge
      (schutte_column_fixpoint 2 a x f 1 (a a') two_complete ha hf one_lt_two (index_lt a a') one_complete ha' hx)

/-- Rocq: `SchutteColumnFacts.schutte_column_2_succ`. -/
theorem schutte_column_2_succ (f : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (hf : NormalFunction f)
    (ha : Complete a) (hx : Complete x) :
    schutteColumn f 2 (succ a) x ≈ enumFixpoints (fun i => veblen (schutteColumn f 2 a) i 0) x := by
  have hN := schutte_column_normal 2 a f two_complete ha hf
  have hF := veblen_first_normal hN
  have hE := enum_fixpoints_normal hF
  have hsa := succ_complete ha
  have hS := schutte_column_normal 2 (succ a) f two_complete hsa hf
  induction x using ltRec with
  | ind x ihx =>
  have hEc := hE.complete x hx
  refine equiv_intro (le_trans (schutte_column_gt0 2 (succ a) f x two_complete hsa hx hf zero_lt_two
    (succ_trans (zero_least a))).le (sup_least fun _ => sup_least fun _ => ?_)) ?_
  · refine normal_fix_least (normal_col_arg hf two_complete ha one_complete) _ _ hEc
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) (complete_subord hx i)).le
        (hE.increasing _ _ hx (index_lt x i))) ?_
    exact le_trans (schutte_column_veblen _ 0 _ hN hEc zero_complete).le (Con.enum_are_fixpoints hF x hx).ge
  · have hY := hS.complete x hx
    exact enum_least' hF x _ hx hY
      (le_trans (schutte_column_veblen _ 0 _ hN hY zero_complete).ge
        (schutte_column_fixpoint 2 (succ a) x f 1 a two_complete hsa hf one_lt_two (succ_lt a) one_complete ha hx))
      fun x' hx' h => lt_of_le_of_lt (ihx x' h hx').ge (hS.increasing _ _ hx h)

/-- `veblen (schutteColumn (1 + ·) 2 0) i 0 ≈ ω ^ i`. -/
private theorem veblen_col2_zero (i : Ordinal.{u}) (hi : Complete i) :
    veblen (schutteColumn (fun y => 1 + y) 2 0) i 0 ≈ ω ^ i := by
  have hN0 := schutte_column_normal 2 0 _ two_complete zero_complete onePlus_normal
  exact equiv_intro
    (le_trans (veblen_monotone_func hN0 onePlus_normal
      (fun z _ => (schutte_column_arg0 2 z _ onePlus_normal.monotone).le) i 0 hi zero_complete)
      (le_trans (veblen_onePlus i hi 0 zero_complete).le (add_zero _).le))
    (le_trans (add_zero _).ge (le_trans (veblen_onePlus i hi 0 zero_complete).ge
      (veblen_monotone_func onePlus_normal hN0
        (fun z _ => (schutte_column_arg0 2 z _ onePlus_normal.monotone).ge) i 0 hi zero_complete)))

/-- Rocq: `SchutteColumnFacts.schutte_column_2_1`. -/
theorem schutte_column_2_1 (x : Ordinal.{u}) (hx : Complete x) : schutteColumn (fun y => 1 + y) 2 1 x ≈ ε x := by
  have hN0 := schutte_column_normal 2 0 _ two_complete zero_complete onePlus_normal
  have hF := veblen_first_normal hN0
  refine equiv_trans (schutte_column_2_succ _ 0 x onePlus_normal zero_complete hx) (equiv_intro ?_ ?_)
  · exact enum_fixpoints_func_mono' hF powOmega_normal (fun y hy => fixOrd_monotone_func''
      (fun i hi => (veblen_col2_zero i hi).le) powOmega_normal.complete hF.monotone y hy) x hx
  · exact enum_fixpoints_func_mono' powOmega_normal hF (fun y hy => fixOrd_monotone_func''
      (fun i hi => (veblen_col2_zero i hi).ge) hF.complete powOmega_normal.monotone y hy) x hx

/-- Rocq: `SchutteColumnFacts.schutte_column_2_2`. -/
theorem schutte_column_2_2 (x : Ordinal.{u}) (hx : Complete x) : schutteColumn (fun y => 1 + y) 2 2 x ≈ Γ x := by
  have hN1 := schutte_column_normal 2 1 _ two_complete one_complete onePlus_normal
  have hF := veblen_first_normal hN1
  have hG := veblen_first_normal ε_normal
  refine equiv_trans (schutte_column_2_succ _ 1 x onePlus_normal one_complete hx)
    (equiv_trans (equiv_intro ?_ ?_) (equiv_symm (Γalt x hx)))
  · exact enum_fixpoints_func_mono' hF hG (fun y hy => fixOrd_monotone_func''
      (fun i hi => veblen_monotone_func hN1 ε_normal (fun z hz => (schutte_column_2_1 z hz).le) i 0 hi zero_complete)
      hG.complete hF.monotone y hy) x hx
  · exact enum_fixpoints_func_mono' hG hF (fun y hy => fixOrd_monotone_func''
      (fun i hi => veblen_monotone_func ε_normal hN1 (fun z hz => (schutte_column_2_1 z hz).ge) i 0 hi zero_complete)
      hF.complete hG.monotone y hy) x hx

/-- Rocq: `SchutteColumnFacts.schutte_column_succ`. -/
theorem schutte_column_succ (f : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) (hf : NormalFunction f)
    (hβ : Complete β) (hα : Complete α) (hx : Complete x) :
    schutteColumn f (succ β) α x ≈
      f x ⊔ sup fun a : α => fixOrd (fun δ => schutteColumn (schutteColumn f (succ β) (α a)) β δ 0)
        (lim fun i : x => schutteColumn f (succ β) α (x i)) := by
  refine equiv_intro ?_ ?_
  · match complete_zeroDec hα with
    | .inl hα₀ =>
      exact le_trans (schutte_column_monotone f _ α x 0 x hf.monotone hα₀ (le_refl x))
        (le_trans (schutte_column_arg0 _ x f hf.monotone).le (lub_le1 _ _))
    | .inr hα₀ =>
      exact le_trans (schutte_column_gt0 (succ β) α f x (succ_complete hβ) hα hx hf (succ_trans (zero_least β))
        hα₀).le (sup_least fun _ => lub_le2 _ _)
  · rw [schutte_column_unroll]
    exact lub_monotone (hf.monotone _ _ (le_add_left α x))
      (sup_le (fun b : (succ β).Carrier => sup fun a : α => fixOrd
        (fun δ => schutteColumn (schutteColumn f (succ β) (α a)) (succ β b) δ 0)
        (lim fun i : x => schutteColumn f (succ β) α (x i))) PUnit.unit)

/-- Rocq: `SchutteColumnFacts.schutte_column_tower_base_le`. -/
theorem schutte_column_tower_base_le (b a x : Ordinal.{u}) (hb : Complete b) (ha : Complete a) (hx : Complete x)
    (hb₂ : 1 < b) : schutteColumn powOmega b a x ≤ schutteColumn (fun y => 1 + y) b (1 + a) x := by
  induction a using ltRec generalizing x with
  | ind a iha =>
  induction x using ltRec with
  | ind x ihx =>
  have h1a := onePlus_complete ha
  have hS1 := schutte_column_normal b (1 + a) _ hb h1a onePlus_normal
  have hY := hS1.complete x hx
  rw [schutte_column_unroll powOmega b a x]
  refine lub_least ?_ (sup_least fun b' => sup_least fun a' => ?_)
  · have hN0 := schutte_column_normal b 0 _ hb zero_complete onePlus_normal
    have haxY : a + x ≤ schutteColumn (fun y => 1 + y) b (1 + a) x :=
      le_trans (le_trans (add_le_add (le_add_left 1 a) (le_refl x)) (le_add_left 1 _))
        (le_trans (ackermann_tower_fax _ (1 + a) x onePlus_normal h1a hx)
          (le_trans (schutte_column_2_ackermann_tower _ (1 + a) x onePlus_normal h1a hx).ge
            (schutte_column_monotoneβ 2 b _ x _ onePlus_normal.monotone (succ_least hb₂))))
    refine le_trans (pow_le_pow_right ω haxY) ?_
    refine le_trans (add_zero _).ge (le_trans (veblen_onePlus _ hY 0 zero_complete).ge ?_)
    refine le_trans (veblen_monotone_func onePlus_normal hN0
      (fun z _ => (schutte_column_arg0 b z _ onePlus_normal.monotone).ge) _ 0 hY zero_complete) ?_
    exact le_trans (schutte_column_veblen _ 0 _ hN0 hY zero_complete).ge
      (schutte_column_fixpoint b (1 + a) x _ 1 0 hb h1a onePlus_normal hb₂ (onePlus_nonzero a) one_complete
        zero_complete hx)
  · have ha' := complete_subord ha a'
    have hb' := complete_subord hb b'
    have h1a' := onePlus_complete ha'
    refine normal_fix_least (normal_col_arg powOmega_normal hb ha' hb') _ _ hY
      (limit_least fun i => lt_of_le_of_lt (ihx (x i) (index_lt x i) (complete_subord hx i))
        (hS1.increasing _ _ hx (index_lt x i))) ?_
    exact le_trans (schutte_column_monotone_func' (b b') _ 0 _ _ (schutte_column_normal b _ powOmega hb ha'
        powOmega_normal) (schutte_column_normal b _ _ hb h1a' onePlus_normal)
        (fun z hz => iha (a a') (index_lt a a') z ha' hz) hb' hY zero_complete)
      (schutte_column_fixpoint b (1 + a) x _ (b b') (1 + a a') hb h1a onePlus_normal (index_lt b b')
        (add_lt_add_left 1 (index_lt a a')) hb' h1a' hx)

/-- Rocq: `SchutteColumnFacts.schutte_column_tower_base_eq`. -/
theorem schutte_column_tower_base_eq (b a x : Ordinal.{u}) (hb : Complete b) (ha : Complete a) (hx : Complete x)
    (hb₂ : 1 < b) (h1a : 1 + a ≤ a) : schutteColumn powOmega b a x ≈ schutteColumn (fun y => 1 + y) b a x :=
  equiv_intro (le_trans (schutte_column_tower_base_le b a x hb ha hx hb₂)
      (schutte_column_monotone _ b _ x a x onePlus_normal.monotone h1a (le_refl x)))
    (schutte_column_monotone_func' b a x _ _ onePlus_normal powOmega_normal
      (fun z hz => onePlus_least_normal powOmega_normal z hz) hb ha hx)

/-- `ω ^ (1 + 0) ≤ ω`. -/
private theorem pow_one_zero_le : ω ^ ((1 : Ordinal.{u}) + 0) ≤ ω :=
  le_trans (pow_le_pow_right ω (add_zero 1).le) (pow_one' omega_gt0).le

/-- Rocq: `SchutteColumnFacts.SVO_alt`. -/
theorem SVO_alt : SmallVeblenOrdinal.{u} ≈ schutteColumn (fun y => 1 + y) ω 1 0 := by
  have hT := schutte_column_normal ω 1 _ omega_complete one_complete onePlus_normal
  have hY := hT.complete 0 zero_complete
  have hN0 := schutte_column_normal ω 0 _ omega_complete zero_complete onePlus_normal
  refine equiv_intro ?_ (schutte_column_monotone_func' ω 1 0 _ _ onePlus_normal powOmega_normal
    (fun z hz => onePlus_least_normal powOmega_normal z hz) omega_complete one_complete zero_complete)
  show schutteColumn powOmega ω 1 0 ≤ _
  rw [schutte_column_unroll]
  refine lub_least (le_trans pow_one_zero_le (normal_inflationary (schutte_column_normalβ _ onePlus_normal) ω
    omega_complete)) (sup_least fun i => sup_least fun _ => ?_)
  have hi := complete_subord (omega_complete : Complete (ω : Ordinal.{u})) i
  have hi2 : Complete (ω i + 2 : Ordinal.{u}) := add_complete hi two_complete
  refine normal_fix_least (normal_col_arg powOmega_normal omega_complete zero_complete hi) _ _ hY
    (lim_zero_le' _) ?_
  have h1Y : 1 + schutteColumn (fun y => 1 + y) ω 1 0 ≤ schutteColumn (fun y => 1 + y) ω 1 0 :=
    le_trans (add_le_add (le_refl 1) (add_zero _).ge) (le_trans (schutte_column_arg0 ω _ _ onePlus_normal.monotone).ge
      (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint ω 1 0 _ 0 0 omega_complete one_complete
        onePlus_normal omega_gt0 zero_lt_one' zero_complete zero_complete zero_complete)))
  refine le_trans (schutte_column_monotone_func _ powOmega (ω i) _ 0 _ 0
    (fun _ _ h => schutte_column_monotone powOmega ω 0 _ 0 _ powOmega_normal.monotone (le_refl 0) h)
    powOmega_normal.monotone (fun z => (schutte_column_arg0 ω z _ powOmega_normal.monotone).le)
    (le_refl _) (le_refl 0)) ?_
  refine le_trans (schutte_column_monotoneβ (ω i) (ω i + 2) _ 0 _ powOmega_normal.monotone (le_add_right _ _)) ?_
  refine le_trans (schutte_column_tower_base_eq (ω i + 2) _ 0 hi2 hY zero_complete
    (lt_of_lt_of_le one_lt_two (le_add_left _ _)) h1Y).le ?_
  have hlt : (ω i + 2 : Ordinal.{u}) < ω :=
    lt_of_le_of_lt (ofNat_add 2 i.down).ge (index_lt ω ⟨2 + i.down⟩)
  exact le_trans (schutte_column_monotone_func' (ω i + 2) _ 0 _ _ onePlus_normal hN0
      (fun z hz => onePlus_least_normal hN0 z hz) hi2 hY zero_complete)
    (schutte_column_fixpoint ω 1 0 _ (ω i + 2) 0 omega_complete one_complete onePlus_normal hlt zero_lt_one'
      hi2 zero_complete zero_complete)

/-- Rocq: `SchutteColumnFacts.omega_least_fix`. -/
theorem omega_least_fix (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) (hf : NormalFunction f) (hx : Complete x) :
    ω ≤ fixOrd f x := by
  have hΦ : Complete (fixOrd f x) := normal_fix_complete x hx (normal_inflationary hf) hf.monotone hf.complete
  have hfix := normal_fixpoint hf x hx
  refine le_intro fun ⟨i⟩ => ?_
  show ofNat i < fixOrd f x
  induction i with
  | zero => exact lt_of_lt_of_le (hf.nonzero _) hfix.ge
  | succ i ih =>
    exact lt_of_le_of_lt (ofNat_add i 1).le (lt_of_lt_of_le (add_lt_add_left 1 ih)
      (le_trans (onePlus_least_normal hf _ hΦ) hfix.ge))

/-- Rocq: `SchutteColumnFacts.LVO_alt`. -/
theorem LVO_alt : LargeVeblenOrdinal.{u} ≈ fixOrd (fun x => schutteColumn (fun y => 1 + y) x 1 0) 0 := by
  have hN1 := schutte_column_normalβ _ onePlus_normal
  have hNω := schutte_column_normalβ powOmega powOmega_normal
  have hc : Complete (fixOrd (fun x => schutteColumn (fun y => 1 + y) x 1 0) (0 : Ordinal.{u})) :=
    normal_fix_complete 0 zero_complete (normal_inflationary hN1) hN1.monotone hN1.complete
  have hfix := normal_fixpoint hN1 0 zero_complete
  have h1Φ : 1 + fixOrd (fun x => schutteColumn (fun y => 1 + y) x 1 0) (0 : Ordinal.{u}) ≤
      fixOrd (fun x => schutteColumn (fun y => 1 + y) x 1 0) 0 :=
    le_trans (onePlus_least_normal hN1 _ hc) hfix.ge
  refine equiv_intro (normal_fix_least hNω 0 _ hc (zero_least _) ?_)
    (fixOrd_monotone_func'' (fun z hz => schutte_column_monotone_func' z 1 0 _ _ onePlus_normal powOmega_normal
      (fun w hw => onePlus_least_normal powOmega_normal w hw) hz one_complete zero_complete) hNω.complete
      hN1.monotone 0 zero_complete)
  show schutteColumn powOmega _ 1 0 ≤ _
  rw [schutte_column_unroll]
  refine lub_least (le_trans pow_one_zero_le (omega_least_fix _ 0 hN1 zero_complete))
    (sup_least fun b => sup_least fun _ => ?_)
  have hb := complete_subord hc b
  have hG := schutte_column_normal_arg _ powOmega hb powOmega_normal
  refine le_trans (fixOrd_monotone (normal_col_arg powOmega_normal hc zero_complete hb).monotone (lim_zero_le' 0)) ?_
  refine le_trans (fixOrd_monotone_func'' (fun z hz => schutte_column_monotone_func' _ z 0 _ _
    (schutte_column_normal _ 0 _ hc zero_complete powOmega_normal) powOmega_normal
    (fun w _ => (schutte_column_arg0 _ w _ powOmega_normal.monotone).le) hb hz zero_complete)
    hG.complete (normal_col_arg powOmega_normal hc zero_complete hb).monotone 0 zero_complete) ?_
  refine normal_fix_least hG 0 _ hc (zero_least _) ?_
  have hb₁ := lt_of_lt_of_le (add_lt_add_left 1 (index_lt _ b)) h1Φ
  have hb₂ := lt_of_lt_of_le (add_lt_add_left 1 hb₁) h1Φ
  have h11b := onePlus_complete (onePlus_complete hb)
  refine le_trans (schutte_column_monotoneβ _ _ _ 0 _ powOmega_normal.monotone
    (le_trans (le_add_left 1 _) (le_add_left 1 _))) ?_
  refine le_trans (schutte_column_tower_base_eq _ _ 0 h11b hc zero_complete
    (lt_of_le_of_lt (add_zero 1).ge (add_lt_add_left 1 (lt_of_lt_of_le zero_lt_one' (le_add_right 1 _)))) h1Φ).le ?_
  obtain ⟨b', hb'⟩ := lt_elim hb₂
  have hb'c := complete_subord hc b'
  have hN0 := schutte_column_normal _ 0 _ hc zero_complete onePlus_normal
  refine le_trans (schutte_column_monotoneβ _ _ _ 0 _ onePlus_normal.monotone hb') ?_
  refine le_trans (schutte_column_monotone _ _ _ 0 _ 0 onePlus_normal.monotone
    (normal_inflationary hN1 _ hc) (le_refl 0)) ?_
  refine le_trans (schutte_column_monotone_func' _ _ 0 _ _ onePlus_normal hN0
    (fun z hz => onePlus_least_normal hN0 z hz) hb'c (hN1.complete _ hc) zero_complete) ?_
  exact le_trans (schutte_column_fixpoint _ 1 0 _ _ 0 hc one_complete onePlus_normal (index_lt _ b') zero_lt_one'
    hb'c zero_complete zero_complete) hfix.ge

/-! ## Stacks of columns -/

/-- A stack of Schütte columns: the `i`-th entry from the end is the
`α`-argument of column `i`. Rocq: `SchutteColumnFacts.schutte_stack`. -/
def schutteStack (f : Ordinal.{u} → Ordinal.{u}) : List Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | [] => f
  | α :: xs => schutteStack (schutteColumn f (ofNat xs.length) α) xs

/-- Rocq: `SchutteColumnFacts.schutte_stack_monotone_func`. -/
theorem schutte_stack_monotone_func (xs : List Ordinal.{u}) :
    ∀ (f g : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), (∀ a b, a ≤ b → f a ≤ f b) →
      (∀ a b, a ≤ b → g a ≤ g b) → (∀ a, f a ≤ g a) → schutteStack f xs x ≤ schutteStack g xs x := by
  induction xs with
  | nil => intro f g x _ _ hfg; exact hfg x
  | cons a xs ih =>
    intro f g x hf hg hfg
    exact ih _ _ x (fun _ _ h => schutte_column_monotone f _ a _ a _ hf (le_refl a) h)
      (fun _ _ h => schutte_column_monotone g _ a _ a _ hg (le_refl a) h)
      (fun z => schutte_column_monotone_func f g _ a z a z hf hg hfg (le_refl a) (le_refl z))

/-- Rocq: `SchutteColumnFacts.list_complete`. -/
def ListComplete (xs : List Ordinal.{u}) : Prop := Each Complete xs

/-- Rocq: `SchutteColumnFacts.schutte_stack_normal`. -/
theorem schutte_stack_normal (xs : List Ordinal.{u}) :
    ∀ f : Ordinal.{u} → Ordinal.{u}, ListComplete xs → NormalFunction f → NormalFunction (schutteStack f xs) := by
  induction xs with
  | nil => intro f _ hf; exact hf
  | cons a xs ih =>
    intro f h hf
    exact ih _ h.2 (schutte_column_normal _ a f (ofNat_complete _) h.1 hf)

/-- Rocq: `SchutteColumnFacts.schutte_stack_base`. -/
theorem schutte_stack_base (xs : List Ordinal.{u}) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), NormalFunction f → ListComplete xs →
      f x ≤ schutteStack f xs x := by
  induction xs with
  | nil => intro f x _ _; exact le_refl _
  | cons a xs ih =>
    intro f x hf h
    exact le_trans (le_trans (hf.monotone _ _ (le_add_left a x)) (schutte_column_le_f _ a x f hf.monotone))
      (ih _ x (schutte_column_normal _ a f (ofNat_complete _) h.1 hf) h.2)

/-- Rocq: `SchutteColumnFacts.schutte_stack_zero_column`. -/
theorem schutte_stack_zero_column (f : Ordinal.{u} → Ordinal.{u}) (x y : Ordinal.{u}) :
    schutteStack f [x] y ≈ f (x + y) :=
  schutte_column0 f x y

/-- Rocq: `SchutteColumnFacts.schutte_stack_veblen`. -/
theorem schutte_stack_veblen (f : Ordinal.{u} → Ordinal.{u}) (α x y : Ordinal.{u}) (hf : NormalFunction f)
    (hα : Complete α) (hx : Complete x) (hy : Complete y) :
    schutteStack f [α, x] y ≈ veblen f α (x + y) :=
  equiv_trans (schutte_column0 (schutteColumn f 1 α) x y)
    (schutte_column_veblen α (x + y) f hf hα (add_complete hx hy))

/-- Rocq: `SchutteColumnFacts.schutte_stack_leading_zero`. -/
theorem schutte_stack_leading_zero (f : Ordinal.{u} → Ordinal.{u}) (xs : List Ordinal.{u}) (y : Ordinal.{u})
    (hf : NormalFunction f) : schutteStack f (0 :: xs) y ≈ schutteStack f xs y :=
  have hm := fun _ _ h => schutte_column_monotone f (ofNat xs.length) 0 _ 0 _ hf.monotone (le_refl 0) h
  equiv_intro
    (schutte_stack_monotone_func xs _ f y hm hf.monotone (fun z => (schutte_column_arg0 _ z f hf.monotone).le))
    (schutte_stack_monotone_func xs f _ y hf.monotone hm (fun z => (schutte_column_arg0 _ z f hf.monotone).ge))

/-- Every entry of the stack is below `α`. Rocq: `SchutteColumnFacts.schutte_stack_proper`. -/
def SchutteStackProper (xs : List Ordinal.{u}) (α : Ordinal.{u}) : Prop := Each (· < α) xs

/-- Rocq: `SchutteColumnFacts.schutte_stack_proper_monotone`. -/
theorem schutte_stack_proper_monotone (xs : List Ordinal.{u}) (α α' : Ordinal.{u}) (h : α ≤ α')
    (hp : SchutteStackProper xs α) : SchutteStackProper xs α' :=
  Each.imp (fun _ hx => lt_of_lt_of_le hx h) hp

/-- Rocq: `SchutteColumnFacts.schutte_stack_zeros`. -/
theorem schutte_stack_zeros (i : Nat) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), (∀ a b, a ≤ b → f a ≤ f b) →
      schutteStack f (List.replicate i 0) x ≈ f x := by
  induction i with
  | zero => intro f x _; exact equiv_refl _
  | succ i ih =>
    intro f x hf
    exact equiv_trans (ih _ x fun _ _ h => schutte_column_monotone f _ 0 _ 0 _ hf (le_refl 0) h)
      (schutte_column_arg0 _ x f hf)

private theorem length_replicate {α : Type u} (a : α) : ∀ i : Nat, (List.replicate i a).length = i
  | 0 => rfl
  | i + 1 => congrArg (· + 1) (length_replicate a i)

private theorem each_replicate {α : Type u} {P : α → Prop} {a : α} (h : P a) : ∀ i : Nat, Each P (List.replicate i a)
  | 0 => trivial
  | i + 1 => ⟨h, each_replicate h i⟩

/-- Rocq: `SchutteColumnFacts.schutte_column_to_stack`. -/
theorem schutte_column_to_stack (f : Ordinal.{u} → Ordinal.{u}) (i : Nat) (a x : Ordinal.{u})
    (hf : ∀ a b, a ≤ b → f a ≤ f b) :
    schutteColumn f (ofNat i) a x ≈ schutteStack f (a :: List.replicate i 0) x := by
  show _ ≈ schutteStack (schutteColumn f (ofNat (List.replicate i (0 : Ordinal.{u})).length) a) _ x
  rw [length_replicate]
  exact equiv_symm (schutte_stack_zeros i _ x fun _ _ h => schutte_column_monotone f _ a _ a _ hf (le_refl a) h)

/-- Rocq: `SchutteColumnFacts.list_complete_cons`. -/
theorem list_complete_cons (x : Ordinal.{u}) (xs : List Ordinal.{u}) (hx : Complete x) (hxs : ListComplete xs) :
    ListComplete (x :: xs) :=
  ⟨hx, hxs⟩

/-- Rocq: `SchutteColumnFacts.proper_stack_unreachable`. -/
theorem proper_stack_unreachable (xs : List Ordinal.{u}) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (a δ x : Ordinal.{u}), NormalFunction f → Complete a → Complete x →
      Complete δ → ListComplete xs → SchutteStackProper xs δ → x < δ →
      schutteStack f xs x < schutteColumn f (ofNat xs.length) δ 0 := by
  induction xs with
  | nil =>
    intro f _ δ x hf _ _ hδ _ _ hxδ
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hδ zero_complete) (lt_of_lt_of_le hxδ (add_zero δ).ge))
      (schutte_column0 f δ 0).ge
  | cons b xs ih =>
    intro f a δ x hf ha hx hδ hxs hp hxδ
    have hn := ofNat_complete.{u} xs.length
    have hsn := ofNat_complete.{u} (xs.length + 1)
    have hNb := schutte_column_normal _ b f hsn hxs.1 hf
    have hN := schutte_column_normal _ b f hn hxs.1 hf
    refine lt_of_lt_of_le (ih _ a δ x hN ha hx hδ hxs.2 hp.2 hxδ) ?_
    refine le_trans (schutte_column_monotone_full _ _ _ δ 0 _ _ 0 hN.monotone hNb.monotone
      (fun z => schutte_column_monotoneβ _ _ b z f hf.monotone (le_of_lt (succ_lt _))) (le_refl _)
      (schutte_column_inflationary1 (ofNat (xs.length + 1)) δ 0 f (normal_inflationary hf) hδ zero_complete)
      (le_refl 0)) ?_
    exact schutte_column_fixpoint (ofNat (xs.length + 1)) δ 0 f (ofNat xs.length) b hsn hδ hf (succ_lt _) hp.1 hn
      hxs.1 zero_complete

/-- Rocq: `SchutteColumnFacts.proper_stack_apex_unreachable`. -/
theorem proper_stack_apex_unreachable (xs : List Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (β x : Ordinal.{u})
    (hf : NormalFunction f) (hβ : Complete β) (hx : Complete x) (hxs : ListComplete xs)
    (hlen : ofNat xs.length < β) (hp : SchutteStackProper xs (schutteColumn f β 1 0))
    (hxT : x < schutteColumn f β 1 0) : schutteStack f xs x < schutteColumn f β 1 0 := by
  have hT := (schutte_column_normal β 1 f hβ one_complete hf).complete 0 zero_complete
  have hβ₀ : 0 < β := lt_of_le_of_lt (zero_least _) hlen
  match xs, hxs, hlen, hp with
  | [], _, _, _ =>
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hT zero_complete) (lt_of_lt_of_le hxT (add_zero _).ge))
      (le_trans (schutte_column_arg0 β _ f hf.monotone).ge (le_trans (schutte_column0 _ _ 0).ge
        (schutte_column_fixpoint β 1 0 f 0 0 hβ one_complete hf hβ₀ zero_lt_one' zero_complete zero_complete
          zero_complete)))
  | o :: xs, hxs, hlen, hp =>
    refine lt_of_lt_of_le (proper_stack_unreachable (o :: xs) f o _ x hf hxs.1 hx hT hxs hp hxT) ?_
    exact le_trans (schutte_column_monotone_func f _ _ _ 0 _ 0 hf.monotone
        (fun _ _ h => schutte_column_monotone f β 0 _ 0 _ hf.monotone (le_refl 0) h)
        (fun z => (schutte_column_arg0 β z f hf.monotone).ge) (le_refl _) (le_refl 0))
      (schutte_column_fixpoint β 1 0 f _ 0 hβ one_complete hf hlen zero_lt_one' (ofNat_complete _) zero_complete
        zero_complete)

/-- Rocq: `SchutteColumnFacts.schutte_stack_unreachable`. -/
theorem schutte_stack_unreachable (f : Ordinal.{u} → Ordinal.{u}) (xs : List Ordinal.{u}) (x : Ordinal.{u})
    (hf : NormalFunction f) (hxs : ListComplete xs) (hx : Complete x) (hxT : x < schutteColumn f ω 1 0)
    (hp : SchutteStackProper xs (schutteColumn f ω 1 0)) : schutteStack f xs x < schutteColumn f ω 1 0 :=
  proper_stack_apex_unreachable xs f ω x hf omega_complete hx hxs (index_lt ω ⟨xs.length⟩) hp hxT

/-- Rocq: `SchutteColumnFacts.schutte_stack_least_unreachable`. -/
theorem schutte_stack_least_unreachable (f : Ordinal.{u} → Ordinal.{u}) (X : Ordinal.{u}) (hf : NormalFunction f)
    (_hX : Complete X) (hX₀ : 0 < X)
    (h : ∀ xs x, ListComplete xs → Complete x → x < X → SchutteStackProper xs X → schutteStack f xs x < X) :
    schutteColumn f ω 1 0 ≤ X := by
  have h1X : 1 < X := lt_of_le_of_lt (succ_least (hf.nonzero 0)) (h [] 0 trivial zero_complete hX₀ trivial)
  refine le_trans (schutte_column_omega_sup f hf).le (sup_least fun i => le_of_lt ?_)
  refine lt_of_le_of_lt (schutte_column_to_stack f i.down 1 0 hf.monotone).le ?_
  exact h _ 0 ⟨one_complete, each_replicate zero_complete i.down⟩ zero_complete hX₀
    ⟨h1X, each_replicate (P := (· < X)) hX₀ i.down⟩

/-- Rocq: `SchutteColumnFacts.SVO_stack_unreachable`. -/
theorem SVO_stack_unreachable (xs : List Ordinal.{u}) (x : Ordinal.{u}) (hxs : ListComplete xs) (hx : Complete x)
    (hxS : x < SmallVeblenOrdinal) (hp : SchutteStackProper xs SmallVeblenOrdinal) :
    schutteStack powOmega xs x < SmallVeblenOrdinal :=
  schutte_stack_unreachable powOmega xs x powOmega_normal hxs hx hxS hp

/-- Rocq: `SchutteColumnFacts.SVO_stack_unreachable'`. -/
theorem SVO_stack_unreachable' (xs : List Ordinal.{u}) (x : Ordinal.{u}) (hxs : ListComplete xs) (hx : Complete x)
    (hxS : x < SmallVeblenOrdinal) (hp : SchutteStackProper xs SmallVeblenOrdinal) :
    schutteStack (fun y => 1 + y) xs x < SmallVeblenOrdinal :=
  lt_of_lt_of_le (schutte_stack_unreachable _ xs x onePlus_normal hxs hx (lt_of_lt_of_le hxS SVO_alt.le)
    (schutte_stack_proper_monotone xs _ _ SVO_alt.le hp)) SVO_alt.ge

/-- Rocq: `SchutteColumnFacts.SVO_least_stack_unreachable`. -/
theorem SVO_least_stack_unreachable (X : Ordinal.{u}) (hX : Complete X) (hX₀ : 0 < X)
    (h : ∀ xs x, ListComplete xs → Complete x → x < X → SchutteStackProper xs X → schutteStack powOmega xs x < X) :
    SmallVeblenOrdinal ≤ X :=
  schutte_stack_least_unreachable powOmega X powOmega_normal hX hX₀ h

/-- Rocq: `SchutteColumnFacts.SVO_least_stack_unreachable'`. -/
theorem SVO_least_stack_unreachable' (X : Ordinal.{u}) (hX : Complete X) (hX₀ : 0 < X)
    (h : ∀ xs x, ListComplete xs → Complete x → x < X → SchutteStackProper xs X →
      schutteStack (fun y => 1 + y) xs x < X) : SmallVeblenOrdinal ≤ X :=
  le_trans SVO_alt.le (schutte_stack_least_unreachable _ X onePlus_normal hX hX₀ h)

/-! ## Matrices of columns -/

/-- A Schütte matrix: a list of `(column, argument)` pairs, applied from the
front. Rocq: `SchutteColumnFacts.schutte_matrix`. -/
def schutteMatrix (f : Ordinal.{u} → Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → Ordinal.{u} → Ordinal.{u}
  | [] => f
  | p :: m => schutteMatrix (schutteColumn f p.1 p.2) m

/-- Rocq: `SchutteColumnFacts.schutte_matrix_monotone_func`. -/
theorem schutte_matrix_monotone_func (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f g : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), (∀ a b, a ≤ b → f a ≤ f b) →
      (∀ a b, a ≤ b → g a ≤ g b) → (∀ a, f a ≤ g a) → schutteMatrix f m x ≤ schutteMatrix g m x := by
  induction m with
  | nil => intro f g x _ _ hfg; exact hfg x
  | cons p m ih =>
    intro f g x hf hg hfg
    exact ih _ _ x (fun _ _ h => schutte_column_monotone f p.1 p.2 _ p.2 _ hf (le_refl _) h)
      (fun _ _ h => schutte_column_monotone g p.1 p.2 _ p.2 _ hg (le_refl _) h)
      (fun z => schutte_column_monotone_func f g p.1 p.2 z p.2 z hf hg hfg (le_refl _) (le_refl z))

/-- Rocq: `SchutteColumnFacts.all_complete`. -/
def AllComplete : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => True
  | p :: m => Complete p.1 ∧ Complete p.2 ∧ AllComplete m

/-- Rocq: `SchutteColumnFacts.schutte_matrix_normal`. -/
theorem schutte_matrix_normal (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ f : Ordinal.{u} → Ordinal.{u}, AllComplete m → NormalFunction f → NormalFunction (schutteMatrix f m) := by
  induction m with
  | nil => intro f _ hf; exact hf
  | cons p m ih =>
    intro f h hf
    exact ih _ h.2.2 (schutte_column_normal p.1 p.2 f h.1 h.2.1 hf)

/-- Rocq: `SchutteColumnFacts.schutte_matrix_zero_column`. -/
theorem schutte_matrix_zero_column (f : Ordinal.{u} → Ordinal.{u}) (x y : Ordinal.{u}) :
    schutteMatrix f [(0, x)] y ≈ f (x + y) :=
  schutte_column0 f x y

/-- Rocq: `SchutteColumnFacts.schutte_matrix_veblen`. -/
theorem schutte_matrix_veblen (f : Ordinal.{u} → Ordinal.{u}) (α x y : Ordinal.{u}) (hf : NormalFunction f)
    (hα : Complete α) (hx : Complete x) (hy : Complete y) :
    schutteMatrix f [(1, α), (0, x)] y ≈ veblen f α (x + y) :=
  equiv_trans (schutte_column0 (schutteColumn f 1 α) x y)
    (schutte_column_veblen α (x + y) f hf hα (add_complete hx hy))

/-- Rocq: `SchutteColumnFacts.schutte_matrix_app`. -/
theorem schutte_matrix_app : ∀ (M N : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (x : Ordinal.{u}), schutteMatrix f (M ++ N) x = schutteMatrix (schutteMatrix f M) N x
  | [], _, _, _ => rfl
  | p :: M, N, f, x => schutte_matrix_app M N (schutteColumn f p.1 p.2) x

/-- Rocq: `SchutteColumnFacts.schutte_matrix_base`. -/
theorem schutte_matrix_base (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), NormalFunction f → AllComplete m →
      f x ≤ schutteMatrix f m x := by
  induction m with
  | nil => intro f x _ _; exact le_refl _
  | cons p m ih =>
    intro f x hf h
    exact le_trans (le_trans (hf.monotone _ _ (le_add_left p.2 x)) (schutte_column_le_f p.1 p.2 x f hf.monotone))
      (ih _ x (schutte_column_normal p.1 p.2 f h.1 h.2.1 hf) h.2.2)

/-- Rocq: `SchutteColumnFacts.schutte_matrix_zero_arg`. -/
theorem schutte_matrix_zero_arg (m₁ : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (m₂ : List (Ordinal.{u} × Ordinal.{u})) (β : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}),
      (∀ a b, a ≤ b → f a ≤ f b) → Complete β →
      schutteMatrix f (m₁ ++ ([(β, 0)] ++ m₂)) x ≈ schutteMatrix f (m₁ ++ m₂) x := by
  induction m₁ with
  | nil =>
    intro m₂ β f x hf _
    have hm : ∀ a b : Ordinal.{u}, a ≤ b → schutteColumn f β 0 a ≤ schutteColumn f β 0 b :=
      fun _ _ h => schutte_column_monotone f β 0 _ 0 _ hf (le_refl 0) h
    exact equiv_intro
      (schutte_matrix_monotone_func m₂ _ f x hm hf (fun z => (schutte_column_arg0 β z f hf).le))
      (schutte_matrix_monotone_func m₂ f _ x hf hm (fun z => (schutte_column_arg0 β z f hf).ge))
  | cons p m₁ ih =>
    intro m₂ β f x hf hβ
    exact ih m₂ β _ x (fun _ _ h => schutte_column_monotone f p.1 p.2 _ p.2 _ hf (le_refl _) h) hβ

/-- Rocq: `SchutteColumnFacts.enumerates_func_equiv`. -/
theorem enumerates_func_equiv (f g : Ordinal.{u} → Ordinal.{u}) (P : Ordinal.{u} → Prop) (hfg : ∀ x, f x ≈ g x)
    (hP : ∀ x y, x ≈ y → P x → P y) (hf : Con.Enumerates f P) : Con.Enumerates g P where
  included x hx := hP _ _ (hfg x) (hf.included x hx)
  monotone x y h := le_trans (hfg x).ge (le_trans (hf.monotone x y h) (hfg y).le)
  increasing x y hy h := lt_of_le_of_lt (hfg x).ge (lt_of_lt_of_le (hf.increasing x y hy h) (hfg y).le)
  least x z hx hz hPz hlt :=
    le_trans (hfg x).ge (hf.least x z hx hz hPz fun y hy => lt_of_le_of_lt (hfg y).le (hlt y hy))

/-- Every argument of the matrix is zero. Rocq: `SchutteColumnFacts.trivial_matrix`. -/
def TrivialMatrix (m : List (Ordinal.{u} × Ordinal.{u})) : Prop := Each (fun c => c.2 ≈ 0) m

/-- Some argument of the matrix is nonzero. Rocq: `SchutteColumnFacts.nontrivial_matrix`. -/
def NontrivialMatrix : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => False
  | p :: m => 0 < p.2 ∨ NontrivialMatrix m

/-- Rocq: `SchutteColumnFacts.trivial_matrix_eq`. -/
theorem trivial_matrix_eq (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}), NormalFunction f → TrivialMatrix m →
      schutteMatrix f m x ≈ f x := by
  induction m with
  | nil => intro f x _ _; exact equiv_refl _
  | cons p m ih =>
    intro f x hf h
    have hm : ∀ a b : Ordinal.{u}, a ≤ b → schutteColumn f p.1 p.2 a ≤ schutteColumn f p.1 p.2 b :=
      fun _ _ h => schutte_column_monotone f p.1 p.2 _ p.2 _ hf.monotone (le_refl _) h
    refine equiv_trans (equiv_intro ?_ ?_) (ih f x hf h.2)
    · exact schutte_matrix_monotone_func m _ f x hm hf.monotone (fun z =>
        le_trans (schutte_column_monotone f p.1 p.2 z 0 z hf.monotone h.1.le (le_refl z))
          (schutte_column_arg0 p.1 z f hf.monotone).le)
    · exact schutte_matrix_monotone_func m f _ x hf.monotone hm (fun z =>
        le_trans (schutte_column_arg0 p.1 z f hf.monotone).ge
          (schutte_column_monotone f p.1 0 z p.2 z hf.monotone (zero_least _) (le_refl z)))

/-- Rocq: `SchutteColumnFacts.matrix_member_le`. -/
theorem matrix_member_le (m n : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u}) (b a : Ordinal.{u})
    (hf : NormalFunction f) (hm : AllComplete m) (hb : Complete b) (ha : Complete a) (hn : AllComplete n) :
    a ≤ schutteMatrix f (m ++ (b, a) :: n) 0 := by
  rw [schutte_matrix_app]
  have hM := schutte_matrix_normal m f hm hf
  exact le_trans (schutte_column_inflationary1 b a 0 _ (normal_inflationary hM) ha zero_complete)
    (schutte_matrix_base n _ 0 (schutte_column_normal b a _ hb ha hM) hn)

/-- `b ≤ schutteColumn g b a 0` for positive `a`. -/
private theorem index_le_col {g : Ordinal.{u} → Ordinal.{u}} (hg : NormalFunction g) {b a : Ordinal.{u}}
    (hb : Complete b) (ha₀ : 0 < a) : b ≤ schutteColumn g b a 0 :=
  le_trans (normal_inflationary (schutte_column_normalβ g hg) b hb)
    (schutte_column_monotone g b 1 0 a 0 hg.monotone (succ_least ha₀) (le_refl 0))

/-- Rocq: `SchutteColumnFacts.matrix_member_index_le`. -/
theorem matrix_member_index_le (m n : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b a : Ordinal.{u}) (hf : NormalFunction f) (hm : AllComplete m) (hb : Complete b) (ha : Complete a)
    (hn : AllComplete n) (ha₀ : 0 < a) : b ≤ schutteMatrix f (m ++ (b, a) :: n) 0 := by
  rw [schutte_matrix_app]
  have hM := schutte_matrix_normal m f hm hf
  exact le_trans (index_le_col hM hb ha₀) (schutte_matrix_base n _ 0 (schutte_column_normal b a _ hb ha hM) hn)

/-- Rocq: `SchutteColumnFacts.matrix_member_index_lt`. -/
theorem matrix_member_index_lt (m n : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b a : Ordinal.{u}) (hf : NormalFunction f) (hm : AllComplete m) (hb : Complete b) (ha : Complete a)
    (hn : AllComplete n) (h1a : 1 < a) : b < schutteMatrix f (m ++ (b, a) :: n) 0 := by
  rw [schutte_matrix_app]
  have hM := schutte_matrix_normal m f hm hf
  exact lt_of_le_of_lt (normal_inflationary (schutte_column_normalβ _ hM) b hb)
    (lt_of_lt_of_le ((schutte_column_normal_arg b _ hb hM).increasing 1 a ha h1a)
      (schutte_matrix_base n _ 0 (schutte_column_normal b a _ hb ha hM) hn))

/-- Anything at most `g 0` is below `schutteMatrix g n 0` for nontrivial `n`. -/
private theorem lt_nontrivial {g : Ordinal.{u} → Ordinal.{u}} (hg : NormalFunction g) {c : Ordinal.{u}}
    (hc : c ≤ g 0) : ∀ n : List (Ordinal.{u} × Ordinal.{u}), AllComplete n → NontrivialMatrix n →
      c < schutteMatrix g n 0
  | [], _, h => h.elim
  | p :: n, hn, .inl hq =>
    lt_of_le_of_lt (le_trans hc (schutte_column_arg0 p.1 0 g hg.monotone).ge)
      (lt_of_lt_of_le ((schutte_column_normal_arg p.1 g hn.1 hg).increasing 0 p.2 hn.2.1 hq)
        (schutte_matrix_base n _ 0 (schutte_column_normal p.1 p.2 g hn.1 hn.2.1 hg) hn.2.2))
  | p :: n, hn, .inr h =>
    lt_of_lt_of_le (lt_nontrivial hg hc n hn.2.2 h)
      (schutte_matrix_monotone_func n g _ 0 hg.monotone
        (fun _ _ h => schutte_column_monotone g p.1 p.2 _ p.2 _ hg.monotone (le_refl _) h)
        (fun z => le_trans (hg.monotone _ _ (le_add_left p.2 z)) (schutte_column_le_f p.1 p.2 z g hg.monotone)))

/-- Rocq: `SchutteColumnFacts.nontrivial_matrix_member_lt`. -/
theorem nontrivial_matrix_member_lt (m n : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b a : Ordinal.{u}) (hf : NormalFunction f) (hm : AllComplete m) (hb : Complete b) (ha : Complete a)
    (hn : AllComplete n) (hnt : NontrivialMatrix n) : a < schutteMatrix f (m ++ (b, a) :: n) 0 := by
  rw [schutte_matrix_app]
  have hM := schutte_matrix_normal m f hm hf
  exact lt_nontrivial (schutte_column_normal b a _ hb ha hM)
    (schutte_column_inflationary1 b a 0 _ (normal_inflationary hM) ha zero_complete) n hn hnt

/-- Rocq: `SchutteColumnFacts.nontrivial_matrix_member_index_lt`. -/
theorem nontrivial_matrix_member_index_lt (m n : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b a : Ordinal.{u}) (hf : NormalFunction f) (hm : AllComplete m) (hb : Complete b) (ha : Complete a)
    (hn : AllComplete n) (hnt : NontrivialMatrix n) (ha₀ : 0 < a) : b < schutteMatrix f (m ++ (b, a) :: n) 0 := by
  rw [schutte_matrix_app]
  have hM := schutte_matrix_normal m f hm hf
  exact lt_nontrivial (schutte_column_normal b a _ hb ha hM) (index_le_col hM hb ha₀) n hn hnt

/-- Rocq: `SchutteColumnFacts.schutte_matrix_enumerates`. -/
theorem schutte_matrix_enumerates (f : Ordinal.{u} → Ordinal.{u}) (m : List (Ordinal.{u} × Ordinal.{u}))
    (β α : Ordinal.{u}) (hβ₀ : 0 < β) (hα₀ : 0 < α) (hf : NormalFunction f) (hm : AllComplete m) (hβ : Complete β)
    (hα : Complete α) :
    Con.Enumerates (fun x => schutteMatrix f (m ++ [(β, α), (0, x)]) 0)
      (fun δ => ∀ b a, Complete b → b < β → Complete a → a < α → schutteMatrix f (m ++ [(β, a), (b, δ)]) 0 ≈ δ) := by
  have hM := schutte_matrix_normal m f hm hf
  have hN := schutte_column_normal β α _ hβ hα hM
  refine enumerates_func_equiv (schutteColumn (schutteMatrix f m) β α) _ _ (fun x => ?_) (fun x y hxy hPx => ?_)
    (Con.enumerates_equiv_pred hN (fun x _ => ⟨fun h b a hb hbβ ha haα => ?_, fun h b a hb ha hbβ haα => ?_⟩)
      (schutte_column_enumerates _ β α hM hβ hα hβ₀ hα₀))
  · rw [schutte_matrix_app]
    exact equiv_trans (equiv_intro (hN.monotone _ _ (add_zero x).ge) (hN.monotone _ _ (add_zero x).le))
      (equiv_symm (schutte_column0 _ x 0))
  · intro b a hb hbβ ha haα
    have h := hPx b a hb hbβ ha haα
    rw [schutte_matrix_app] at h ⊢
    have hNa := schutte_column_normal β a _ hβ ha hM
    exact equiv_trans (equiv_intro (schutte_column_monotone _ b y 0 x 0 hNa.monotone hxy.ge (le_refl 0))
      (schutte_column_monotone _ b x 0 y 0 hNa.monotone hxy.le (le_refl 0))) (equiv_trans h hxy)
  · rw [schutte_matrix_app]; exact h b a hb ha hbβ haα
  · have h' := h b a hb hbβ ha haα
    rw [schutte_matrix_app] at h'
    exact h'

/-- Rocq: `SchutteColumnFacts.schutte_matrix_proper`. -/
def SchutteMatrixProper : List (Ordinal.{u} × Ordinal.{u}) → Ordinal.{u} → Ordinal.{u} → Prop
  | [], _, _ => True
  | p :: m, β, α => p.1 < β ∧ p.2 < α ∧ SchutteMatrixProper m p.1 α

/-- Rocq: `SchutteColumnFacts.schutte_matrix_proper_monotone`. -/
theorem schutte_matrix_proper_monotone :
    ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (β β' α α' : Ordinal.{u}), β ≤ β' → α ≤ α' →
      SchutteMatrixProper m β α → SchutteMatrixProper m β' α'
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: m, _, _, _, _, hβ, hα, ⟨h₁, h₂, h₃⟩ =>
    ⟨lt_of_lt_of_le h₁ hβ, lt_of_lt_of_le h₂ hα, schutte_matrix_proper_monotone m _ _ _ _ (le_refl _) hα h₃⟩

/-- Rocq: `SchutteColumnFacts.final_index`. -/
def finalIndex (q : Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → Ordinal.{u}
  | [] => q
  | p :: m => finalIndex p.1 m

/-- Rocq: `SchutteColumnFacts.final_index_last`. -/
theorem final_index_last : ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (q i a : Ordinal.{u}),
    finalIndex q (m ++ [(i, a)]) = i
  | [], _, _, _ => rfl
  | p :: m, _, i, a => final_index_last m p.1 i a

/-- Rocq: `SchutteColumnFacts.final_index_monotone`. -/
theorem final_index_monotone (p q : Ordinal.{u}) (xs : List (Ordinal.{u} × Ordinal.{u})) (h : p ≤ q) :
    finalIndex p xs ≤ finalIndex q xs :=
  match xs with
  | [] => h
  | _ :: _ => le_refl _

/-- Rocq: `SchutteColumnFacts.schutte_matrix_proper_app`. -/
theorem schutte_matrix_proper_app : ∀ (m n : List (Ordinal.{u} × Ordinal.{u})) (q p : Ordinal.{u}),
    SchutteMatrixProper (m ++ n) q p ↔ SchutteMatrixProper m q p ∧ SchutteMatrixProper n (finalIndex q m) p
  | [], _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | r :: m, n, _, p =>
    ⟨fun ⟨h₁, h₂, h₃⟩ =>
      let ⟨a, b⟩ := (schutte_matrix_proper_app m n r.1 p).1 h₃
      ⟨⟨h₁, h₂, a⟩, b⟩,
     fun ⟨⟨h₁, h₂, a⟩, b⟩ => ⟨h₁, h₂, (schutte_matrix_proper_app m n r.1 p).2 ⟨a, b⟩⟩⟩

/-- Rocq: `SchutteColumnFacts.schutte_matrix_proper_split_final`. -/
theorem schutte_matrix_proper_split_final (m : List (Ordinal.{u} × Ordinal.{u})) (b a q p : Ordinal.{u}) :
    SchutteMatrixProper (m ++ [(b, a)]) q p ↔ SchutteMatrixProper m q p ∧ b < finalIndex q m ∧ a < p :=
  (schutte_matrix_proper_app m [(b, a)] q p).trans
    ⟨fun ⟨h₁, h₂, h₃, _⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃, trivial⟩⟩

/-- Rocq: `SchutteColumnFacts.proper_matrix_unreachable`. -/
theorem proper_matrix_unreachable (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (b a δ x : Ordinal.{u}), NormalFunction f → Complete b → Complete a →
      Complete x → Complete δ → AllComplete m → SchutteMatrixProper m b δ → (x ≈ 0 ∨ AdditivelyClosed δ) →
      a < δ → x < δ → schutteMatrix f ((b, a) :: m) x < schutteColumn f b δ 0 := by
  induction m with
  | nil =>
    intro f b a δ x hf hb ha hx hδ _ _ hcl haδ hxδ
    show schutteColumn f b a x < _
    match complete_zeroDec hb with
    | .inl hb₀ =>
      refine lt_of_le_of_lt (b := f (a + x)) ?_ ?_
      · rw [schutte_column_unroll]
        exact lub_least (le_refl _) (sup_least fun b' => (zero_lt _ (lt_of_lt_of_le (index_lt b b') hb₀)).elim)
      · refine lt_of_lt_of_le (hf.increasing _ _ (add_complete hδ zero_complete) ?_)
          (schutte_column_le_f b δ 0 f hf.monotone)
        refine lt_of_lt_of_le ?_ (add_zero δ).ge
        match hcl with
        | .inl hx₀ => exact lt_of_le_of_lt (le_trans (add_le_add (le_refl a) hx₀.le) (add_zero a).le) haδ
        | .inr hcl => exact hcl a x haδ hxδ
    | .inr hb₀ =>
      have hY := (schutte_column_normal b δ f hb hδ hf).complete 0 zero_complete
      exact lt_of_lt_of_le ((schutte_column_normal b a f hb ha hf).increasing _ _ (add_complete hY zero_complete)
          (lt_of_lt_of_le hxδ (le_trans (schutte_column_inflationary1 b δ 0 f (normal_inflationary hf) hδ
            zero_complete) (add_zero _).ge)))
        (le_trans (schutte_column0 _ _ 0).ge
          (schutte_column_fixpoint b δ 0 f 0 a hb hδ hf hb₀ haδ zero_complete ha zero_complete))
  | cons r m ih =>
    intro f b a δ x hf hb ha hx hδ hm hp hcl haδ hxδ
    have hNa := schutte_column_normal b a f hb ha hf
    exact lt_of_lt_of_le (ih _ r.1 r.2 δ x hNa hm.1 hm.2.1 hx hδ hm.2.2 hp.2.2 hcl hp.2.1 hxδ)
      (le_trans (schutte_column_monotone _ r.1 δ 0 _ 0 hNa.monotone
        (schutte_column_inflationary1 b δ 0 f (normal_inflationary hf) hδ zero_complete) (le_refl 0))
        (schutte_column_fixpoint b δ 0 f r.1 a hb hδ hf hp.1 haδ hm.1 ha zero_complete))

/-- Rocq: `SchutteColumnFacts.proper_matrix_apex_unreachable`. -/
theorem proper_matrix_apex_unreachable (m : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (β x : Ordinal.{u}) (hf : NormalFunction f) (hβ : Complete β) (hx : Complete x) (hm : AllComplete m)
    (hcase : x ≈ 0 ∨ 1 < β) (hβ₀ : 0 < β) (hp : SchutteMatrixProper m β (schutteColumn f β 1 0))
    (hxT : x < schutteColumn f β 1 0) : schutteMatrix f m x < schutteColumn f β 1 0 := by
  have hT := (schutte_column_normal β 1 f hβ one_complete hf).complete 0 zero_complete
  match m, hm, hp with
  | [], _, _ =>
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hT zero_complete) (lt_of_lt_of_le hxT (add_zero _).ge))
      (le_trans (schutte_column_arg0 β _ f hf.monotone).ge (le_trans (schutte_column0 _ _ 0).ge
        (schutte_column_fixpoint β 1 0 f 0 0 hβ one_complete hf hβ₀ zero_lt_one' zero_complete zero_complete
          zero_complete)))
  | r :: m, hm, hp =>
    have hcl : x ≈ 0 ∨ AdditivelyClosed (schutteColumn f β 1 0) := match hcase with
      | .inl h => .inl h
      | .inr h1β => .inr fun p q hp hq =>
        schutte_column_add_closed f β 1 0 p q hf hβ one_complete zero_complete h1β zero_lt_one' hp hq
    refine lt_of_lt_of_le (proper_matrix_unreachable m f r.1 r.2 _ x hf hm.1 hm.2.1 hx hT hm.2.2 hp.2.2 hcl
      hp.2.1 hxT) ?_
    exact le_trans (schutte_column_monotone_func f _ _ _ 0 _ 0 hf.monotone
        (fun _ _ h => schutte_column_monotone f β 0 _ 0 _ hf.monotone (le_refl 0) h)
        (fun z => (schutte_column_arg0 β z f hf.monotone).ge) (le_refl _) (le_refl 0))
      (schutte_column_fixpoint β 1 0 f r.1 0 hβ one_complete hf hp.1 zero_lt_one' hm.1 zero_complete zero_complete)

/-- Rocq: `SchutteColumnFacts.max_index_exists`. -/
theorem max_index_exists : ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (q : Ordinal.{u}), 0 < q → Complete q →
    Each (fun x => x.1 < q) m → ∃ r : q.Carrier, Each (fun x => x.1 ≤ q r) m
  | [], _, hq₀, _, _ => let ⟨r, _⟩ := lt_elim hq₀; ⟨r, trivial⟩
  | p :: m, q, hq₀, hq, ⟨h₁, h₂⟩ =>
    let ⟨r, hr⟩ := max_index_exists m q hq₀ hq h₂
    let ⟨s, hs⟩ := lt_elim h₁
    let ⟨t, hst, hrt⟩ := complete_directed hq s r
    ⟨t, le_trans hs hst, Each.imp (fun _ hx => le_trans hx hrt) hr⟩

/-- Rocq: `SchutteColumnFacts.pump_matrix`. -/
def pumpMatrix (x : Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u})
  | [] => []
  | p :: m => (x + ofNat (m.length + 1), p.2) :: pumpMatrix x m

/-- Rocq: `SchutteColumnFacts.pump_matrix_proper`. -/
theorem pump_matrix_proper : ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (p q : Ordinal.{u}),
    Each (fun x => x.2 < q) m → SchutteMatrixProper (pumpMatrix p m) (p + ofNat (m.length + 1)) q
  | [], _, _, _ => trivial
  | _ :: m, p, q, ⟨h₁, h₂⟩ => ⟨add_lt_add_left p (succ_lt _), h₁, pump_matrix_proper m p q h₂⟩

/-- Rocq: `SchutteColumnFacts.pump_matrix_all_complete`. -/
theorem pump_matrix_all_complete : ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (q : Ordinal.{u}),
    AllComplete m → Complete q → AllComplete (pumpMatrix q m)
  | [], _, _, _ => trivial
  | _ :: m, q, ⟨_, h₂, h₃⟩, hq => ⟨add_complete hq (ofNat_complete _), h₂, pump_matrix_all_complete m q h₃ hq⟩

/-- `1 < E` when `E` is closed under `schutteColumn f · 1 0`. -/
private theorem one_lt_of_E {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) {E : Ordinal.{u}}
    (hfix : schutteColumn f E 1 0 ≤ E) : 1 < E :=
  lt_of_lt_of_le (lt_of_le_of_lt (add_zero 1).ge (add_lt_add_left 1 (lt_of_lt_of_le zero_lt_one' (add_zero 1).ge)))
    (le_trans (onePlus_least_normal hf _ (add_complete one_complete zero_complete))
      (le_trans (schutte_column_le_f E 1 0 f hf.monotone) hfix))

/-- Rocq: `SchutteColumnFacts.proper_matrix_E_unreachable`. -/
theorem proper_matrix_E_unreachable (m : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (x E : Ordinal.{u}) (hf : NormalFunction f) (hE : Complete E) (hx : Complete x) (hm : AllComplete m)
    (hp : SchutteMatrixProper m E E) (hxE : x < E) (hfix : schutteColumn f E 1 0 ≤ E) : schutteMatrix f m x < E :=
  have hinf := normal_inflationary (schutte_column_normalβ f hf) E hE
  have h1E := one_lt_of_E hf hfix
  lt_of_lt_of_le (proper_matrix_apex_unreachable m f E x hf hE hx hm (.inr h1E) (lt_trans zero_lt_one' h1E)
    (schutte_matrix_proper_monotone m E E E _ (le_refl E) hinf hp) (lt_of_lt_of_le hxE hinf)) hfix

private theorem pump_le (r x : Ordinal.{u}) : ∀ (m : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u}),
    (∀ a b, a ≤ b → f a ≤ f b) → Each (fun p => p.1 ≤ r) m → schutteMatrix f m x ≤ schutteMatrix f (pumpMatrix r m) x
  | [], _, _, _ => le_refl _
  | p :: m, f, hf, ⟨h₁, h₂⟩ =>
    have hm := fun _ _ h => schutte_column_monotone f p.1 p.2 _ p.2 _ hf (le_refl _) h
    le_trans (pump_le r x m _ hm h₂) (schutte_matrix_monotone_func (pumpMatrix r m) _ _ x hm
      (fun _ _ h => schutte_column_monotone f _ p.2 _ p.2 _ hf (le_refl _) h)
      (fun z => schutte_column_monotoneβ p.1 _ p.2 z f hf (le_trans h₁ (le_add_right r _))))

/-- Rocq: `SchutteColumnFacts.matrix_E_unreachable`. -/
theorem matrix_E_unreachable (m : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (x E : Ordinal.{u}) (hf : NormalFunction f) (hE : Complete E) (hx : Complete x) (hm : AllComplete m)
    (h : Each (fun p => p.1 < E ∧ p.2 < E) m) (hxE : x < E) (hfix : schutteColumn f E 1 0 ≤ E) :
    schutteMatrix f m x < E := by
  have hE₀ : 0 < E := lt_of_le_of_lt (zero_least x) hxE
  obtain ⟨q, hq⟩ := max_index_exists m E hE₀ hE (Each.imp (fun _ h => h.1) h)
  refine lt_of_le_of_lt (pump_le (E q) x m f hf.monotone hq) ?_
  have hEq := complete_subord hE q
  have hinf := normal_inflationary (schutte_column_normalβ f hf) E hE
  have h1E := one_lt_of_E hf hfix
  have hωE : (ω : Ordinal.{u}) ≤ schutteColumn f E 1 0 := by
    have hN0 := schutte_column_normal 1 0 f one_complete zero_complete hf
    refine le_trans (pow_one' omega_gt0).ge (le_trans (add_zero _).ge ?_)
    refine le_trans (veblen_onePlus 1 one_complete 0 zero_complete).ge ?_
    refine le_trans (veblen_monotone_func onePlus_normal hf (fun z hz => onePlus_least_normal hf z hz) 1 0
      one_complete zero_complete) ?_
    exact le_trans (schutte_column_veblen 1 0 f hf one_complete zero_complete).ge
      (schutte_column_monotoneβ 1 E 1 0 f hf.monotone (le_of_lt h1E))
  refine proper_matrix_E_unreachable _ f x E hf hE hx (pump_matrix_all_complete m _ hm hEq)
    (schutte_matrix_proper_monotone _ _ E E E ?_ (le_refl E)
      (pump_matrix_proper m (E q) E (Each.imp (fun _ h => h.2) h))) hxE hfix
  exact le_of_lt (lt_of_lt_of_le (schutte_column_add_closed f E 1 0 _ _ hf hE one_complete zero_complete h1E
    zero_lt_one' (lt_of_lt_of_le (index_lt E q) hinf) (lt_of_lt_of_le (index_lt ω ⟨m.length + 1⟩) hωE)) hfix)

/-- Rocq: `SchutteColumnFacts.proper_matrix_is_unreachable`. -/
def ProperMatrixIsUnreachable (f : Ordinal.{u} → Ordinal.{u}) (E : Ordinal.{u}) : Prop :=
  0 < E ∧ ∀ m, AllComplete m → SchutteMatrixProper m E E → schutteMatrix f m 0 < E

/-- Rocq: `SchutteColumnFacts.proper_matrix_is_unreachable_iff`. -/
theorem proper_matrix_is_unreachable_iff (f : Ordinal.{u} → Ordinal.{u}) (E : Ordinal.{u}) (hf : NormalFunction f)
    (hE : Complete E) : SchutteUnreachable f E ↔ ProperMatrixIsUnreachable f E := by
  refine ⟨fun H => ?_, fun ⟨hE₀, H⟩ => ⟨hE₀, fun β α x hβ hα hx hβE hαE hxE => ?_⟩⟩
  · have hT := (E_number_iff_unreachable E f hf hE).2 H
    exact ⟨H.1, fun m hm hp => proper_matrix_E_unreachable m f 0 E hf hE zero_complete hm hp H.1 hT.le⟩
  · have hbase : ∀ z, (∀ (b : β) (a : α), False) → f (α + x) ≤ z → schutteColumn f β α x ≤ z := by
      intro z hne h
      rw [schutte_column_unroll]
      exact lub_least h (sup_least fun b => sup_least fun a => (hne b a).elim)
    have h1E : 1 < E := lt_of_le_of_lt (succ_least (hf.nonzero 0)) (H [] trivial trivial)
    match complete_zeroDec hα with
    | .inl hα₀ =>
      have hne : ∀ (b : β) (a : α), False := fun _ a => zero_lt _ (lt_of_lt_of_le (index_lt α a) hα₀)
      match complete_zeroDec hx with
      | .inl hx₀ =>
        exact lt_of_le_of_lt (hbase _ hne (hf.monotone _ _ (le_trans (add_le_add hα₀ hx₀) (zero_add 0).le)))
          (H [] trivial trivial)
      | .inr _ =>
        refine lt_of_le_of_lt (hbase _ hne ?_) (H [(0, x)] ⟨zero_complete, hx, trivial⟩ ⟨hE₀, hxE, trivial⟩)
        exact le_trans (hf.monotone _ _ (le_trans (add_le_add hα₀ (add_zero x).ge) (zero_add _).le))
          (schutte_column_le_f 0 x 0 f hf.monotone)
    | .inr hα₀ =>
      match complete_zeroDec hβ with
      | .inl hβ₀ =>
        have hne : ∀ (b : β) (a : α), False := fun b _ => zero_lt _ (lt_of_lt_of_le (index_lt β b) hβ₀)
        match complete_zeroDec hx with
        | .inl hx₀ =>
          refine lt_of_le_of_lt (hbase _ hne ?_) (H [(0, α)] ⟨zero_complete, hα, trivial⟩ ⟨hE₀, hαE, trivial⟩)
          exact le_trans (hf.monotone _ _ (add_le_add (le_refl α) hx₀)) (schutte_column_le_f 0 α 0 f hf.monotone)
        | .inr hx₀ =>
          refine lt_of_le_of_lt (hbase _ hne ?_) (H [(1, α), (0, x)]
            ⟨one_complete, hα, zero_complete, hx, trivial⟩ ⟨h1E, hαE, zero_lt_one', hxE, trivial⟩)
          exact le_trans (hf.monotone _ _ (add_le_add (le_refl α) (add_zero x).ge))
            (le_trans (schutte_column_le_f 1 α _ f hf.monotone) (schutte_column0 _ x 0).ge)
      | .inr hβ₀ =>
        match complete_zeroDec hx with
        | .inl hx₀ =>
          exact lt_of_le_of_lt (schutte_column_monotone f β α x α 0 hf.monotone (le_refl α) hx₀)
            (H [(β, α)] ⟨hβ, hα, trivial⟩ ⟨hβE, hαE, trivial⟩)
        | .inr _ =>
          have hN := schutte_column_normal β α f hβ hα hf
          exact lt_of_le_of_lt (le_trans (hN.monotone _ _ (add_zero x).ge) (schutte_column0 _ x 0).ge)
            (H [(β, α), (0, x)] ⟨hβ, hα, zero_complete, hx, trivial⟩ ⟨hβE, hαE, hβ₀, hxE, trivial⟩)

/-- Rocq: `SchutteColumnFacts.E_number_iff_matrix_unreachable`. -/
theorem E_number_iff_matrix_unreachable (E : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f)
    (hE : Complete E) : schutteColumn f E 1 0 ≈ E ↔ ProperMatrixIsUnreachable f E :=
  (E_number_iff_unreachable E f hf hE).trans (proper_matrix_is_unreachable_iff f E hf hE)

/-- Rocq: `SchutteColumnFacts.LVO_proper_matrix_unreachable`. -/
theorem LVO_proper_matrix_unreachable : ProperMatrixIsUnreachable powOmega (LargeVeblenOrdinal.{u}) :=
  (proper_matrix_is_unreachable_iff powOmega _ powOmega_normal LVO_complete).1 LVO_unreachable

/-- Rocq: `SchutteColumnFacts.LVO_least_matrix_unreachable`. -/
theorem LVO_least_matrix_unreachable (E : Ordinal.{u}) (hE : Complete E) (h : ProperMatrixIsUnreachable powOmega E) :
    LargeVeblenOrdinal ≤ E :=
  LVO_least_unreachable E hE ((proper_matrix_is_unreachable_iff powOmega E powOmega_normal hE).2 h)

/-- Rocq: `SchutteColumnFacts.LVO_matrix_unreachable'`. -/
theorem LVO_matrix_unreachable' : ProperMatrixIsUnreachable (fun y => 1 + y) (LargeVeblenOrdinal.{u}) :=
  (proper_matrix_is_unreachable_iff _ _ onePlus_normal LVO_complete).1
    ⟨LVO_nonzero, fun β α x hβ hα hx h₁ h₂ h₃ =>
      lt_of_lt_of_le ((fixpoint_schutte_unreachable _ 0 onePlus_normal zero_complete).2 β α x hβ hα hx
        (lt_of_lt_of_le h₁ LVO_alt.le) (lt_of_lt_of_le h₂ LVO_alt.le) (lt_of_lt_of_le h₃ LVO_alt.le)) LVO_alt.ge⟩

/-- Rocq: `SchutteColumnFacts.LVO_least_matrix_unreachable'`. -/
theorem LVO_least_matrix_unreachable' (E : Ordinal.{u}) (hE : Complete E)
    (h : ProperMatrixIsUnreachable (fun y => 1 + y) E) : LargeVeblenOrdinal ≤ E :=
  le_trans LVO_alt.le (fixpoint_schutte_least_unreachable _ E onePlus_normal hE
    ((proper_matrix_is_unreachable_iff _ E onePlus_normal hE).2 h))

/-- Rocq: `SchutteColumnFacts.stack_to_matrix`. -/
def stackToMatrix : List Ordinal.{u} → List (Ordinal.{u} × Ordinal.{u})
  | [] => []
  | x :: xs => (ofNat xs.length, x) :: stackToMatrix xs

/-- Rocq: `SchutteColumnFacts.stack_to_matrix_eq`. -/
theorem stack_to_matrix_eq : ∀ (xs : List Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (x₀ : Ordinal.{u}),
    schutteStack f xs x₀ = schutteMatrix f (stackToMatrix xs) x₀
  | [], _, _ => rfl
  | _ :: xs, _, x₀ => stack_to_matrix_eq xs _ x₀

/-- Rocq: `SchutteColumnFacts.stack_to_matrix_complete`. -/
theorem stack_to_matrix_complete : ∀ xs : List Ordinal.{u}, AllComplete (stackToMatrix xs) ↔ ListComplete xs
  | [] => ⟨fun _ => trivial, fun _ => trivial⟩
  | _ :: xs => ⟨fun ⟨_, h, h'⟩ => ⟨h, (stack_to_matrix_complete xs).1 h'⟩,
      fun ⟨h, h'⟩ => ⟨ofNat_complete _, h, (stack_to_matrix_complete xs).2 h'⟩⟩

/-- Rocq: `SchutteColumnFacts.stack_to_matrix_proper`. -/
theorem stack_to_matrix_proper : ∀ (xs : List Ordinal.{u}) (p q : Ordinal.{u}),
    SchutteMatrixProper (stackToMatrix xs) p q ↔ ofNat xs.length ≤ p ∧ SchutteStackProper xs q
  | [], p, _ => ⟨fun _ => ⟨zero_least p, trivial⟩, fun _ => trivial⟩
  | _ :: xs, _, q =>
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨succ_least h₁, h₂, ((stack_to_matrix_proper xs _ q).1 h₃).2⟩,
     fun ⟨hle, h₂, hs⟩ => ⟨lt_of_lt_of_le (succ_lt _) hle, h₂,
       (stack_to_matrix_proper xs _ q).2 ⟨le_refl _, hs⟩⟩⟩

/-! ## Comparing matrices -/

/-- Rocq: `SchutteColumnFacts.schutte_column_collapse`. -/
theorem schutte_column_collapse (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (n a b c : Ordinal.{u})
    (hn : Complete n) (ha : Complete a) (_hb : Complete b) (hc : Complete c) (hn₀ : 0 < n) (hac : a < c)
    (hbc : b ≤ c) (hfix : schutteColumn f n c 0 ≤ c) : schutteColumn f n a b ≤ c :=
  have hY := (schutte_column_normal n c f hn hc hf).complete 0 zero_complete
  le_trans (schutte_column_monotone f n a b a _ hf.monotone (le_refl a)
      (le_trans hbc (le_trans (schutte_column_inflationary1 n c 0 f (normal_inflationary hf) hc zero_complete)
        (add_zero _).ge)))
    (le_trans (schutte_column0 _ _ 0).ge (le_trans (schutte_column_fixpoint n c 0 f 0 a hn hc hf hn₀ hac
      zero_complete ha zero_complete) hfix))

/-- Rocq: `SchutteColumnFacts.schutte_column_collapse'`. -/
theorem schutte_column_collapse' (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (n a b c : Ordinal.{u})
    (hn : Complete n) (ha : Complete a) (_hb : Complete b) (hc : Complete c) (hn₀ : 0 < n) (hac : a < c)
    (hbc : b < c) (hfix : schutteColumn f n c 0 ≤ c) : schutteColumn f n a b < c :=
  have hY := (schutte_column_normal n c f hn hc hf).complete 0 zero_complete
  lt_of_lt_of_le ((schutte_column_normal n a f hn ha hf).increasing _ _ (add_complete hY zero_complete)
      (lt_of_lt_of_le hbc (le_trans (schutte_column_inflationary1 n c 0 f (normal_inflationary hf) hc
        zero_complete) (add_zero _).ge)))
    (le_trans (schutte_column0 _ _ 0).ge (le_trans (schutte_column_fixpoint n c 0 f 0 a hn hc hf hn₀ hac
      zero_complete ha zero_complete) hfix))

/-- Rocq: `SchutteColumnFacts.schutte_matrix_preserves_add_closed`. -/
theorem schutte_matrix_preserves_add_closed (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ f : Ordinal.{u} → Ordinal.{u}, NormalFunction f →
      (∀ x p q, Complete x → p < f x → q < f x → p + q < f x) →
      ∀ x₀ p q, Complete x₀ → AllComplete m → p < schutteMatrix f m x₀ → q < schutteMatrix f m x₀ →
        p + q < schutteMatrix f m x₀ := by
  induction m with
  | nil => intro f _ hf₂ x₀ p q hx₀ _ hp hq; exact hf₂ x₀ p q hx₀ hp hq
  | cons r m ih =>
    intro f hf hf₂ x₀ p q hx₀ hm hp hq
    exact ih _ (schutte_column_normal r.1 r.2 f hm.1 hm.2.1 hf)
      (fun x p q hx hp hq => schutte_column_preserves_add_closed f hf hf₂ x r.1 r.2 p q hx hm.1 hm.2.1 hp hq)
      x₀ p q hx₀ hm.2.2 hp hq

/-- Rocq: `SchutteColumnFacts.schutte_matrix_add_closed`. -/
theorem schutte_matrix_add_closed (f : Ordinal.{u} → Ordinal.{u}) (b x x₀ : Ordinal.{u})
    (m : List (Ordinal.{u} × Ordinal.{u})) (p q : Ordinal.{u}) (hf : NormalFunction f) (hx : Complete x)
    (hb : Complete b) (hm : AllComplete m) (hx₀ : Complete x₀) (hx0 : 0 < x) (h1b : 1 < b)
    (hp : p < schutteMatrix f ((b, x) :: m) x₀) (hq : q < schutteMatrix f ((b, x) :: m) x₀) :
    p + q < schutteMatrix f ((b, x) :: m) x₀ :=
  schutte_matrix_preserves_add_closed m _ (schutte_column_normal b x f hb hx hf)
    (fun z p q hz hp hq => schutte_column_add_closed f b x z p q hf hb hx hz h1b hx0 hp hq) x₀ p q hx₀ hm hp hq

/-- Rocq: `SchutteColumnFacts.schutte_matrix_fixpoint1`. -/
theorem schutte_matrix_fixpoint1 (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (x₀ : Ordinal.{u}) (f g : Ordinal.{u} → Ordinal.{u}), AllComplete m → Complete x₀ → NormalFunction f →
      NormalFunction g → (∀ z, Complete z → g (f z) ≤ f z) →
      g (schutteMatrix f m x₀) ≤ schutteMatrix f m x₀ := by
  induction m with
  | nil => intro x₀ f g _ hx₀ _ _ h; exact h x₀ hx₀
  | cons r m ih =>
    intro x₀ f g hm hx₀ hf hg h
    obtain ⟨hb, hx, hm⟩ := hm
    refine ih x₀ _ g hm hx₀ (schutte_column_normal r.1 r.2 f hb hx hf) hg fun z hz => ?_
    have transfer : ∀ w, Complete w → schutteColumn f r.1 r.2 z ≈ f w → g (schutteColumn f r.1 r.2 z) ≤
        schutteColumn f r.1 r.2 z := fun w hw heq =>
      le_trans (hg.monotone _ _ heq.le) (le_trans (h w hw) heq.ge)
    match complete_zeroDec hb, complete_zeroDec hx with
    | .inl hb₀, _ =>
      exact transfer _ (add_complete hx hz) (equiv_intro
        (le_trans (schutte_column_monotoneβ _ 0 _ z f hf.monotone hb₀) (schutte_column0 f _ z).le)
        (schutte_column_le_f _ _ z f hf.monotone))
    | _, .inl hx₀' =>
      exact transfer _ hz (equiv_intro
        (le_trans (schutte_column_monotone f _ _ z 0 z hf.monotone hx₀' (le_refl z))
          (schutte_column_arg0 _ z f hf.monotone).le)
        (le_trans (hf.monotone _ _ (le_add_left _ z)) (schutte_column_le_f _ _ z f hf.monotone)))
    | .inr hb₀, .inr hx₀' =>
      have hY := (schutte_column_normal r.1 r.2 f hb hx hf).complete z hz
      exact le_trans (hg.monotone _ _ (le_trans (le_trans (add_zero _).ge (normal_inflationary hf _
          (add_complete hY zero_complete))) (le_refl _)))
        (le_trans (h _ (add_complete hY zero_complete)) (le_trans (schutte_column_arg0 r.1 _ f hf.monotone).ge
          (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint r.1 r.2 z f 0 0 hb hx hf hb₀ hx₀'
            zero_complete zero_complete hz))))

/-- Rocq: `SchutteColumnFacts.schutte_matrix_fixpoint2`. -/
theorem schutte_matrix_fixpoint2 (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (x₀ : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (r s : Ordinal.{u}), NormalFunction f → AllComplete m →
      Complete x₀ → (r, s) ∈ m → 0 < r → 0 < s → Complete r → Complete s →
      f (schutteMatrix f m x₀) ≤ schutteMatrix f m x₀ := by
  induction m with
  | nil => intro _ _ _ _ _ _ _ h; nomatch h
  | cons p m ih =>
    intro x₀ f r s hf hm hx₀ hmem hr hs hrc hsc
    cases hmem with
    | head =>
      exact schutte_matrix_fixpoint1 m x₀ _ f hm.2.2 hx₀ (schutte_column_normal r s f hrc hsc hf) hf fun z hz =>
        have hY := (schutte_column_normal r s f hrc hsc hf).complete z hz
        le_trans (hf.monotone _ _ (add_zero _).ge) (le_trans (schutte_column_arg0 r _ f hf.monotone).ge
          (le_trans (schutte_column0 _ _ 0).ge (schutte_column_fixpoint r s z f 0 0 hrc hsc hf hr hs
            zero_complete zero_complete hz)))
    | tail _ hmem =>
      have hN := schutte_column_normal p.1 p.2 f hm.1 hm.2.1 hf
      exact le_trans (le_trans (hf.monotone _ _ (le_add_left p.2 _)) (schutte_column_le_f p.1 p.2 _ f hf.monotone))
        (ih x₀ _ r s hN hm.2.2 hx₀ hmem hr hs hrc hsc)

/-- Rocq: `SchutteColumnFacts.schutte_matrix_unreachable`. -/
theorem schutte_matrix_unreachable (m : Ordinal.{u}) :
    ∀ (x : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (vs : List (Ordinal.{u} × Ordinal.{u})),
      NormalFunction f → Complete m → AllComplete vs → SchutteMatrixProper vs m x → Complete x → 0 < m →
      (∀ v, Complete v → v < m → schutteColumn f v x 0 ≤ x) → schutteMatrix f vs 0 < x := by
  induction m using ltRec with
  | ind m ih =>
  intro x f vs hf hm hvs hp hx hm₀ hfix
  match vs, hvs, hp with
  | [], _, _ =>
    have hx₀ : 0 < x := lt_of_lt_of_le (schutte_column_nonzero f 0 x 0 hf) (hfix 0 zero_complete hm₀)
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hx zero_complete) (lt_of_lt_of_le hx₀ (add_zero x).ge))
      (le_trans (schutte_column_le_f 0 x 0 f hf.monotone) (hfix 0 zero_complete hm₀))
  | (b, v) :: vs, ⟨hb, hv, hvs⟩, ⟨hbm, hvx, hp⟩ =>
    show schutteMatrix (schutteColumn f b v) vs 0 < x
    match complete_zeroDec hb with
    | .inl hb₀ =>
      match vs, hp with
      | [], _ =>
        exact lt_of_lt_of_le ((schutte_column_normal_arg b f hb hf).increasing v x hx hvx) (hfix b hb hbm)
      | _ :: _, hp => exact (lt_irrefl _ (lt_of_lt_of_le hp.1 (le_trans hb₀ (zero_least _)))).elim
    | .inr hb₀ =>
      refine ih b hbm x _ vs (schutte_column_normal b v f hb hv hf) hb hvs hp hx hb₀ fun q hq hqb => ?_
      have hNv := schutte_column_normal b v f hb hv hf
      exact le_trans (schutte_column_monotone _ q x 0 _ 0 hNv.monotone
          (schutte_column_inflationary1 b x 0 f (normal_inflationary hf) hx zero_complete) (le_refl 0))
        (le_trans (schutte_column_fixpoint b x 0 f q v hb hx hf hqb hvx hq hv zero_complete) (hfix b hb hbm))

/-- Rocq: `SchutteColumnFacts.schutte_matrix_column_fix`. -/
theorem schutte_matrix_column_fix (f : Ordinal.{u} → Ordinal.{u}) (b b' a : Ordinal.{u})
    (m : List (Ordinal.{u} × Ordinal.{u})) (x₀ : Ordinal.{u}) (hf : NormalFunction f) (hb : Complete b)
    (hb' : Complete b') (ha : Complete a) (hm : AllComplete m) (hx₀ : Complete x₀) (hb'b : b' < b) (ha₀ : 0 < a) :
    schutteColumn f b' (schutteMatrix f ((b, a) :: m) x₀) 0 ≤ schutteMatrix f ((b, a) :: m) x₀ :=
  schutte_matrix_fixpoint1 m x₀ _ (fun x => schutteColumn f b' x 0) hm hx₀ (schutte_column_normal b a f hb ha hf)
    (schutte_column_normal_arg b' f hb' hf) fun z hz =>
      have hY := (schutte_column_normal b a f hb ha hf).complete z hz
      le_trans (schutte_column_monotone_func f _ b' _ 0 _ 0 hf.monotone
          (fun _ _ h => schutte_column_monotone f b 0 _ 0 _ hf.monotone (le_refl 0) h)
          (fun w => (schutte_column_arg0 b w f hf.monotone).ge) (le_refl _) (le_refl 0))
        (schutte_column_fixpoint b a z f b' 0 hb ha hf hb'b ha₀ hb' zero_complete hz)

/-- Rocq: `SchutteColumnFacts.schutte_matrix_column_lt1`. -/
theorem schutte_matrix_column_lt1 (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (q : Ordinal.{u}), NormalFunction f → AllComplete m → Complete q →
      SchutteMatrixProper m q (schutteMatrix f m 0) →
      schutteMatrix f m 0 < schutteColumn f q (schutteMatrix f m 0) 0 := by
  induction m with
  | nil =>
    intro f q hf _ hq _
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete (hf.complete 0 zero_complete) zero_complete)
      (lt_of_lt_of_le (hf.nonzero 0) (add_zero _).ge)) (schutte_column_le_f q _ 0 f hf.monotone)
  | cons r m ih =>
    intro f q hf hm hq hp
    have hN := schutte_column_normal r.1 r.2 f hm.1 hm.2.1 hf
    have hW := (schutte_matrix_normal m _ hm.2.2 hN).complete 0 zero_complete
    refine lt_of_lt_of_le (ih _ r.1 hN hm.2.2 hm.1 hp.2.2) ?_
    refine le_trans (schutte_column_monotone_full _ (schutteColumn f q r.2) r.1 _ 0 r.1 _ 0 hN.monotone
      (schutte_column_normal q r.2 f hq hm.2.1 hf).monotone
      (fun z => schutte_column_monotoneβ r.1 q r.2 z f hf.monotone (le_of_lt hp.1)) (le_refl _)
      (schutte_column_inflationary1 q _ 0 f (normal_inflationary hf) hW zero_complete) (le_refl 0)) ?_
    exact schutte_column_fixpoint q _ 0 f r.1 r.2 hq hW hf hp.1 hp.2.1 hm.1 hm.2.1 zero_complete

/-- Rocq: `SchutteColumnFacts.schutte_matrix_column_lt2`. -/
theorem schutte_matrix_column_lt2 (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (b a : Ordinal.{u}), NormalFunction f → AllComplete m → Complete b →
      Complete a → a < schutteMatrix f ((b, a) :: m) 0 →
      SchutteMatrixProper m b (schutteMatrix f ((b, a) :: m) 0) →
      schutteMatrix f ((b, a) :: m) 0 < schutteColumn f b (schutteMatrix f ((b, a) :: m) 0) 0 := by
  induction m with
  | nil =>
    intro f b a hf _ hb ha haW _
    exact (schutte_column_normal_arg b f hb hf).increasing a _
      ((schutte_column_normal b a f hb ha hf).complete 0 zero_complete) haW
  | cons r m ih =>
    intro f b a hf hm hb ha haW hp
    have hNa := schutte_column_normal b a f hb ha hf
    have hW := (schutte_matrix_normal (r :: m) _ hm hNa).complete 0 zero_complete
    refine lt_of_lt_of_le (ih _ r.1 r.2 hNa hm.2.2 hm.1 hm.2.1 hp.2.1 hp.2.2) ?_
    exact le_trans (schutte_column_monotone _ r.1 _ 0 _ 0 hNa.monotone
        (schutte_column_inflationary1 b _ 0 f (normal_inflationary hf) hW zero_complete) (le_refl 0))
      (schutte_column_fixpoint b _ 0 f r.1 a hb hW hf hp.1 haW hm.1 ha zero_complete)

/-- Rocq: `SchutteColumnFacts.schutte_matrix_rev_induction`. -/
theorem schutte_matrix_rev_induction (f : Ordinal.{u} → Ordinal.{u})
    (P : List (Ordinal.{u} × Ordinal.{u}) → Ordinal.{u} → Ordinal.{u} → Prop)
    (h₀ : ∀ x₀, P [] x₀ (f x₀))
    (hind : ∀ m, (∀ x₀, P m x₀ (schutteMatrix f m x₀)) →
      ∀ b a x₀, P (m ++ [(b, a)]) x₀ (schutteColumn (schutteMatrix f m) b a x₀)) :
    ∀ m x₀, P m x₀ (schutteMatrix f m x₀) := by
  intro m
  refine List.rev_ind (fun m => ∀ x₀, P m x₀ (schutteMatrix f m x₀)) h₀ (fun x xs ih x₀ => ?_) m
  rw [schutte_matrix_app]
  exact hind xs ih x.1 x.2 x₀

/-- Rocq: `SchutteColumnFacts.all_complete_app`. -/
theorem all_complete_app : ∀ M N : List (Ordinal.{u} × Ordinal.{u}),
    AllComplete (M ++ N) ↔ AllComplete M ∧ AllComplete N
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: M, N => ⟨fun ⟨h₁, h₂, h₃⟩ => let ⟨a, b⟩ := (all_complete_app M N).1 h₃; ⟨⟨h₁, h₂, a⟩, b⟩,
      fun ⟨⟨h₁, h₂, a⟩, b⟩ => ⟨h₁, h₂, (all_complete_app M N).2 ⟨a, b⟩⟩⟩

/-- Rocq: `SchutteColumnFacts.schutte_matrix_lt1`. -/
theorem schutte_matrix_lt1 (xs : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (xb xa : Ordinal.{u}) (ys : List (Ordinal.{u} × Ordinal.{u})) (yb ya y₀ : Ordinal.{u}) (hf : NormalFunction f)
    (hxs : AllComplete xs) (hxb : Complete xb) (hxa : Complete xa) (hys : AllComplete ys) (hyb : Complete yb)
    (hya : Complete ya) (hy₀ : Complete y₀) (hp : SchutteMatrixProper xs xb (schutteMatrix f ((yb, ya) :: ys) y₀))
    (hya₀ : 0 < ya) (hxy : xb < yb) (hxa' : xa < schutteMatrix f ((yb, ya) :: ys) y₀) :
    schutteMatrix f ((xb, xa) :: xs) 0 < schutteMatrix f ((yb, ya) :: ys) y₀ := by
  have hY := (schutte_matrix_normal ((yb, ya) :: ys) f ⟨hyb, hya, hys⟩ hf).complete y₀ hy₀
  have hcol := schutte_matrix_column_fix f yb xb ya ys y₀ hf hyb hxb hya hys hy₀ hxy hya₀
  show schutteMatrix (schutteColumn f xb xa) xs 0 < _
  match complete_zeroDec hxb with
  | .inl hxb₀ =>
    match xs, hp with
    | [], _ => exact lt_of_lt_of_le ((schutte_column_normal_arg xb f hxb hf).increasing xa _ hY hxa') hcol
    | _ :: _, hp => exact (lt_irrefl _ (lt_of_lt_of_le hp.1 (le_trans hxb₀ (zero_least _)))).elim
  | .inr hxb₀ =>
    have hNa := schutte_column_normal xb xa f hxb hxa hf
    refine schutte_matrix_unreachable xb _ _ xs hNa hxb hxs hp hY hxb₀ fun v hv hvb => ?_
    exact le_trans (schutte_column_monotone _ v _ 0 _ 0 hNa.monotone
        (schutte_column_inflationary1 xb _ 0 f (normal_inflationary hf) hY zero_complete) (le_refl 0))
      (le_trans (schutte_column_fixpoint xb _ 0 f v xa hxb hY hf hvb hxa' hv hxa zero_complete) hcol)

/-- `schutteColumn f b a ≈ f` pointwise when `a ≈ 0`. -/
private theorem col_zero_arg_le {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ a b, a ≤ b → f a ≤ f b) {b a : Ordinal.{u}}
    (ha : a ≈ 0) (z : Ordinal.{u}) : schutteColumn f b a z ≈ f z :=
  equiv_intro (le_trans (schutte_column_monotone f b a z 0 z hf ha.le (le_refl z)) (schutte_column_arg0 b z f hf).le)
    (le_trans (schutte_column_arg0 b z f hf).ge (schutte_column_monotone f b 0 z a z hf (zero_least a) (le_refl z)))

/-- Rocq: `SchutteColumnFacts.proper_fix_cases`. -/
theorem proper_fix_cases (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (p q : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) (x₀ : Ordinal.{u}), AllComplete m →
      SchutteMatrixProper m p q → NormalFunction f →
      (∃ r s, (r, s) ∈ m ∧ 0 < r ∧ 0 < s ∧ r < p ∧ s < q ∧ Complete r ∧ Complete s) ∨
      (∃ b v, b < p ∧ v < q ∧ Complete v ∧ (b, v) ∈ m ∧ (b ≈ 0 ∨ v ≈ 0) ∧
        schutteMatrix f m x₀ ≈ f (v + x₀)) ∨
      (m = [] ∧ schutteMatrix f m x₀ ≈ f x₀) := by
  induction m with
  | nil => intro _ _ f x₀ _ _ _; exact .inr (.inr ⟨rfl, equiv_refl _⟩)
  | cons r m ih =>
    intro p q f x₀ hm hp hf
    obtain ⟨b, a⟩ := r
    obtain ⟨hb, ha, hm⟩ := hm
    obtain ⟨hbp, haq, hp⟩ := hp
    match ih b q f x₀ hm hp hf with
    | .inl ⟨r, s, hmem, hr, hs, hrb, hsq, hrc, hsc⟩ =>
      exact .inl ⟨r, s, .tail _ hmem, hr, hs, lt_trans hrb hbp, hsq, hrc, hsc⟩
    | .inr (.inl ⟨b', v, hb'b, hvq, hvc, hmem, hz, heq⟩) =>
      match complete_zeroDec hb, complete_zeroDec ha with
      | .inl hb₀, _ => exact (zero_lt _ (lt_of_lt_of_le hb'b hb₀)).elim
      | .inr _, .inl ha₀ =>
        have hza : a ≈ 0 := equiv_intro ha₀ (zero_least a)
        refine .inr (.inl ⟨b', v, lt_trans hb'b hbp, hvq, hvc, .tail _ hmem, hz, equiv_trans ?_ heq⟩)
        exact equiv_intro
          (schutte_matrix_monotone_func m _ f x₀ (fun _ _ h => schutte_column_monotone f b a _ a _ hf.monotone
            (le_refl a) h) hf.monotone (fun z => (col_zero_arg_le hf.monotone hza z).le))
          (schutte_matrix_monotone_func m f _ x₀ hf.monotone (fun _ _ h => schutte_column_monotone f b a _ a _
            hf.monotone (le_refl a) h) (fun z => (col_zero_arg_le hf.monotone hza z).ge))
      | .inr hb₀, .inr ha₀ => exact .inl ⟨b, a, .head _, hb₀, ha₀, hbp, haq, hb, ha⟩
    | .inr (.inr ⟨hm0, _⟩) =>
      subst hm0
      show _ ∨ (∃ b' v, b' < p ∧ v < q ∧ Complete v ∧ (b', v) ∈ [(b, a)] ∧ (b' ≈ 0 ∨ v ≈ 0) ∧
          schutteColumn f b a x₀ ≈ f (v + x₀)) ∨ _
      match complete_zeroDec hb, complete_zeroDec ha with
      | .inl hb₀, _ =>
        exact .inr (.inl ⟨b, a, hbp, haq, ha, .head _, .inl (equiv_intro hb₀ (zero_least b)), equiv_intro
          (le_trans (schutte_column_monotoneβ b 0 a x₀ f hf.monotone hb₀) (schutte_column0 f a x₀).le)
          (schutte_column_le_f b a x₀ f hf.monotone)⟩)
      | .inr _, .inl ha₀ =>
        exact .inr (.inl ⟨b, a, hbp, haq, ha, .head _, .inr (equiv_intro ha₀ (zero_least a)), equiv_intro
          (le_trans (col_zero_arg_le hf.monotone (equiv_intro ha₀ (zero_least a)) x₀).le
            (hf.monotone _ _ (le_add_left a x₀)))
          (schutte_column_le_f b a x₀ f hf.monotone)⟩)
      | .inr hb₀, .inr ha₀ => exact .inl ⟨b, a, .head _, hb₀, ha₀, hbp, haq, hb, ha⟩

/-- Rocq: `SchutteColumnFacts.schutte_matrix_lt2_aux`. -/
theorem schutte_matrix_lt2_aux (xs : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b xa : Ordinal.{u}) (ys : List (Ordinal.{u} × Ordinal.{u})) (ya y₀ : Ordinal.{u}) (hf : NormalFunction f)
    (hxs : AllComplete xs) (hb : Complete b) (hxa : Complete xa) (hys : AllComplete ys) (hya : Complete ya)
    (hy₀ : Complete y₀) (hex : ∃ r s, (r, s) ∈ ys ∧ 0 < r ∧ 0 < s ∧ Complete r ∧ Complete s)
    (hp : SchutteMatrixProper xs b (schutteMatrix f ((b, ya) :: ys) y₀)) (hxy : xa < ya) :
    schutteMatrix f ((b, xa) :: xs) 0 < schutteMatrix f ((b, ya) :: ys) y₀ := by
  have hNy := schutte_column_normal b ya f hb hya hf
  have hY := (schutte_matrix_normal ys _ hys hNy).complete y₀ hy₀
  show schutteMatrix (schutteColumn f b xa) xs 0 < schutteMatrix (schutteColumn f b ya) ys y₀
  match complete_zeroDec hb with
  | .inl hb₀ =>
    match xs, hp with
    | [], _ =>
      exact lt_of_lt_of_le ((schutte_column_normal_arg b f hb hf).increasing xa ya hya hxy)
        (le_trans (hNy.monotone 0 y₀ (zero_least y₀)) (schutte_matrix_base ys _ y₀ hNy hys))
    | _ :: _, hp => exact (lt_irrefl _ (lt_of_lt_of_le hp.1 (le_trans hb₀ (zero_least _)))).elim
  | .inr hb₀ =>
    obtain ⟨r, s, hmem, hr, hs, hrc, hsc⟩ := hex
    have hNa := schutte_column_normal b xa f hb hxa hf
    refine schutte_matrix_unreachable b _ _ xs hNa hb hxs hp hY hb₀ fun v hv hvb => ?_
    exact le_trans (schutte_column_monotone _ v _ 0 _ 0 hNa.monotone
        (schutte_column_inflationary2 b ya _ f (normal_inflationary hf) hya hY) (le_refl 0))
      (le_trans (schutte_column_fixpoint b ya _ f v xa hb hya hf hvb hxy hv hxa hY)
        (schutte_matrix_fixpoint2 ys y₀ _ r s hNy hys hy₀ hmem hr hs hrc hsc))

/-- Rocq: `SchutteColumnFacts.schutte_matrix_lt2`. -/
theorem schutte_matrix_lt2 (xs : List (Ordinal.{u} × Ordinal.{u})) (f : Ordinal.{u} → Ordinal.{u})
    (b xa : Ordinal.{u}) (ys : List (Ordinal.{u} × Ordinal.{u})) (ya y₀ : Ordinal.{u}) (hf : NormalFunction f)
    (hxs : AllComplete xs) (hb : Complete b) (hxa : Complete xa) (hys : AllComplete ys) (hya : Complete ya)
    (hy₀ : Complete y₀) (hq : ∃ q, SchutteMatrixProper ys b q)
    (hp : SchutteMatrixProper xs b (schutteMatrix f ((b, ya) :: ys) y₀)) (hxy : xa < ya) :
    schutteMatrix f ((b, xa) :: xs) 0 < schutteMatrix f ((b, ya) :: ys) y₀ := by
  obtain ⟨q, hq⟩ := hq
  have hNy := schutte_column_normal b ya f hb hya hf
  have hNa := schutte_column_normal b xa f hb hxa hf
  have hY := (schutte_matrix_normal ys _ hys hNy).complete y₀ hy₀
  match proper_fix_cases ys b q _ y₀ hys hq hNy with
  | .inl ⟨r, s, hmem, hr, hs, _, _, hrc, hsc⟩ =>
    exact schutte_matrix_lt2_aux xs f b xa ys ya y₀ hf hxs hb hxa hys hya hy₀ ⟨r, s, hmem, hr, hs, hrc, hsc⟩ hp hxy
  | .inr (.inl ⟨b', v, hb'b, _, hvc, _, _, heq⟩) =>
    show schutteMatrix (schutteColumn f b xa) xs 0 < _
    refine schutte_matrix_unreachable b _ _ xs hNa hb hxs hp hY (lt_of_le_of_lt (zero_least b') hb'b)
      fun v' hv' hv'b => ?_
    have hZ := add_complete hvc hy₀
    exact le_trans (schutte_column_monotone _ v' _ 0 _ 0 hNa.monotone heq.le (le_refl 0))
      (le_trans (schutte_column_fixpoint b ya _ f v' xa hb hya hf hv'b hxy hv' hxa hZ) heq.ge)
  | .inr (.inr ⟨hys0, _⟩) =>
    subst hys0
    show schutteMatrix (schutteColumn f b xa) xs 0 < schutteColumn f b ya y₀
    match complete_zeroDec hb with
    | .inl hb₀ =>
      match xs, hp with
      | [], _ =>
        exact lt_of_lt_of_le ((schutte_column_normal_arg b f hb hf).increasing xa ya hya hxy)
          (hNy.monotone 0 y₀ (zero_least y₀))
      | _ :: _, hp => exact (lt_irrefl _ (lt_of_lt_of_le hp.1 (le_trans hb₀ (zero_least _)))).elim
    | .inr hb₀ =>
      exact schutte_matrix_unreachable b _ _ xs hNa hb hxs hp hY hb₀ fun v hv hvb =>
        schutte_column_fixpoint b ya y₀ f v xa hb hya hf hvb hxy hv hxa hy₀

/-- Rocq: `SchutteColumnFacts.matrix_fixpoint`. -/
theorem matrix_fixpoint (m : List (Ordinal.{u} × Ordinal.{u})) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (b a q : Ordinal.{u}), NormalFunction f → AllComplete m → Complete b →
      Complete a → SchutteMatrixProper m q a → b < finalIndex q m → 0 < a →
      (∀ r, r < q → Complete r → schutteColumn f r a 0 ≤ a) → schutteMatrix f (m ++ [(b, a)]) 0 ≤ a := by
  induction m with
  | nil => intro f b a q _ _ hb _ _ hbq _ hfix; exact hfix b hbq hb
  | cons r m ih =>
    intro f b a q hf hm hb ha hp hbq ha₀ hfix
    have hNs := schutte_column_normal r.1 r.2 f hm.1 hm.2.1 hf
    refine ih _ b a r.1 hNs hm.2.2 hb ha hp.2.2 hbq ha₀ fun r₀ hr₀ hr₀c => ?_
    exact le_trans (schutte_column_monotone _ r₀ a 0 _ 0 hNs.monotone
        (schutte_column_inflationary1 r.1 a 0 f (normal_inflationary hf) ha zero_complete) (le_refl 0))
      (le_trans (schutte_column_fixpoint r.1 a 0 f r₀ r.2 hm.1 ha hf hr₀ hp.2.1 hr₀c hm.2.1 zero_complete)
        (hfix r.1 hp.1 hm.1))

/-- The lexicographic order on matrices, up to zero arguments.
Rocq: `SchutteColumnFacts.matrix_lex_lt`. -/
inductive MatrixLexLt (b : Option Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `matrix_lex_lt_zl`. -/
  | zl (xb xa : Ordinal.{u}) (xs ys) : xa ≈ 0 → MatrixLexLt b xs ys → MatrixLexLt b ((xb, xa) :: xs) ys
  /-- Rocq: `matrix_lex_lt_zr`. -/
  | zr (xs) (yb ya : Ordinal.{u}) (ys) : ya ≈ 0 → MatrixLexLt b xs ys → MatrixLexLt b xs ((yb, ya) :: ys)
  /-- Rocq: `matrix_lex_lt_nil`. -/
  | nil (yb ya : Ordinal.{u}) (ys) (v : Ordinal.{u}) : 0 < ya → b = some v → v < yb →
      MatrixLexLt b [] ((yb, ya) :: ys)
  /-- Rocq: `matrix_lex_lt_index`. -/
  | index (xb xa : Ordinal.{u}) (xs) (yb ya : Ordinal.{u}) (ys) : xb < yb → 0 < ya →
      MatrixLexLt b ((xb, xa) :: xs) ((yb, ya) :: ys)
  /-- Rocq: `matrix_lex_lt_arg`. -/
  | arg (xb xa : Ordinal.{u}) (xs) (yb ya : Ordinal.{u}) (ys) : xb ≈ yb → xa < ya →
      MatrixLexLt b ((xb, xa) :: xs) ((yb, ya) :: ys)
  /-- Rocq: `matrix_lex_lt_recurse`. -/
  | recurse (xb xa : Ordinal.{u}) (xs) (yb ya : Ordinal.{u}) (ys) : xb ≈ yb → xa ≈ ya → MatrixLexLt b xs ys →
      MatrixLexLt b ((xb, xa) :: xs) ((yb, ya) :: ys)

/-- Equality of matrices up to zero arguments. Rocq: `SchutteColumnFacts.matrix_lex_eq`. -/
inductive MatrixLexEq : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `matrix_lex_eq_zl`. -/
  | zl (xb xa : Ordinal.{u}) (xs ys) : xa ≈ 0 → MatrixLexEq xs ys → MatrixLexEq ((xb, xa) :: xs) ys
  /-- Rocq: `matrix_lex_eq_zr`. -/
  | zr (xs) (yb ya : Ordinal.{u}) (ys) : ya ≈ 0 → MatrixLexEq xs ys → MatrixLexEq xs ((yb, ya) :: ys)
  /-- Rocq: `matrix_lex_eq_nil`. -/
  | nil : MatrixLexEq [] []
  /-- Rocq: `matrix_lex_eq_recurse`. -/
  | recurse (xb xa : Ordinal.{u}) (xs) (yb ya : Ordinal.{u}) (ys) : xb ≈ yb → xa ≈ ya → MatrixLexEq xs ys →
      MatrixLexEq ((xb, xa) :: xs) ((yb, ya) :: ys)

/-- Rocq: `SchutteColumnFacts.matrix_lex_eq_symm`. -/
theorem matrix_lex_eq_symm {m n : List (Ordinal.{u} × Ordinal.{u})} (h : MatrixLexEq m n) : MatrixLexEq n m := by
  induction h with
  | zl _ _ _ _ h _ ih => exact .zr _ _ _ _ h ih
  | zr _ _ _ _ h _ ih => exact .zl _ _ _ _ h ih
  | nil => exact .nil
  | recurse _ _ _ _ _ _ hb ha _ ih => exact .recurse _ _ _ _ _ _ (equiv_symm hb) (equiv_symm ha) ih

/-- Rocq: `SchutteColumnFacts.matrix_lex_eq_lt_compose`. -/
theorem matrix_lex_eq_lt_compose {m₁ n₁ : List (Ordinal.{u} × Ordinal.{u})} (m₂ n₂ : List (Ordinal.{u} × Ordinal.{u}))
    (b : Option Ordinal.{u}) (h : MatrixLexEq m₁ n₁) (hlt : MatrixLexLt b m₂ n₂) :
    MatrixLexLt b (m₁ ++ m₂) (n₁ ++ n₂) := by
  induction h with
  | zl _ _ _ _ h _ ih => exact .zl _ _ _ _ h ih
  | zr _ _ _ _ h _ ih => exact .zr _ _ _ _ h ih
  | nil => exact hlt
  | recurse _ _ _ _ _ _ hb ha _ ih => exact .recurse _ _ _ _ _ _ hb ha ih

/-- Rocq: `SchutteColumnFacts.matrix_lex_eq_compose`. -/
theorem matrix_lex_eq_compose {m₁ n₁ : List (Ordinal.{u} × Ordinal.{u})} (m₂ n₂ : List (Ordinal.{u} × Ordinal.{u}))
    (h : MatrixLexEq m₁ n₁) (h₂ : MatrixLexEq m₂ n₂) : MatrixLexEq (m₁ ++ m₂) (n₁ ++ n₂) := by
  induction h with
  | zl _ _ _ _ h _ ih => exact .zl _ _ _ _ h ih
  | zr _ _ _ _ h _ ih => exact .zr _ _ _ _ h ih
  | nil => exact h₂
  | recurse _ _ _ _ _ _ hb ha _ ih => exact .recurse _ _ _ _ _ _ hb ha ih

/-- Rocq: `SchutteColumnFacts.matrix_lex_eq_snoc`. -/
theorem matrix_lex_eq_snoc {m n : List (Ordinal.{u} × Ordinal.{u})} (mb nb ma na : Ordinal.{u}) (h : MatrixLexEq m n)
    (hb : mb ≈ nb) (ha : ma ≈ na) : MatrixLexEq (m ++ [(mb, ma)]) (n ++ [(nb, na)]) :=
  matrix_lex_eq_compose _ _ h (.recurse _ _ _ _ _ _ hb ha .nil)

/-- Rocq: `SchutteColumnFacts.matrix_lex_eq_eq`. -/
theorem matrix_lex_eq_eq {m n : List (Ordinal.{u} × Ordinal.{u})} (h : MatrixLexEq m n) :
    AllComplete m → AllComplete n → ∀ (f : Ordinal.{u} → Ordinal.{u}) (x₀ : Ordinal.{u}), NormalFunction f →
      Complete x₀ → schutteMatrix f m x₀ ≈ schutteMatrix f n x₀ := by
  induction h with
  | zl xb xa xs ys hz _ ih =>
    intro hm hn f x₀ hf hx₀
    refine equiv_trans (equiv_intro ?_ ?_) (ih hm.2.2 hn f x₀ hf hx₀)
    · exact schutte_matrix_monotone_func xs _ f x₀
        (fun _ _ h => schutte_column_monotone f xb xa _ xa _ hf.monotone (le_refl _) h) hf.monotone
        (fun z => (col_zero_arg_le hf.monotone hz z).le)
    · exact schutte_matrix_monotone_func xs f _ x₀ hf.monotone
        (fun _ _ h => schutte_column_monotone f xb xa _ xa _ hf.monotone (le_refl _) h)
        (fun z => (col_zero_arg_le hf.monotone hz z).ge)
  | zr xs yb ya ys hz _ ih =>
    intro hm hn f x₀ hf hx₀
    refine equiv_trans (ih hm hn.2.2 f x₀ hf hx₀) (equiv_intro ?_ ?_)
    · exact schutte_matrix_monotone_func ys f _ x₀ hf.monotone
        (fun _ _ h => schutte_column_monotone f yb ya _ ya _ hf.monotone (le_refl _) h)
        (fun z => (col_zero_arg_le hf.monotone hz z).ge)
    · exact schutte_matrix_monotone_func ys _ f x₀
        (fun _ _ h => schutte_column_monotone f yb ya _ ya _ hf.monotone (le_refl _) h) hf.monotone
        (fun z => (col_zero_arg_le hf.monotone hz z).le)
  | nil => intro _ _ f x₀ _ _; exact equiv_refl _
  | recurse xb xa xs yb ya ys hb ha _ ih =>
    intro hm hn f x₀ hf hx₀
    have hNx := schutte_column_normal xb xa f hm.1 hm.2.1 hf
    have hNy := schutte_column_normal yb ya f hn.1 hn.2.1 hf
    refine equiv_trans (ih hm.2.2 hn.2.2 _ x₀ hNx hx₀) (equiv_intro ?_ ?_)
    · exact schutte_matrix_monotone_func ys _ _ x₀ hNx.monotone hNy.monotone
        (fun z => schutte_column_monotone_full f f xb xa z yb ya z hf.monotone hf.monotone (fun _ => le_refl _)
          hb.le ha.le (le_refl z))
    · exact schutte_matrix_monotone_func ys _ _ x₀ hNy.monotone hNx.monotone
        (fun z => schutte_column_monotone_full f f yb ya z xb xa z hf.monotone hf.monotone (fun _ => le_refl _)
          hb.ge ha.ge (le_refl z))

/-- Matrices differing by an argument `a ≈ 0` in their first column agree. -/
private theorem matrix_zero_head {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ a b, a ≤ b → f a ≤ f b)
    (m : List (Ordinal.{u} × Ordinal.{u})) {b a : Ordinal.{u}} (ha : a ≈ 0) (x : Ordinal.{u}) :
    schutteMatrix f ((b, a) :: m) x ≈ schutteMatrix f m x :=
  have hm := fun _ _ h => schutte_column_monotone f b a _ a _ hf (le_refl a) h
  equiv_intro (schutte_matrix_monotone_func m _ f x hm hf (fun z => (col_zero_arg_le hf ha z).le))
    (schutte_matrix_monotone_func m f _ x hf hm (fun z => (col_zero_arg_le hf ha z).ge))

/-- Matrices with equivalent first columns agree. -/
private theorem matrix_head_congr {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ a b, a ≤ b → f a ≤ f b)
    (m : List (Ordinal.{u} × Ordinal.{u})) {xb xa yb ya : Ordinal.{u}} (hb : xb ≈ yb) (ha : xa ≈ ya)
    (x : Ordinal.{u}) : schutteMatrix f ((xb, xa) :: m) x ≈ schutteMatrix f ((yb, ya) :: m) x :=
  have hmx := fun _ _ h => schutte_column_monotone f xb xa _ xa _ hf (le_refl xa) h
  have hmy := fun _ _ h => schutte_column_monotone f yb ya _ ya _ hf (le_refl ya) h
  equiv_intro
    (schutte_matrix_monotone_func m _ _ x hmx hmy
      (fun z => schutte_column_monotone_full f f _ _ z _ _ z hf hf (fun _ => le_refl _) hb.le ha.le (le_refl z)))
    (schutte_matrix_monotone_func m _ _ x hmy hmx
      (fun z => schutte_column_monotone_full f f _ _ z _ _ z hf hf (fun _ => le_refl _) hb.ge ha.ge (le_refl z)))

/-- Replacing the argument of the last column by something larger. -/
private theorem matrix_snoc_mono {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f)
    (xs : List (Ordinal.{u} × Ordinal.{u})) (hxs : AllComplete xs) (b : Ordinal.{u}) {N N' : Ordinal.{u}}
    (h : N ≤ N') : schutteMatrix f (xs ++ [(b, N)]) 0 ≤ schutteMatrix f (xs ++ [(b, N')]) 0 := by
  rw [schutte_matrix_app, schutte_matrix_app]
  exact schutte_column_monotone _ b N 0 N' 0 (schutte_matrix_normal xs f hxs hf).monotone h (le_refl 0)

/-- Rocq: `SchutteColumnFacts.matrix_matrix_fixpoint`. -/
theorem matrix_matrix_fixpoint {m n : List (Ordinal.{u} × Ordinal.{u})} {b : Ordinal.{u}}
    (h : MatrixLexLt (some b) m n) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (q : Ordinal.{u}), NormalFunction f → AllComplete m → Complete b →
      AllComplete n → SchutteMatrixProper m q (schutteMatrix f n 0) → (∃ s t, SchutteMatrixProper n s t) →
      b < finalIndex q m → schutteMatrix f (m ++ [(b, schutteMatrix f n 0)]) 0 ≤ schutteMatrix f n 0 := by
  induction h with
  | zl xb xa xs ys hz _ ih =>
    intro f q hf hm hb hn hp hst hbq
    have hm' : ∀ a b : Ordinal.{u}, a ≤ b → schutteColumn f xb xa a ≤ schutteColumn f xb xa b :=
      fun _ _ h => schutte_column_monotone f xb xa _ xa _ hf.monotone (le_refl xa) h
    exact le_trans (schutte_matrix_monotone_func (xs ++ _) _ f 0 hm' hf.monotone
      (fun z => (col_zero_arg_le hf.monotone hz z).le)) (ih f xb hf hm.2.2 hb hn hp.2.2 hst hbq)
  | zr xs yb ya ys hz _ ih =>
    intro f q hf hm hb hn hp hst hbq
    have heq := matrix_zero_head hf.monotone ys hz (f := f) (b := yb) 0
    obtain ⟨s, t, hst⟩ := hst
    exact le_trans (matrix_snoc_mono hf xs hm b heq.le)
      (le_trans (ih f q hf hm hb hn.2.2 (schutte_matrix_proper_monotone xs q q _ _ (le_refl q) heq.le hp)
        ⟨yb, t, hst.2.2⟩ hbq) heq.ge)
  | nil yb ya ys v hya hv hvb =>
    intro f _ hf _ hb hn _ _ _
    cases hv
    exact schutte_matrix_column_fix f yb b ya ys 0 hf hn.1 hb hn.2.1 hn.2.2 zero_complete hvb hya
  | index xb xa xs yb ya ys hxy hya =>
    intro f q hf hm hb hn hp _ hbq
    have hY := (schutte_matrix_normal _ f hn hf).complete 0 zero_complete
    have hNx := schutte_column_normal xb xa f hm.1 hm.2.1 hf
    refine matrix_fixpoint xs _ b _ xb hNx hm.2.2 hb hY hp.2.2 hbq
      ((schutte_matrix_normal _ f hn hf).nonzero 0) fun r hr hrc => ?_
    exact le_trans (schutte_column_monotone _ r _ 0 _ 0 hNx.monotone
        (schutte_column_inflationary1 xb _ 0 f (normal_inflationary hf) hY zero_complete) (le_refl 0))
      (le_trans (schutte_column_fixpoint xb _ 0 f r xa hm.1 hY hf hr hp.2.1 hrc hm.2.1 zero_complete)
        (schutte_matrix_column_fix f yb xb ya ys 0 hf hn.1 hm.1 hn.2.1 hn.2.2 zero_complete hxy hya))
  | arg xb xa xs yb ya ys hb' ha' =>
    intro f q hf hm hb hn hp hst hbq
    have hY := (schutte_matrix_normal _ f hn hf).complete 0 zero_complete
    have hNx := schutte_column_normal xb xa f hm.1 hm.2.1 hf
    have hNy := schutte_column_normal yb ya f hn.1 hn.2.1 hf
    obtain ⟨_, t, hst⟩ := hst
    have hv : ∃ v, Complete v ∧ schutteMatrix (schutteColumn f yb ya) ys 0 ≈ schutteColumn f yb ya v := by
      match proper_fix_cases ys yb t _ 0 hn.2.2 hst.2.2 hNy with
      | .inl ⟨u, v, hmem, hu, hv, _, _, huc, hvc⟩ =>
        exact ⟨_, hY, equiv_intro (schutte_column_inflationary2 yb ya _ f (normal_inflationary hf) hn.2.1 hY)
          (schutte_matrix_fixpoint2 ys 0 _ u v hNy hn.2.2 zero_complete hmem hu hv huc hvc)⟩
      | .inr (.inl ⟨_, a, _, _, hac, _, _, heq⟩) => exact ⟨_, add_complete hac zero_complete, heq⟩
      | .inr (.inr ⟨_, heq⟩) => exact ⟨0, zero_complete, heq⟩
    obtain ⟨v, hvc, heq⟩ := hv
    refine matrix_fixpoint xs _ b _ xb hNx hm.2.2 hb hY hp.2.2 hbq
      ((schutte_matrix_normal _ f hn hf).nonzero 0) fun r hr hrc => ?_
    have hNyx := schutte_column_normal yb xa f hn.1 hm.2.1 hf
    refine le_trans (schutte_column_monotone_full _ _ r _ 0 r _ 0 hNx.monotone hNyx.monotone
      (fun z => schutte_column_monotoneβ xb yb xa z f hf.monotone hb'.le) (le_refl r) heq.le (le_refl 0)) ?_
    exact le_trans (schutte_column_fixpoint yb ya v f r xa hn.1 hn.2.1 hf (lt_of_lt_of_le hr hb'.le) ha' hrc
      hm.2.1 hvc) heq.ge
  | recurse xb xa xs yb ya ys hb' ha' _ ih =>
    intro f q hf hm hb hn hp hst hbq
    obtain ⟨_, t, hst⟩ := hst
    have hNx := schutte_column_normal xb xa f hm.1 hm.2.1 hf
    have heq := equiv_symm (matrix_head_congr hf.monotone ys hb' ha' (f := f) 0)
    exact le_trans (matrix_snoc_mono hNx xs hm.2.2 b heq.le)
      (le_trans (ih _ xb hNx hm.2.2 hb hn.2.2 (schutte_matrix_proper_monotone xs xb xb _ _ (le_refl _) heq.le hp.2.2)
        ⟨yb, t, hst.2.2⟩ hbq) heq.ge)

/-- A syntactic check of how `schutteMatrix f xs 0` compares with `z`,
given that `z` is a fixpoint of the relevant columns.
Rocq: `SchutteColumnFacts.confirm_lt`. -/
inductive ConfirmLt : Ordering → List (Ordinal.{u} × Ordinal.{u}) → Ordinal.{u} → Prop
  /-- Rocq: `confirm_lt_nil`. -/
  | nil (z : Ordinal.{u}) : ConfirmLt .lt [] z
  /-- Rocq: `confirm_lt_lt`. -/
  | lt (o : Ordering) (b a : Ordinal.{u}) (xs) (z : Ordinal.{u}) : a < z → ConfirmLt o xs z →
      ConfirmLt o ((b, a) :: xs) z
  /-- Rocq: `confirm_lt_eq1`. -/
  | eq1 (b a : Ordinal.{u}) (xs) (z : Ordinal.{u}) : a ≈ z → TrivialMatrix xs → ConfirmLt .eq ((b, a) :: xs) z
  /-- Rocq: `confirm_lt_eq2`. -/
  | eq2 (b a : Ordinal.{u}) (xs) (z : Ordinal.{u}) : a ≈ z → NontrivialMatrix xs → ConfirmLt .gt ((b, a) :: xs) z
  /-- Rocq: `confirm_lt_gt`. -/
  | gt (b a : Ordinal.{u}) (xs) (z : Ordinal.{u}) : z < a → ConfirmLt .gt ((b, a) :: xs) z

/-- Rocq: `SchutteColumnFacts.confirm_lt_eq_mor`. -/
theorem ConfirmLt.congr {o : Ordering} {xs : List (Ordinal.{u} × Ordinal.{u})} {x y : Ordinal.{u}} (h : x ≈ y)
    (hc : ConfirmLt o xs x) : ConfirmLt o xs y := by
  induction hc with
  | nil => exact .nil y
  | lt o b a xs _ ha _ ih => exact .lt o b a xs y (lt_of_lt_of_le ha h.le) (ih h)
  | eq1 b a xs _ ha ht => exact .eq1 b a xs y (equiv_trans ha h) ht
  | eq2 b a xs _ ha ht => exact .eq2 b a xs y (equiv_trans ha h) ht
  | gt b a xs _ ha => exact .gt b a xs y (lt_of_le_of_lt h.ge ha)

/-- Rocq: `SchutteColumnFacts.ordering_correct_swap`. -/
theorem ordering_correct_swap (o : Ordering) (x y : Ordinal.{u}) :
    OrderingCorrect o.swap x y ↔ OrderingCorrect o y x :=
  match o with
  | .lt => Iff.rfl
  | .eq => ⟨equiv_symm, equiv_symm⟩
  | .gt => Iff.rfl

/-- Rocq: `SchutteColumnFacts.confirm_lt_is_correct`. -/
def ConfirmLtIsCorrect (o : Ordering) (xs : List (Ordinal.{u} × Ordinal.{u})) (z : Ordinal.{u})
    (f : Ordinal.{u} → Ordinal.{u}) (p : Ordinal.{u}) : Prop :=
  match o with
  | .lt => SchutteMatrixProper xs p z
  | .eq => schutteMatrix f xs 0 ≈ z
  | .gt => z < schutteMatrix f xs 0

/-- Rocq: `SchutteColumnFacts.confirm_lt_correct`. -/
theorem confirm_lt_correct {o : Ordering} {xs : List (Ordinal.{u} × Ordinal.{u})} {z : Ordinal.{u}}
    (hc : ConfirmLt o xs z) :
    ∀ (f : Ordinal.{u} → Ordinal.{u}) (p q : Ordinal.{u}), Complete z → Complete p → NormalFunction f →
      AllComplete xs → SchutteMatrixProper xs p q →
      (∀ b, b < p → Complete b → schutteColumn f b z 0 ≈ z) → ConfirmLtIsCorrect o xs z f p := by
  induction hc with
  | nil => intro _ _ _ _ _ _ _ _ _; exact trivial
  | lt o b a xs z haz _ ih =>
    intro f p q hz _ hf hm hpr hfix
    have hNa := schutte_column_normal b a f hm.1 hm.2.1 hf
    have hfix' : ∀ b₀, b₀ < b → Complete b₀ → schutteColumn (schutteColumn f b a) b₀ z 0 ≈ z := fun b₀ hb₀ hb₀c =>
      equiv_intro (le_trans (schutte_column_monotone _ b₀ z 0 _ 0 hNa.monotone (hfix b hpr.1 hm.1).ge (le_refl 0))
          (le_trans (schutte_column_fixpoint b z 0 f b₀ a hm.1 hz hf hb₀ haz hb₀c hm.2.1 zero_complete)
            (hfix b hpr.1 hm.1).le))
        (schutte_column_inflationary1 b₀ z 0 _ (normal_inflationary hNa) hz zero_complete)
    have := ih _ b q hz hm.1 hNa hm.2.2 hpr.2.2 hfix'
    cases o with
    | lt => exact ⟨hpr.1, haz, this⟩
    | eq => exact this
    | gt => exact this
  | eq1 b a xs z haz ht =>
    intro f p _ _ _ hf hm hpr hfix
    have hNa := schutte_column_normal b a f hm.1 hm.2.1 hf
    exact equiv_trans (trivial_matrix_eq xs _ 0 hNa ht) (equiv_trans
      (equiv_intro (schutte_column_monotone f b a 0 z 0 hf.monotone haz.le (le_refl 0))
        (schutte_column_monotone f b z 0 a 0 hf.monotone haz.ge (le_refl 0))) (hfix b hpr.1 hm.1))
  | eq2 b a xs z haz hnt =>
    intro f _ _ _ _ hf hm _ _
    exact lt_of_le_of_lt haz.ge (nontrivial_matrix_member_lt [] xs f b a hf trivial hm.1 hm.2.1 hm.2.2 hnt)
  | gt b a xs z hza =>
    intro f _ _ _ _ hf hm _ _
    have hNa := schutte_column_normal b a f hm.1 hm.2.1 hf
    exact lt_of_lt_of_le hza (le_trans (schutte_column_inflationary1 b a 0 f (normal_inflationary hf) hm.2.1
      zero_complete) (schutte_matrix_base xs _ 0 hNa hm.2.2))

/-- A syntactic comparison of two matrices. Rocq: `SchutteColumnFacts.schutte_matrix_compare`. -/
inductive SchutteMatrixCompare :
    Ordering → (Ordinal.{u} → Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `mat_comp_nil_nil`. -/
  | nil_nil (f) : SchutteMatrixCompare .eq f [] []
  /-- Rocq: `mat_comp_nil_left`. -/
  | nil_left (f) (b a : Ordinal.{u}) (n) : 0 < a → SchutteMatrixCompare .lt f [] ((b, a) :: n)
  /-- Rocq: `mat_comp_nil_right`. -/
  | nil_right (f) (b a : Ordinal.{u}) (m) : 0 < a → SchutteMatrixCompare .gt f ((b, a) :: m) []
  /-- Rocq: `mat_comp_zl`. -/
  | zl (o f m) (b a : Ordinal.{u}) (n) : a ≈ 0 → SchutteMatrixCompare o f m n →
      SchutteMatrixCompare o f ((b, a) :: m) n
  /-- Rocq: `mat_comp_zr`. -/
  | zr (o f m n) (b a : Ordinal.{u}) : a ≈ 0 → SchutteMatrixCompare o f m n →
      SchutteMatrixCompare o f m ((b, a) :: n)
  /-- Rocq: `mat_comp_eq`. -/
  | eq (o f m) (mb ma : Ordinal.{u}) (n) (nb na : Ordinal.{u}) : mb ≈ nb → ma ≈ na →
      SchutteMatrixCompare o (schutteColumn f mb ma) m n → SchutteMatrixCompare o f ((mb, ma) :: m) ((nb, na) :: n)
  /-- Rocq: `mat_comp_index_lt`. -/
  | index_lt (o f m) (mb ma : Ordinal.{u}) (n) (nb na : Ordinal.{u}) : mb < nb → 0 < na →
      ConfirmLt o ((mb, ma) :: m) (schutteMatrix f ((nb, na) :: n) 0) →
      SchutteMatrixCompare o f ((mb, ma) :: m) ((nb, na) :: n)
  /-- Rocq: `mat_comp_index_gt`. -/
  | index_gt (o f m) (mb ma : Ordinal.{u}) (n) (nb na : Ordinal.{u}) : nb < mb → 0 < ma →
      ConfirmLt o.swap ((nb, na) :: n) (schutteMatrix f ((mb, ma) :: m) 0) →
      SchutteMatrixCompare o f ((mb, ma) :: m) ((nb, na) :: n)
  /-- Rocq: `mat_comp_arg_lt`. -/
  | arg_lt (o f m) (mb ma : Ordinal.{u}) (n) (nb na : Ordinal.{u}) : mb ≈ nb → ma < na →
      ConfirmLt o m (schutteMatrix f ((nb, na) :: n) 0) →
      SchutteMatrixCompare o f ((mb, ma) :: m) ((nb, na) :: n)
  /-- Rocq: `mat_comp_arg_gt`. -/
  | arg_gt (o f m) (mb ma : Ordinal.{u}) (n) (nb na : Ordinal.{u}) : mb ≈ nb → na < ma →
      ConfirmLt o.swap n (schutteMatrix f ((mb, ma) :: m) 0) →
      SchutteMatrixCompare o f ((mb, ma) :: m) ((nb, na) :: n)

/-- `b < succ c` gives `b < d` whenever `c < d`. -/
private theorem lt_of_lt_succ_of_lt {b c d : Ordinal.{u}} (h : b < succ c) (hcd : c < d) : b < d :=
  let ⟨_, hb⟩ := lt_elim h
  lt_of_le_of_lt hb hcd

/-- Rocq: `SchutteColumnFacts.schutte_matrix_compare_correct`. -/
theorem schutte_matrix_compare_correct {o : Ordering} {f : Ordinal.{u} → Ordinal.{u}}
    {m n : List (Ordinal.{u} × Ordinal.{u})} (h : SchutteMatrixCompare o f m n) :
    ∀ p q s t : Ordinal.{u}, NormalFunction f → AllComplete m → AllComplete n → SchutteMatrixProper m p q →
      SchutteMatrixProper n s t → OrderingCorrect o (schutteMatrix f m 0) (schutteMatrix f n 0) := by
  induction h with
  | nil_nil f => intro _ _ _ _ _ _ _ _ _; exact equiv_refl _
  | nil_left f b a n ha =>
    intro _ _ _ _ hf _ hn _ _
    have hNa := schutte_column_normal b a f hn.1 hn.2.1 hf
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hn.2.1 zero_complete) (lt_of_lt_of_le ha (add_zero a).ge))
      (le_trans (schutte_column_le_f b a 0 f hf.monotone) (schutte_matrix_base n _ 0 hNa hn.2.2))
  | nil_right f b a m ha =>
    intro _ _ _ _ hf hm _ _ _
    have hNa := schutte_column_normal b a f hm.1 hm.2.1 hf
    exact lt_of_lt_of_le (hf.increasing _ _ (add_complete hm.2.1 zero_complete) (lt_of_lt_of_le ha (add_zero a).ge))
      (le_trans (schutte_column_le_f b a 0 f hf.monotone) (schutte_matrix_base m _ 0 hNa hm.2.2))
  | zl o f m b a n ha _ ih =>
    intro p q s t hf hm hn hp hpn
    exact OrderingCorrect.congr (equiv_symm (matrix_zero_head hf.monotone m ha 0)) (equiv_refl _)
      (ih b q s t hf hm.2.2 hn hp.2.2 hpn)
  | zr o f m n b a ha _ ih =>
    intro p q s t hf hm hn hp hpn
    exact OrderingCorrect.congr (equiv_refl _) (equiv_symm (matrix_zero_head hf.monotone n ha 0))
      (ih p q b t hf hm hn.2.2 hp hpn.2.2)
  | eq o f m mb ma n nb na hb ha _ ih =>
    intro p q s t hf hm hn hp hpn
    exact OrderingCorrect.congr (equiv_refl _) (matrix_head_congr hf.monotone n hb ha 0)
      (ih mb q nb t (schutte_column_normal mb ma f hm.1 hm.2.1 hf) hm.2.2 hn.2.2 hp.2.2 hpn.2.2)
  | index_lt o f m mb ma n nb na hmn hna hc =>
    intro p q s t hf hm hn hp hpn
    have hY := (schutte_matrix_normal _ f hn hf).complete 0 zero_complete
    have hcor := confirm_lt_correct hc f (succ mb) q hY (succ_complete hm.1) hf hm ⟨succ_lt mb, hp.2.1, hp.2.2⟩
      fun b hb hbc => equiv_intro
        (schutte_matrix_column_fix f nb b na n 0 hf hn.1 hbc hn.2.1 hn.2.2 zero_complete
          (lt_of_lt_succ_of_lt hb hmn) hna)
        (schutte_column_inflationary1 b _ 0 f (normal_inflationary hf) hY zero_complete)
    cases o with
    | lt =>
      exact schutte_matrix_lt1 m f mb ma n nb na 0 hf hm.2.2 hm.1 hm.2.1 hn.2.2 hn.1 hn.2.1 zero_complete
        hcor.2.2 hna hmn hcor.2.1
    | eq => exact hcor
    | gt => exact hcor
  | index_gt o f m mb ma n nb na hnm hma hc =>
    intro p q s t hf hm hn hp hpn
    have hX := (schutte_matrix_normal _ f hm hf).complete 0 zero_complete
    have hcor := confirm_lt_correct hc f (succ nb) t hX (succ_complete hn.1) hf hn ⟨succ_lt nb, hpn.2.1, hpn.2.2⟩
      fun b hb hbc => equiv_intro
        (schutte_matrix_column_fix f mb b ma m 0 hf hm.1 hbc hm.2.1 hm.2.2 zero_complete
          (lt_of_lt_succ_of_lt hb hnm) hma)
        (schutte_column_inflationary1 b _ 0 f (normal_inflationary hf) hX zero_complete)
    cases o with
    | lt => exact hcor
    | eq => exact equiv_symm hcor
    | gt =>
      exact schutte_matrix_lt1 n f nb na m mb ma 0 hf hn.2.2 hn.1 hn.2.1 hm.2.2 hm.1 hm.2.1 zero_complete
        hcor.2.2 hma hnm hcor.2.1
  | arg_lt o f m mb ma n nb na hb ha hc =>
    intro p q s t hf hm hn hp hpn
    have hY := (schutte_matrix_normal _ f hn hf).complete 0 zero_complete
    have hNm := schutte_column_normal mb ma f hm.1 hm.2.1 hf
    have hNn := schutte_column_normal nb na f hn.1 hn.2.1 hf
    have hNnm := schutte_column_normal nb ma f hn.1 hm.2.1 hf
    have hcor := confirm_lt_correct hc _ mb q hY hm.1 hNm hm.2.2 hp.2.2 fun b hb' hbc => equiv_intro
      (schutte_matrix_fixpoint1 n 0 _ (fun x => schutteColumn (schutteColumn f mb ma) b x 0) hn.2.2 zero_complete
        hNn (schutte_column_normal_arg b _ hbc hNm) fun z hz =>
          le_trans (schutte_column_monotone_func _ _ b _ 0 _ 0 hNm.monotone hNnm.monotone
            (fun w => schutte_column_monotoneβ mb nb ma w f hf.monotone hb.le) (le_refl _) (le_refl 0))
            (schutte_column_fixpoint nb na z f b ma hn.1 hn.2.1 hf (lt_of_lt_of_le hb' hb.le) ha hbc hm.2.1 hz))
      (schutte_column_inflationary1 b _ 0 _ (normal_inflationary hNm) hY zero_complete)
    cases o with
    | lt =>
      exact lt_of_le_of_lt (schutte_matrix_monotone_func m _ _ 0 hNm.monotone hNnm.monotone
          (fun w => schutte_column_monotoneβ mb nb ma w f hf.monotone hb.le))
        (schutte_matrix_lt2 m f nb ma n na 0 hf hm.2.2 hn.1 hm.2.1 hn.2.2 hn.2.1 zero_complete ⟨t, hpn.2.2⟩
          (schutte_matrix_proper_monotone m mb nb _ _ hb.le (le_refl _) hcor) ha)
    | eq => exact hcor
    | gt => exact hcor
  | arg_gt o f m mb ma n nb na hb ha hc =>
    intro p q s t hf hm hn hp hpn
    have hX := (schutte_matrix_normal _ f hm hf).complete 0 zero_complete
    have hNm := schutte_column_normal mb ma f hm.1 hm.2.1 hf
    have hNn := schutte_column_normal nb na f hn.1 hn.2.1 hf
    have hNmn := schutte_column_normal mb na f hm.1 hn.2.1 hf
    have hcor := confirm_lt_correct hc _ nb t hX hn.1 hNn hn.2.2 hpn.2.2 fun b hb' hbc => equiv_intro
      (schutte_matrix_fixpoint1 m 0 _ (fun x => schutteColumn (schutteColumn f nb na) b x 0) hm.2.2 zero_complete
        hNm (schutte_column_normal_arg b _ hbc hNn) fun z hz =>
          le_trans (schutte_column_monotone_func _ _ b _ 0 _ 0 hNn.monotone hNmn.monotone
            (fun w => schutte_column_monotoneβ nb mb na w f hf.monotone hb.ge) (le_refl _) (le_refl 0))
            (schutte_column_fixpoint mb ma z f b na hm.1 hm.2.1 hf (lt_of_lt_of_le hb' hb.ge) ha hbc hn.2.1 hz))
      (schutte_column_inflationary1 b _ 0 _ (normal_inflationary hNn) hX zero_complete)
    cases o with
    | lt => exact hcor
    | eq => exact equiv_symm hcor
    | gt =>
      exact lt_of_le_of_lt (schutte_matrix_monotone_func n _ _ 0 hNn.monotone hNmn.monotone
          (fun w => schutte_column_monotoneβ nb mb na w f hf.monotone hb.ge))
        (schutte_matrix_lt2 n f mb na m ma 0 hf hn.2.2 hm.1 hn.2.1 hm.2.2 hm.2.1 zero_complete ⟨q, hp.2.2⟩
          (schutte_matrix_proper_monotone n nb mb _ _ hb.ge (le_refl _) hcor) ha)

end Ordinal

end ConstructiveOrdinals
