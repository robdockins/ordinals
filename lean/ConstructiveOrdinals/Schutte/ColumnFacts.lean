import ConstructiveOrdinals.Schutte.Column
import ConstructiveOrdinals.AckermannTower

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

end Ordinal

end ConstructiveOrdinals
