import ConstructiveOrdinals.Schutte.ColumnFacts

/-!
# Absorption of Schütte columns

A column `(b, a)` followed by a strictly higher column `(β, α)` is absorbed:
the higher column built over `schutteColumn P b a` enumerates a final segment
of what it enumerates over `P`, namely the part above `a`. This file proves
that fact constructively, for ordinals, in terms of the critical predicates
`SchutteCritical`; the actual offset of the shift is supplied by the caller
(it is computed on notations). It also proves that adjacent columns of equal
height merge.

Main results:
- `schutte_column_merge`: `(c, a), (c, a') ↦ (c, a + a')`.
- `absorb_critical`: in the principal regime, the critical points of `(β, α)`
  over `schutteColumn P b a` are those over `P` that exceed `a`.
- `absorb_shift`: hence the column over `schutteColumn P b a` is the column
  over `P` shifted by the least argument whose value exceeds `a`.

Ported from the Rocq file `SchutteAbsorb.v`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-- Rocq: `SchutteAbsorb.addOrd_lt_cases'`. -/
theorem add_lt_cases' {t y a : Ordinal.{u}} (h : a < t + y) : a < t ∨ ∃ j : y, a ≤ t + y j := by
  rw [add_unfold] at h
  match lub_lt h with
  | .inl h => exact .inl h
  | .inr h =>
    obtain ⟨j, hj⟩ := sup_lt h
    obtain ⟨_, hj⟩ := lt_elim hj
    exact .inr ⟨j, hj⟩

/-- Rocq: `SchutteAbsorb.col_normal_mono`. -/
theorem col_normal_mono {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) :
    ∀ a b, a ≤ b → f a ≤ f b :=
  hf.monotone

/-- Rocq: `SchutteAbsorb.zero_lt_one`. -/
theorem zero_lt_one : (0 : Ordinal.{u}) < 1 := succ_lt 0

theorem one_complete : Complete (1 : Ordinal.{u}) := succ_complete zero_complete

/-- `1 > a` means `a ≤ 0`. -/
theorem le_zero_of_lt_one {a : Ordinal.{u}} (h : a < 1) : a ≤ 0 :=
  let ⟨_, h⟩ := lt_elim h; h

/-- Monotonicity of a column in its last argument. -/
theorem colx_mono {P : Ordinal.{u} → Ordinal.{u}} (hP : NormalFunction P) (β a : Ordinal.{u})
    {x x' : Ordinal.{u}} (h : x ≤ x') : schutteColumn P β a x ≤ schutteColumn P β a x' :=
  schutte_column_monotone P β a x a x' hP.monotone (le_refl a) h

/-- A column at height 0 is a translation of its base. Rocq: `SchutteAbsorb.col0`. -/
theorem col0 (P : Ordinal.{u} → Ordinal.{u}) (a x : Ordinal.{u}) (_hP : NormalFunction P) :
    schutteColumn P 0 a x ≈ P (a + x) :=
  schutte_column0 P a x

/-- Columns respect pointwise inequality of normal bases. Rocq: `SchutteAbsorb.col_base_le`. -/
theorem col_base_le (f g : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) (hf : NormalFunction f)
    (hg : NormalFunction g) (h : ∀ y, Complete y → f y ≤ g y) (hβ : Complete β) (hα : Complete α)
    (hx : Complete x) : schutteColumn f β α x ≤ schutteColumn g β α x :=
  schutte_column_monotone_func' β α x f g hf hg h hβ hα hx

/-- The fixpoint clause, specialised: values of `(β, α)` are fixed by
`schutteColumn P β a` for `a < α`. Rocq: `SchutteAbsorb.col_value_fix`. -/
theorem col_value_fix (P : Ordinal.{u} → Ordinal.{u}) (β α a x : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hα : Complete α) (ha : Complete a) (hx : Complete x) (hβ0 : 0 < β) (hlt : a < α) :
    schutteColumn P β a (schutteColumn P β α x) ≤ schutteColumn P β α x :=
  calc schutteColumn P β a (schutteColumn P β α x)
      ≤ schutteColumn P β a (schutteColumn P β α x + 0) := colx_mono hP β a (add_zero _).ge
    _ ≤ schutteColumn (schutteColumn P β a) 0 (schutteColumn P β α x) 0 := (schutte_column0 _ _ 0).ge
    _ ≤ schutteColumn P β α x := schutte_column_fixpoint β α x P 0 a hβ hα hP hβ0 hlt zero_complete ha hx

/-! ## Merging equal heights -/

/-- Rocq: `SchutteAbsorb.schutte_column_merge_le`. -/
theorem schutte_column_merge_le (c : Ordinal.{u}) : ∀ (x y a : Ordinal.{u}) (P : Ordinal.{u} → Ordinal.{u}),
    NormalFunction P → Complete c → Complete a → Complete x → Complete y →
    schutteColumn (schutteColumn P c a) c x y ≤ schutteColumn P c (a + x) y := by
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro y
  induction y using ltRec with
  | ind y ihy =>
  intro a P hP hc ha hx hy
  have hQ := schutte_column_normal c a P hc ha hP
  have hax := add_complete ha hx
  have hV : Complete (schutteColumn P c (a + x) y) := (schutte_column_normal c _ P hc hax hP).complete y hy
  rw [schutte_column_unroll]
  refine lub_least ?_ (sup_least fun b4 => sup_least fun a4 => ?_)
  · -- the base term
    match complete_zeroDec hx with
    | .inl hx0 =>
      calc schutteColumn P c a (x + y) ≤ schutteColumn P c a y :=
            hQ.monotone _ _ (le_trans (add_le_add hx0 (le_refl y)) (zero_add y).le)
        _ ≤ schutteColumn P c (a + x) y :=
            schutte_column_monotone P c a y _ y hP.monotone (le_add_right a x) (le_refl y)
    | .inr hx0 =>
      match complete_zeroDec hc with
      | .inl hc0 =>
        calc schutteColumn P c a (x + y) ≤ schutteColumn P 0 a (x + y) :=
              schutte_column_monotoneβ c 0 a _ P hP.monotone hc0
          _ ≈ P (a + (x + y)) := schutte_column0 P a _
          _ ≈ P (a + x + y) := equiv_intro (hP.monotone _ _ (add_assoc a x y).le)
              (hP.monotone _ _ (add_assoc a x y).ge)
          _ ≈ schutteColumn P 0 (a + x) y := (schutte_column0 P _ y).symm
          _ ≤ schutteColumn P c (a + x) y := schutte_column_monotoneβ 0 c _ y P hP.monotone (zero_least c)
      | .inr hc0 =>
        calc schutteColumn P c a (x + y) ≤ schutteColumn P c a (schutteColumn P c (a + x) y) := by
              refine colx_mono hP c a ?_
              calc x + y ≤ a + x + y := add_le_add (le_add_left a x) (le_refl y)
                _ ≤ P (a + x + y) := normal_inflationary hP _ (add_complete hax hy)
                _ ≤ schutteColumn P c (a + x) y := schutte_column_le_f c (a + x) y P hP.monotone
          _ ≤ schutteColumn P c (a + x) y := by
              refine col_value_fix P c (a + x) a y hP hc hax ha hy hc0 ?_
              exact lt_of_le_of_lt (add_zero a).ge (add_lt_add_left a hx0)
  · refine normal_fix_least (schutte_column_normal_arg (c b4) _ (complete_subord hc b4)
      (schutte_column_normal c (x a4) _ hc (complete_subord hx a4) hQ)) _ _ hV ?_ ?_
    · exact limit_least fun i => lt_of_le_of_lt (ihy (y i) (index_lt y i) a P hP hc ha hx (complete_subord hy i))
        (schutte_column_increasing c (a + x) y (y i) P hP hc hax hy (index_lt y i))
    · have ha4 := complete_subord hx a4
      calc schutteColumn (schutteColumn (schutteColumn P c a) c (x a4)) (c b4) (schutteColumn P c (a + x) y) 0
          ≤ schutteColumn (schutteColumn P c (a + x a4)) (c b4) (schutteColumn P c (a + x) y) 0 :=
            col_base_le _ _ _ _ _ (schutte_column_normal c _ _ hc ha4 hQ)
              (schutte_column_normal c _ P hc (add_complete ha ha4) hP)
              (fun w hw => ihx (x a4) (index_lt x a4) w a P hP hc ha ha4 hw) (complete_subord hc b4) hV zero_complete
        _ ≤ schutteColumn P c (a + x) y :=
            schutte_column_fixpoint c (a + x) y P (c b4) (a + x a4) hc hax hP (index_lt c b4)
              (add_lt_add_left a (index_lt x a4)) (complete_subord hc b4) (add_complete ha ha4) hy

/-! ## Additively principal ordinals and the principal regime -/

/-- Rocq: `SchutteAbsorb.principal`. -/
def Principal (z : Ordinal.{u}) : Prop := ∀ c, c < z → c + z ≤ z

/-- Rocq: `SchutteAbsorb.principal_eq`. -/
theorem principal_eq {z z' : Ordinal.{u}} (E : z ≈ z') (H : Principal z) : Principal z' := fun c hc =>
  le_trans (add_le_add (le_refl c) E.ge) (le_trans (H c (lt_of_lt_of_le hc E.ge)) E.le)

/-- `z` with `φ_z(0) ≤ z` at height 1 over any normal base is principal.
Rocq: `SchutteAbsorb.principal_of_col1`. -/
theorem principal_of_col1 (P : Ordinal.{u} → Ordinal.{u}) (z : Ordinal.{u}) (hP : NormalFunction P)
    (hz : Complete z) (H : schutteColumn P 1 z 0 ≤ z) : Principal z := fun c hc => by
  obtain ⟨i, hi⟩ := lt_elim hc
  have hzi := complete_subord hz i
  calc c + z ≤ z i + z := add_le_add hi (le_refl z)
    _ ≤ P (z i + z) := normal_inflationary hP _ (add_complete hzi hz)
    _ ≤ schutteColumn P 1 (z i) z := schutte_column_le_f 1 (z i) z P hP.monotone
    _ ≤ schutteColumn P 1 (z i) (schutteColumn P 1 z 0) :=
        colx_mono hP 1 (z i) (schutte_column_inflationary1 1 z 0 P (normal_inflationary hP) hz zero_complete)
    _ ≤ schutteColumn P 1 z 0 :=
        col_value_fix P 1 z (z i) 0 hP one_complete hz hzi zero_complete zero_lt_one (index_lt z i)
    _ ≤ z := H

/-- A fixpoint of `schutteColumn P b · 0` is fixed by every `schutteColumn P b a`
with `a` below it. Rocq: `SchutteAbsorb.col_fix_below`. -/
theorem col_fix_below (P : Ordinal.{u} → Ordinal.{u}) (b a z : Ordinal.{u}) (hP : NormalFunction P)
    (hb : Complete b) (ha : Complete a) (hz : Complete z) (hb0 : 0 < b) (H : schutteColumn P b z 0 ≤ z)
    (haz : a < z) : schutteColumn P b a z ≤ z :=
  le_trans (colx_mono hP b a (schutte_column_inflationary1 b z 0 P (normal_inflationary hP) hz zero_complete))
    (le_trans (col_value_fix P b z a 0 hP hb hz ha zero_complete hb0 haz) H)

/-- Rocq: `SchutteAbsorb.principal_succ`. -/
theorem principal_succ (a z : Ordinal.{u}) (hp : Principal z) (h1 : 1 < z) (ha : a < z) : succ a < z :=
  calc succ a ≤ a + 1 := le_trans (succ_monotone (add_zero a).ge) (add_succ a 0).ge
    _ < a + z := add_lt_add_left a h1
    _ ≤ z := hp a ha

/-- Rocq: `SchutteAbsorb.fix_gt1`. -/
theorem fix_gt1 (P : Ordinal.{u} → Ordinal.{u}) (z : Ordinal.{u}) (hP : NormalFunction P) (hz : Complete z)
    (H : P z ≤ z) : 1 < z :=
  have H1 : 1 + z ≤ z := le_trans (onePlus_least_normal hP z hz) H
  have H0 : 1 ≤ z := le_trans (le_add_right 1 z) H1
  lt_of_le_of_lt (add_zero 1).ge
    (lt_of_lt_of_le (add_lt_add_left 1 zero_lt_one) (le_trans (add_le_add (le_refl 1) H0) H1))

/-- Fixpoints of `P` are principal. Rocq: `SchutteAbsorb.Prin`. -/
def Prin (P : Ordinal.{u} → Ordinal.{u}) : Prop := ∀ z, Complete z → P z ≤ z → Principal z

/-- The principal regime for a column at height `β` over `P`. Rocq: `SchutteAbsorb.Reg`. -/
def Reg (P : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) : Prop := Prin P ∨ 1 < β

/-- Rocq: `SchutteAbsorb.crit_base`. -/
theorem crit_base (P : Ordinal.{u} → Ordinal.{u}) (β α z : Ordinal.{u}) (hP : NormalFunction P)
    (_hβ : Complete β) (_hα : Complete α) (_hz : Complete z) (hβ0 : 0 < β) (hα0 : 0 < α)
    (H : SchutteCritical P β α z) : P z ≤ z :=
  calc P z ≤ P (0 + (z + 0)) := hP.monotone _ _ (le_trans (add_zero z).ge (zero_add _).ge)
    _ ≤ schutteColumn P β 0 (z + 0) := schutte_column_le_f β 0 (z + 0) P hP.monotone
    _ ≤ schutteColumn (schutteColumn P β 0) 0 z 0 := (schutte_column0 _ z 0).ge
    _ ≤ z := (H 0 0 zero_complete zero_complete hβ0 hα0).le

/-- Rocq: `SchutteAbsorb.crit_principal`. -/
theorem crit_principal (P : Ordinal.{u} → Ordinal.{u}) (β α z : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hα : Complete α) (hz : Complete z) (hreg : Reg P β) (hβ0 : 0 < β) (hα0 : 0 < α)
    (H : SchutteCritical P β α z) : Principal z :=
  match hreg with
  | .inl hpr => hpr z hz (crit_base P β α z hP hβ hα hz hβ0 hα0 H)
  | .inr h1 => principal_of_col1 P z hP hz
      (le_trans (col_base_le P (schutteColumn P β 0) 1 z 0 hP (schutte_column_normal β 0 P hβ zero_complete hP)
          (fun y _ => (schutte_column_arg0 β y P hP.monotone).ge) one_complete hz zero_complete)
        (H 1 0 one_complete zero_complete h1 hα0).le)

/-- Rocq: `SchutteAbsorb.crit_value`. -/
theorem crit_value (P : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hα : Complete α) (hx : Complete x) (hβ0 : 0 < β) (hα0 : 0 < α) :
    SchutteCritical P β α (schutteColumn P β α x) :=
  (schutte_column_enumerates P β α hP hβ hα hβ0 hα0).included x hx

/-- A common upper bound below `β` for two ordinals below a complete `β`.
Rocq: `SchutteAbsorb.below_join`. -/
theorem below_join (β b b' : Ordinal.{u}) (hβ : Complete β) (hb : b < β) (hb' : b' < β) :
    ∃ c, Complete c ∧ b ≤ c ∧ b' ≤ c ∧ c < β := by
  obtain ⟨i, hi⟩ := lt_elim hb
  obtain ⟨j, hj⟩ := lt_elim hb'
  cases β with
  | mk B g =>
  obtain ⟨hdir, _, hc⟩ := hβ
  obtain ⟨k, hk1, hk2⟩ := hdir i j
  exact ⟨g k, hc k, le_trans hi hk1, le_trans hj hk2, index_lt (mk B g) k⟩

/-! ## Absorption: critical points -/

/-- (⇐) In the principal regime, a critical point of `(β, α)` over `P` that is
principal and lies above `a` is also critical over `schutteColumn P b a`, for
any `b < β`. By induction on `β`, then `α`; the shift bound `UB` for smaller
`α` keeps the lower columns under control, and equal heights are reduced to
`schutte_column_merge_le` through a common upper bound below `β` (no
comparison of heights is needed). Rocq: `SchutteAbsorb.absorb_critical`. -/
theorem absorb_critical (β : Ordinal.{u}) : Complete β → ∀ α : Ordinal.{u}, Complete α →
    ∀ (P : Ordinal.{u} → Ordinal.{u}) (b a z : Ordinal.{u}),
    NormalFunction P → Complete b → Complete a → Complete z → b < β → Reg P β → Principal z → 1 < z → a < z →
    SchutteCritical P β α z → SchutteCritical (schutteColumn P b a) β α z := by
  induction β using ltRec with
  | ind β ihβ =>
  intro hβ α
  induction α using ltRec with
  | ind α ihα =>
  intro hα P b a z hP hb ha hz hbβ hreg hpz h1z haz hcrit
  have hβ0 : 0 < β := lt_of_le_of_lt (zero_least b) hbβ
  have hz0 : 0 < z := lt_trans zero_lt_one h1z
  have hQ : NormalFunction (schutteColumn P b a) := schutte_column_normal b a P hb ha hP
  intro b' a' hb' ha' hb'β ha'α
  have hα0 : 0 < α := lt_of_le_of_lt (zero_least a') ha'α
  have hQa' := schutte_column_normal β a' _ hβ ha' hQ
  refine equiv_intro ?_ (schutte_column_inflationary1 _ _ _ _ (normal_inflationary hQa') hz zero_complete)
  match complete_zeroDec ha' with
  | .inl ha'0 =>
    -- a' = 0: compare with the merged column at a common height c
    obtain ⟨c, hc, hbc, hb'c, hcβ⟩ := below_join β b b' hβ hbβ hb'β
    calc schutteColumn (schutteColumn (schutteColumn P b a) β a') b' z 0
        ≤ schutteColumn (schutteColumn P b a) b' z 0 :=
          col_base_le _ _ b' z 0 hQa' hQ
            (fun y _ => le_trans (schutte_column_monotone _ β a' y 0 y hQ.monotone ha'0 (le_refl y))
              (schutte_column_arg0 β y _ hQ.monotone).le) hb' hz zero_complete
      _ ≤ schutteColumn (schutteColumn P c a) c z 0 :=
          schutte_column_monotone_full _ _ b' z 0 c z 0 hQ.monotone (schutte_column_normal c a P hc ha hP).monotone
            (fun y => schutte_column_monotoneβ b c a y P hP.monotone hbc) hb'c (le_refl z) (le_refl 0)
      _ ≤ schutteColumn P c (a + z) 0 := schutte_column_merge_le c z 0 a P hP hc ha hz zero_complete
      _ ≤ schutteColumn P c z 0 := schutte_column_monotone P c _ 0 z 0 hP.monotone (hpz a haz) (le_refl 0)
      _ ≤ schutteColumn (schutteColumn P β 0) c z 0 :=
          col_base_le P _ c z 0 hP (schutte_column_normal β 0 P hβ zero_complete hP)
            (fun y _ => (schutte_column_arg0 β y P hP.monotone).ge) hc hz zero_complete
      _ ≤ z := (hcrit c 0 hc zero_complete hcβ hα0).le
  | .inr ha'0 =>
    have hka : succ a < z := principal_succ a z hpz h1z haz
    have hsa := succ_complete ha
    -- the shift bound for (β, a')
    have UB : ∀ y, Complete y →
        schutteColumn (schutteColumn P b a) β a' y ≤ schutteColumn P β a' (succ a + y) := by
      intro y
      induction y using ltRec with
      | ind y ihy =>
      intro hy
      have hsy := add_complete hsa hy
      have hv : Complete (schutteColumn P β a' (succ a + y)) :=
        (schutte_column_normal β a' P hβ ha' hP).complete _ hsy
      have hcv := crit_value P β a' (succ a + y) hP hβ ha' hsy hβ0 ha'0
      refine (schutte_column_enumerates _ β a' hQ hβ ha' hβ0 ha'0).least y _ hy hv ?_ ?_
      · refine ihα a' ha'α ha' P b a _ hP hb ha hv hbβ hreg (crit_principal P β a' _ hP hβ ha' hv hreg hβ0 ha'0 hcv)
          (fix_gt1 P _ hP hv (crit_base P β a' _ hP hβ ha' hv hβ0 ha'0 hcv)) ?_ hcv
        exact lt_of_lt_of_le (succ_lt a) (le_trans (le_add_right (succ a) y)
          (schutte_column_inflationary2 β a' _ P (normal_inflationary hP) ha' hsy))
      · intro y' hy'
        obtain ⟨i, hi⟩ := lt_elim hy'
        calc schutteColumn (schutteColumn P b a) β a' y' ≤ schutteColumn (schutteColumn P b a) β a' (y i) :=
              colx_mono hQ β a' hi
          _ ≤ schutteColumn P β a' (succ a + y i) := ihy (y i) (index_lt y i) (complete_subord hy i)
          _ < schutteColumn P β a' (succ a + y) :=
              schutte_column_increasing β a' _ _ P hP hβ ha' hsy (add_lt_add_left (succ a) (index_lt y i))
    match complete_zeroDec hb' with
    | .inl hb'0 =>
      calc schutteColumn (schutteColumn (schutteColumn P b a) β a') b' z 0
          ≤ schutteColumn (schutteColumn (schutteColumn P b a) β a') 0 z 0 :=
            schutte_column_monotoneβ b' 0 z 0 _ hQa'.monotone hb'0
        _ ≤ schutteColumn (schutteColumn P b a) β a' (z + 0) := (schutte_column0 _ z 0).le
        _ ≤ schutteColumn (schutteColumn P b a) β a' z := colx_mono hQ β a' (add_zero z).le
        _ ≤ schutteColumn P β a' (succ a + z) := UB z hz
        _ ≤ schutteColumn P β a' z := colx_mono hP β a' (hpz (succ a) hka)
        _ ≤ schutteColumn P β a' (z + 0) := colx_mono hP β a' (add_zero z).ge
        _ ≤ schutteColumn (schutteColumn P β a') 0 z 0 := (schutte_column0 _ z 0).ge
        _ ≤ z := (hcrit 0 a' zero_complete ha' hβ0 ha'α).le
    | .inr hb'0 =>
      -- b' > 0: a 0-column over P' = (β, a') absorbed at height b'
      have hP' : NormalFunction (schutteColumn P β a') := schutte_column_normal β a' P hβ ha' hP
      have hsc := hcrit b' a' hb' ha' hb'β ha'α
      have hsup : SchutteSupercritical (schutteColumn P β a') b' z :=
        (schutte_supercritical_alt _ b' z hP' hb' hz hb'0).mpr hsc
      obtain ⟨_, hcz⟩ := hsup
      have hprin : Prin (schutteColumn P β a') := fun w hw hfw =>
        principal_eq (equiv_intro hfw (normal_inflationary hP' w hw))
          (crit_principal P β a' _ hP hβ ha' (hP'.complete w hw) hreg hβ0 ha'0
            (crit_value P β a' w hP hβ ha' hw hβ0 ha'0))
      have hres : SchutteCritical (schutteColumn (schutteColumn P β a') 0 (succ a)) b' z z :=
        ihβ b' hb'β hb' z hz _ 0 (succ a) z hP' zero_complete hsa hz hb'0 (.inl hprin) hpz h1z hka hcz
      have hN0 := schutte_column_normal 0 (succ a) _ zero_complete hsa hP'
      have hfinal := (schutte_supercritical_alt _ b' z hN0 hb' hz hb'0).mp ⟨hz0, hres⟩
      calc schutteColumn (schutteColumn (schutteColumn P b a) β a') b' z 0
          ≤ schutteColumn (schutteColumn (schutteColumn P β a') 0 (succ a)) b' z 0 :=
            col_base_le _ _ b' z 0 hQa' hN0
              (fun y hy => le_trans (UB y hy) (schutte_column0 _ (succ a) y).ge) hb' hz zero_complete
        _ ≤ z := hfinal.le

/-- Rocq: `SchutteAbsorb.col_ge_base`. -/
theorem col_ge_base (P : Ordinal.{u} → Ordinal.{u}) (b a y : Ordinal.{u}) (hP : NormalFunction P) :
    P y ≤ schutteColumn P b a y :=
  le_trans (hP.monotone _ _ (le_add_left a y)) (schutte_column_le_f b a y P hP.monotone)

/-- (⇒) Critical points over `schutteColumn P b a` are critical over `P` and lie
above `a`. Rocq: `SchutteAbsorb.absorb_critical_inv`. -/
theorem absorb_critical_inv (P : Ordinal.{u} → Ordinal.{u}) (β α b a z : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hα : Complete α) (hb : Complete b) (ha : Complete a) (hz : Complete z)
    (hβ0 : 0 < β) (hα0 : 0 < α) (H : SchutteCritical (schutteColumn P b a) β α z) :
    SchutteCritical P β α z ∧ a < z := by
  have hQ := schutte_column_normal b a P hb ha hP
  refine ⟨fun b' a' hb' ha' hb'β ha'α => equiv_intro ?_
    (schutte_column_inflationary1 _ _ _ _ (normal_inflationary (schutte_column_normal β a' P hβ ha' hP))
      hz zero_complete), ?_⟩
  · refine le_trans ?_ (H b' a' hb' ha' hb'β ha'α).le
    exact col_base_le _ _ b' z 0 (schutte_column_normal β a' P hβ ha' hP) (schutte_column_normal β a' _ hβ ha' hQ)
      (fun y hy => col_base_le P _ β a' y hP hQ (fun w _ => col_ge_base P b a w hP) hβ ha' hy) hb' hz zero_complete
  · have hQz := crit_base _ β α z hQ hβ hα hz hβ0 hα0 H
    have hz0 : 0 < z := lt_of_lt_of_le (hQ.nonzero z) hQz
    calc a ≤ a + 0 := (add_zero a).ge
      _ < a + z := add_lt_add_left a hz0
      _ ≤ P (a + z) := normal_inflationary hP _ (add_complete ha hz)
      _ ≤ schutteColumn P b a z := schutte_column_le_f b a z P hP.monotone
      _ ≤ z := hQz

/-! ## Absorption as a shift -/

/-- The column over `schutteColumn P b a` is the column over `P` shifted by `s`,
the least argument whose value exceeds `a` (hypotheses `hs1`, `hs2`).
Rocq: `SchutteAbsorb.absorb_shift`. -/
theorem absorb_shift (P : Ordinal.{u} → Ordinal.{u}) (β α b a s : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hα : Complete α) (hb : Complete b) (ha : Complete a) (hs : Complete s)
    (hbβ : b < β) (hα0 : 0 < α) (hreg : Reg P β) (hs1 : a < schutteColumn P β α s)
    (hs2 : ∀ z, Complete z → SchutteCritical P β α z → a < z → schutteColumn P β α s ≤ z) :
    ∀ x, Complete x → schutteColumn (schutteColumn P b a) β α x ≈ schutteColumn P β α (s + x) := by
  have hβ0 : 0 < β := lt_of_le_of_lt (zero_least b) hbβ
  have hQ := schutte_column_normal b a P hb ha hP
  have EQ := schutte_column_enumerates _ β α hQ hβ hα hβ0 hα0
  have EP := schutte_column_enumerates P β α hP hβ hα hβ0 hα0
  intro x
  induction x using ltRec with
  | ind x ih =>
  intro hx
  have hsx := add_complete hs hx
  have hv : Complete (schutteColumn P β α (s + x)) := (schutte_column_normal β α P hβ hα hP).complete _ hsx
  have hw : Complete (schutteColumn (schutteColumn P b a) β α x) :=
    (schutte_column_normal β α _ hβ hα hQ).complete x hx
  refine equiv_intro ?_ ?_
  · have hcv := crit_value P β α (s + x) hP hβ hα hsx hβ0 hα0
    refine EQ.least x _ hx hv ?_ ?_
    · exact absorb_critical β hβ α hα P b a _ hP hb ha hv hbβ hreg
        (crit_principal P β α _ hP hβ hα hv hreg hβ0 hα0 hcv)
        (fix_gt1 P _ hP hv (crit_base P β α _ hP hβ hα hv hβ0 hα0 hcv))
        (lt_of_lt_of_le hs1 (colx_mono hP β α (le_add_right s x))) hcv
    · intro y hy
      obtain ⟨i, hi⟩ := lt_elim hy
      calc schutteColumn (schutteColumn P b a) β α y ≤ schutteColumn (schutteColumn P b a) β α (x i) :=
            colx_mono hQ β α hi
        _ ≤ schutteColumn P β α (s + x i) := (ih (x i) (index_lt x i) (complete_subord hx i)).le
        _ < schutteColumn P β α (s + x) :=
            schutte_column_increasing β α _ _ P hP hβ hα hsx (add_lt_add_left s (index_lt x i))
  · obtain ⟨hcw, haw⟩ := absorb_critical_inv P β α b a _ hP hβ hα hb ha hw hβ0 hα0 (EQ.included x hx)
    refine EP.least (s + x) _ hsx hw hcw fun y hy => ?_
    match add_lt_cases' hy with
    | .inl hy1 =>
      exact lt_of_lt_of_le (schutte_column_increasing β α s y P hP hβ hα hs hy1) (hs2 _ hw hcw haw)
    | .inr ⟨j, hj⟩ =>
      calc schutteColumn P β α y ≤ schutteColumn P β α (s + x j) := colx_mono hP β α hj
        _ ≈ schutteColumn (schutteColumn P b a) β α (x j) := (ih (x j) (index_lt x j) (complete_subord hx j)).symm
        _ < schutteColumn (schutteColumn P b a) β α x :=
            schutte_column_increasing β α x (x j) _ hQ hβ hα hx (index_lt x j)

/-! ## Merging equal heights: the other direction -/

/-- Rocq: `SchutteAbsorb.schutte_column_merge_ge`. -/
theorem schutte_column_merge_ge (c : Ordinal.{u}) : ∀ (x y a : Ordinal.{u}) (P : Ordinal.{u} → Ordinal.{u}),
    NormalFunction P → Complete c → Complete a → Complete x → Complete y →
    schutteColumn P c (a + x) y ≤ schutteColumn (schutteColumn P c a) c x y := by
  intro x
  induction x using ltRec with
  | ind x ihx =>
  intro y
  induction y using ltRec with
  | ind y ihy =>
  intro a P hP hc ha hx hy
  have hQ := schutte_column_normal c a P hc ha hP
  have hW : Complete (schutteColumn (schutteColumn P c a) c x y) := (schutte_column_normal c x _ hc hx hQ).complete y hy
  have hWb : schutteColumn P c a (x + y) ≤ schutteColumn (schutteColumn P c a) c x y :=
    schutte_column_le_f c x y _ hQ.monotone
  match complete_zeroDec hx with
  | .inl hx0 =>
    calc schutteColumn P c (a + x) y ≤ schutteColumn P c a y :=
          schutte_column_monotone P c _ y a y hP.monotone (le_trans (add_le_add (le_refl a) hx0) (add_zero a).le)
            (le_refl y)
      _ ≤ schutteColumn P c a (x + y) := colx_mono hP c a (le_add_left x y)
      _ ≤ _ := hWb
  | .inr hx0 =>
  have hax := add_complete ha hx
  rw [schutte_column_unroll P c (a + x) y]
  refine lub_least ?_ (sup_least fun b4 => sup_least fun a4 => ?_)
  · calc P (a + x + y) ≤ P (a + (x + y)) := hP.monotone _ _ (add_assoc a x y).ge
      _ ≤ schutteColumn P c a (x + y) := schutte_column_le_f c a (x + y) P hP.monotone
      _ ≤ _ := hWb
  · have ha4 := complete_subord hax a4
    have hb4 := complete_subord hc b4
    have hc0 : 0 < c := lt_of_le_of_lt (zero_least _) (index_lt c b4)
    have hN4 := schutte_column_normal c ((a + x) a4) P hc ha4 hP
    refine normal_fix_least (schutte_column_normal_arg (c b4) _ hb4 hN4) _ _ hW ?_ ?_
    · exact limit_least fun i => lt_of_le_of_lt (ihy (y i) (index_lt y i) a P hP hc ha hx (complete_subord hy i))
        (schutte_column_increasing c x y (y i) _ hQ hc hx hy (index_lt y i))
    · match add_lt_cases' (index_lt (a + x) a4) with
      | .inl h =>
        -- below a: the target is a value of `schutteColumn P c a`
        have hfixW : schutteColumn P c a (schutteColumn (schutteColumn P c a) c x y) ≤
            schutteColumn (schutteColumn P c a) c x y :=
          le_trans (schutte_column_arg0 c _ (schutteColumn P c a) hQ.monotone).ge
            (col_value_fix (schutteColumn P c a) c x 0 y hQ hc hx zero_complete hy hc0 hx0)
        calc schutteColumn (schutteColumn P c ((a + x) a4)) (c b4) (schutteColumn (schutteColumn P c a) c x y) 0
            ≤ schutteColumn (schutteColumn P c ((a + x) a4)) (c b4)
                (schutteColumn P c a (schutteColumn (schutteColumn P c a) c x y)) 0 :=
              schutte_column_monotone _ (c b4) _ 0 _ 0 hN4.monotone
                (schutte_column_inflationary2 c a _ P (normal_inflationary hP) ha hW) (le_refl 0)
          _ ≤ schutteColumn P c a (schutteColumn (schutteColumn P c a) c x y) :=
              schutte_column_fixpoint c a _ P (c b4) ((a + x) a4) hc ha hP (index_lt c b4) h hb4 ha4 hW
          _ ≤ _ := hfixW
      | .inr ⟨j, hj⟩ =>
        have hxj := complete_subord hx j
        calc schutteColumn (schutteColumn P c ((a + x) a4)) (c b4) (schutteColumn (schutteColumn P c a) c x y) 0
            ≤ schutteColumn (schutteColumn P c (a + x j)) (c b4) (schutteColumn (schutteColumn P c a) c x y) 0 :=
              schutte_column_monotone_full _ _ (c b4) _ 0 (c b4) _ 0 hN4.monotone
                (schutte_column_normal c _ P hc (add_complete ha hxj) hP).monotone
                (fun w => schutte_column_monotone P c _ w _ w hP.monotone hj (le_refl w))
                (le_refl _) (le_refl _) (le_refl _)
          _ ≤ schutteColumn (schutteColumn (schutteColumn P c a) c (x j)) (c b4)
                (schutteColumn (schutteColumn P c a) c x y) 0 :=
              col_base_le _ _ (c b4) _ 0 (schutte_column_normal c _ P hc (add_complete ha hxj) hP)
                (schutte_column_normal c _ _ hc hxj hQ)
                (fun w hw => ihx (x j) (index_lt x j) w a P hP hc ha hxj hw) hb4 hW zero_complete
          _ ≤ schutteColumn (schutteColumn P c a) c x y :=
              schutte_column_fixpoint c x y _ (c b4) (x j) hc hx hQ (index_lt c b4) (index_lt x j) hb4 hxj hy

/-- Adjacent columns of equal height merge. Rocq: `SchutteAbsorb.schutte_column_merge`. -/
theorem schutte_column_merge (c x y a : Ordinal.{u}) (P : Ordinal.{u} → Ordinal.{u}) (hP : NormalFunction P)
    (hc : Complete c) (ha : Complete a) (hx : Complete x) (hy : Complete y) :
    schutteColumn (schutteColumn P c a) c x y ≈ schutteColumn P c (a + x) y :=
  equiv_intro (schutte_column_merge_le c x y a P hP hc ha hx hy) (schutte_column_merge_ge c x y a P hP hc ha hx hy)

/-! ## The low regime: a height-1 column over a translation

Over the base `y ↦ d + y`, with `ω^m ≤ d < ω^(m+1)`, the Veblen functions of
positive index are those of `1 + y` shifted in index by `m`: the first
fixpoints of `d + ·` are `ω^(m+1) + y`. This is the case excluded by
`absorb_critical` (`d + ·` is not `Prin`, and `β = 1`). -/

/-- Rocq: `SchutteAbsorb.low_regime_veblen`. -/
theorem low_regime_veblen (e : Ordinal.{u}) : ∀ (y d m : Ordinal.{u}),
    Complete d → Complete m → Complete e → Complete y → 0 < e →
    ω ^ m ≤ d → d < ω ^ succ m → veblen (d + ·) e y ≈ ω ^ (m + e) + y := by
  induction e using ltRec with
  | ind e ihe =>
  intro y
  induction y using ltRec with
  | ind y ihy =>
  intro d m hd hm he hy he0 hmd hdm
  have hω : Complete ω := omega_complete
  have hd0 : 0 < d := lt_of_lt_of_le (pow_pos ω m) hmd
  have hdn : NormalFunction (d + ·) := normal_addOrd d hd hd0
  have hme := add_complete hm he
  have hpme : Complete (ω ^ (m + e)) := pow_complete omega_gt0 hω hme
  have hdlt : d < ω ^ (m + e) := lt_of_lt_of_le hdm (pow_le_pow_right ω
    (le_trans (succ_monotone (add_zero m).ge) (le_trans (add_succ m 0).ge (add_le_add (le_refl m) (succ_least he0)))))
  refine equiv_intro ?_ ?_
  · rw [veblen_unroll]
    refine lub_least (add_le_add (le_of_lt hdlt) (le_refl y)) (sup_least fun i => ?_)
    have hi := complete_subord he i
    have hV : Complete (ω ^ (m + e) + y) := add_complete hpme hy
    refine normal_fix_least (veblen_normal hdn (e i) hi) _ _ hV ?_ ?_
    · exact limit_least fun j => lt_of_le_of_lt
        (ihy (y j) (index_lt y j) d m hd hm he (complete_subord hy j) he0 hmd hdm).le
        (add_lt_add_left _ (index_lt y j))
    · match complete_zeroDec hi with
      | .inl hi0 =>
        calc veblen (d + ·) (e i) (ω ^ (m + e) + y) ≤ veblen (d + ·) 0 (ω ^ (m + e) + y) :=
              veblen_monotone_first hdn.monotone 0 (e i) _ hi0
          _ ≈ d + (ω ^ (m + e) + y) := veblen_zero _ _
          _ ≈ d + ω ^ (m + e) + y := add_assoc _ _ _
          _ ≤ ω ^ (m + e) + y :=
              add_le_add (additively_closed_collapse (powOmega_additively_closed hme) hdlt) (le_refl y)
      | .inr hi0 =>
        calc veblen (d + ·) (e i) (ω ^ (m + e) + y) ≈ ω ^ (m + e i) + (ω ^ (m + e) + y) :=
              ihe (e i) (index_lt e i) _ d m hd hm hi hV hi0 hmd hdm
          _ ≈ ω ^ (m + e i) + ω ^ (m + e) + y := add_assoc _ _ _
          _ ≤ ω ^ (m + e) + y :=
              add_le_add (pow_add_collapse hme (add_lt_add_left m (index_lt e i))) (le_refl y)
  · -- compare with the Veblen hierarchy of 1 + y from index m
    have h1 : NormalFunction (1 + ·) := onePlus_normal
    calc ω ^ (m + e) + y ≈ veblen (1 + ·) (m + e) y := (veblen_onePlus (m + e) hme y hy).symm
      _ ≈ schutteColumn (1 + ·) 1 (m + e) y := (schutte_column_veblen (m + e) y _ h1 hme hy).symm
      _ ≈ schutteColumn (schutteColumn (1 + ·) 1 m) 1 e y :=
          (schutte_column_merge 1 e y m _ h1 one_complete hm he hy).symm
      _ ≤ schutteColumn (d + ·) 1 e y :=
          col_base_le _ _ 1 e y (schutte_column_normal 1 m _ one_complete hm h1) hdn
            (fun w hw => le_trans (schutte_column_veblen m w _ h1 hm hw).le
              (le_trans (veblen_onePlus m hm w hw).le (add_le_add hmd (le_refl w)))) one_complete he hy
      _ ≈ veblen (d + ·) e y := schutte_column_veblen e y _ hdn he hy

/-! ## The principal regime along a matrix -/

/-- Rocq: `SchutteAbsorb.Prin_col`. -/
theorem Prin_col (P : Ordinal.{u} → Ordinal.{u}) (b a : Ordinal.{u}) (hP : NormalFunction P) (H : Prin P) :
    Prin (schutteColumn P b a) := fun z hz hfz =>
  H z hz (le_trans (col_ge_base P b a z hP) hfz)

/-- Rocq: `SchutteAbsorb.Prin_col_high`. -/
theorem Prin_col_high (P : Ordinal.{u} → Ordinal.{u}) (b a : Ordinal.{u}) (hP : NormalFunction P)
    (hb : Complete b) (ha : Complete a) (h1 : 1 < b) (ha0 : 0 < a) : Prin (schutteColumn P b a) :=
  fun z hz hfz =>
    have hb0 : 0 < b := lt_trans zero_lt_one h1
    have hN := schutte_column_normal b a P hb ha hP
    principal_eq (equiv_intro hfz (normal_inflationary hN z hz))
      (crit_principal P b a _ hP hb ha (hN.complete z hz) (.inr h1) hb0 ha0 (crit_value P b a z hP hb ha hz hb0 ha0))

/-- Rocq: `SchutteAbsorb.Reg_col`. -/
theorem Reg_col (P : Ordinal.{u} → Ordinal.{u}) (β b a : Ordinal.{u}) (hP : NormalFunction P) :
    Reg P β → Reg (schutteColumn P b a) β
  | .inl h => .inl (Prin_col P b a hP h)
  | .inr h => .inr h

/-- Rocq: `SchutteAbsorb.Prin_matrix`. -/
theorem Prin_matrix : ∀ (L : List (Ordinal.{u} × Ordinal.{u})) (P : Ordinal.{u} → Ordinal.{u}),
    NormalFunction P → AllComplete L → (Prin P ∨ ∃ b a, (b, a) ∈ L ∧ 1 < b ∧ 0 < a) →
    Prin (schutteMatrix P L)
  | [], _, _, _, H =>
    match H with
    | .inl h => h
    | .inr ⟨_, _, hm, _⟩ => nomatch hm
  | (b, a) :: L, P, hP, ⟨hb, ha, hL⟩, H =>
    Prin_matrix L _ (schutte_column_normal b a P hb ha hP) hL
      (match H with
       | .inl h => .inl (Prin_col P b a hP h)
       | .inr ⟨b', a', hm, h1, h2⟩ =>
         match hm with
         | .head _ => .inl (Prin_col_high P _ _ hP hb ha h1 h2)
         | .tail _ hm => .inr ⟨b', a', hm, h1, h2⟩)

/-! ## Iterated absorption -/

/-- Rocq: `SchutteAbsorb.cols_below`. -/
def ColsBelow (β z : Ordinal.{u}) : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => True
  | p :: L => p.1 < β ∧ p.2 < z ∧ ColsBelow β z L

/-- Absorbing a whole list of lower columns keeps critical points whose value
exceeds every absorbed entry. Rocq: `SchutteAbsorb.absorb_critical_list`. -/
theorem absorb_critical_list : ∀ (L : List (Ordinal.{u} × Ordinal.{u})) (β α : Ordinal.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (z : Ordinal.{u}),
    NormalFunction G → Complete β → Complete α → Complete z → AllComplete L →
    Reg G β → Principal z → 1 < z → ColsBelow β z L →
    SchutteCritical G β α z → SchutteCritical (schutteMatrix G L) β α z
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, hc => hc
  | p :: L, β, α, G, z, hG, hβ, hα, hz, ⟨hbc, hac, hL⟩, hreg, hp, h1, ⟨hbβ, haz, hb⟩, hc =>
    absorb_critical_list L β α _ z (schutte_column_normal p.1 p.2 G hbc hac hG) hβ hα hz hL
      (Reg_col G β p.1 p.2 hG hreg) hp h1 hb
      (absorb_critical β hβ α hα G p.1 p.2 z hG hbc hac hz hbβ hreg hp h1 haz hc)

/-- Rocq: `SchutteAbsorb.absorb_critical_list_inv`. -/
theorem absorb_critical_list_inv : ∀ (L : List (Ordinal.{u} × Ordinal.{u})) (β α : Ordinal.{u})
    (G : Ordinal.{u} → Ordinal.{u}) (z : Ordinal.{u}),
    NormalFunction G → Complete β → Complete α → Complete z → AllComplete L → 0 < β → 0 < α →
    SchutteCritical (schutteMatrix G L) β α z →
    SchutteCritical G β α z ∧ ∀ b a, (b, a) ∈ L → a < z
  | [], _, _, _, _, _, _, _, _, _, _, _, hc => ⟨hc, fun _ _ h => nomatch h⟩
  | (b0, a0) :: L, β, α, G, z, hG, hβ, hα, hz, ⟨hbc, hac, hL⟩, hβ0, hα0, hc =>
    let ⟨h1, h2⟩ := absorb_critical_list_inv L β α _ z (schutte_column_normal b0 a0 G hbc hac hG) hβ hα hz hL
      hβ0 hα0 hc
    let ⟨h3, h4⟩ := absorb_critical_inv G β α b0 a0 z hG hβ hα hbc hac hz hβ0 hα0 h1
    ⟨h3, fun b a hin =>
      match hin with
      | .head _ => h4
      | .tail _ hin => h2 b a hin⟩

/-! ## Shifted enumeration, generically -/

/-- If the critical points of `(β, α)` over `Q` are those over `P` that satisfy
an upward-closed `U`, the column over `Q` is the column over `P` shifted by
the least `s` whose value satisfies `U`. Rocq: `SchutteAbsorb.shift_gen`. -/
theorem shift_gen (P Q : Ordinal.{u} → Ordinal.{u}) (β α s : Ordinal.{u}) (U : Ordinal.{u} → Prop)
    (hP : NormalFunction P) (hQ : NormalFunction Q) (hβ : Complete β) (hα : Complete α) (hs : Complete s)
    (hβ0 : 0 < β) (hα0 : 0 < α) (hreg : Reg P β) (hUup : ∀ a b, a ≤ b → U a → U b)
    (hfwd : ∀ z, Complete z → SchutteCritical Q β α z → SchutteCritical P β α z ∧ U z)
    (hbwd : ∀ z, Complete z → Principal z → 1 < z → SchutteCritical P β α z → U z → SchutteCritical Q β α z)
    (hs1 : U (schutteColumn P β α s))
    (hs2 : ∀ z, Complete z → SchutteCritical P β α z → U z → schutteColumn P β α s ≤ z) :
    ∀ x, Complete x → schutteColumn Q β α x ≈ schutteColumn P β α (s + x) := by
  have EQ := schutte_column_enumerates Q β α hQ hβ hα hβ0 hα0
  have EP := schutte_column_enumerates P β α hP hβ hα hβ0 hα0
  intro x
  induction x using ltRec with
  | ind x ih =>
  intro hx
  have hsx := add_complete hs hx
  have hv : Complete (schutteColumn P β α (s + x)) := (schutte_column_normal β α P hβ hα hP).complete _ hsx
  have hw : Complete (schutteColumn Q β α x) := (schutte_column_normal β α Q hβ hα hQ).complete x hx
  refine equiv_intro ?_ ?_
  · have hcv := crit_value P β α (s + x) hP hβ hα hsx hβ0 hα0
    refine EQ.least x _ hx hv ?_ ?_
    · exact hbwd _ hv (crit_principal P β α _ hP hβ hα hv hreg hβ0 hα0 hcv)
        (fix_gt1 P _ hP hv (crit_base P β α _ hP hβ hα hv hβ0 hα0 hcv)) hcv
        (hUup _ _ (colx_mono hP β α (le_add_right s x)) hs1)
    · intro y hy
      obtain ⟨i, hi⟩ := lt_elim hy
      calc schutteColumn Q β α y ≤ schutteColumn Q β α (x i) := colx_mono hQ β α hi
        _ ≤ schutteColumn P β α (s + x i) := (ih (x i) (index_lt x i) (complete_subord hx i)).le
        _ < schutteColumn P β α (s + x) :=
            schutte_column_increasing β α _ _ P hP hβ hα hsx (add_lt_add_left s (index_lt x i))
  · obtain ⟨hcw, huw⟩ := hfwd _ hw (EQ.included x hx)
    refine EP.least (s + x) _ hsx hw hcw fun y hy => ?_
    match add_lt_cases' hy with
    | .inl hy1 =>
      exact lt_of_lt_of_le (schutte_column_increasing β α s y P hP hβ hα hs hy1) (hs2 _ hw hcw huw)
    | .inr ⟨j, hj⟩ =>
      calc schutteColumn P β α y ≤ schutteColumn P β α (s + x j) := colx_mono hP β α hj
        _ ≈ schutteColumn Q β α (x j) := (ih (x j) (index_lt x j) (complete_subord hx j)).symm
        _ < schutteColumn Q β α x := schutte_column_increasing β α x (x j) _ hQ hβ hα hx (index_lt x j)

/-- Rocq: `SchutteAbsorb.cols_below_intro`. -/
theorem cols_below_intro (β z : Ordinal.{u}) : ∀ L : List (Ordinal.{u} × Ordinal.{u}),
    (∀ b a, (b, a) ∈ L → b < β ∧ a < z) → ColsBelow β z L
  | [], _ => trivial
  | (b, a) :: L, H =>
    let ⟨h1, h2⟩ := H b a (.head _)
    ⟨h1, h2, cols_below_intro β z L fun b' a' hin => H b' a' (.tail _ hin)⟩

/-- The list form used by the normalizer: absorbing `L` (all heights below `β`)
into `(β, α)` shifts by the least `s` whose value exceeds `m`, where "above
`m`" means "above every absorbed entry". Rocq: `SchutteAbsorb.absorb_shift_list`. -/
theorem absorb_shift_list (G : Ordinal.{u} → Ordinal.{u}) (L : List (Ordinal.{u} × Ordinal.{u}))
    (β α m s : Ordinal.{u}) (hG : NormalFunction G) (hL : AllComplete L) (hβ : Complete β) (hα : Complete α)
    (hm : Complete m) (hs : Complete s) (hβ0 : 0 < β) (hα0 : 0 < α) (hreg : Reg G β)
    (hbelow : ∀ b a, (b, a) ∈ L → b < β)
    (hmax : ∀ z, (∀ b a, (b, a) ∈ L → a < z) ↔ m < z)
    (hs1 : m < schutteColumn G β α s)
    (hs2 : ∀ y, y < s → schutteColumn G β α y ≤ m) :
    ∀ x, Complete x → schutteColumn (schutteMatrix G L) β α x ≈ schutteColumn G β α (s + x) := by
  have _hm := hm
  have EP := schutte_column_enumerates G β α hG hβ hα hβ0 hα0
  refine shift_gen G (schutteMatrix G L) β α s (fun z => m < z) hG (schutte_matrix_normal L G hL hG) hβ hα hs
    hβ0 hα0 hreg (fun a b hab ha => lt_of_lt_of_le ha hab) ?_ ?_ hs1 ?_
  · intro z hz hc
    obtain ⟨h1, h2⟩ := absorb_critical_list_inv L β α G z hG hβ hα hz hL hβ0 hα0 hc
    exact ⟨h1, (hmax z).mp h2⟩
  · intro z hz hp h1 hc hmz
    exact absorb_critical_list L β α G z hG hβ hα hz hL hreg hp h1
      (cols_below_intro β z L fun b a hin => ⟨hbelow b a hin, (hmax z).mpr hmz b a hin⟩) hc
  · intro z hz hc hmz
    exact EP.least s z hs hz hc fun y hy => lt_of_le_of_lt (hs2 y hy) hmz

/-! ## Comparing a matrix against the values of another

Used to compute offsets on notations: `Mlt Y X` is the lexicographic order on
column lists, first columns first (heights, then entries). If `Y < X` then
values of `Y` with small entries lie below every value of `X` (`nest`); if
`X < Y` then values of `Y` are fixpoints of `X` (`fix_gt`). -/

/-- Rocq: `SchutteAbsorb.mlt`. -/
inductive Mlt : List (Ordinal.{u} × Ordinal.{u}) → List (Ordinal.{u} × Ordinal.{u}) → Prop
  /-- Rocq: `SchutteAbsorb.mlt_nil`. -/
  | nil (c : Ordinal.{u} × Ordinal.{u}) (X : List (Ordinal.{u} × Ordinal.{u})) : Mlt [] (c :: X)
  /-- Rocq: `SchutteAbsorb.mlt_height`. -/
  | height (g d h e : Ordinal.{u}) (Y X : List (Ordinal.{u} × Ordinal.{u})) :
      g < h → Mlt ((g, d) :: Y) ((h, e) :: X)
  /-- Rocq: `SchutteAbsorb.mlt_entry`. -/
  | entry (h d e : Ordinal.{u}) (Y X : List (Ordinal.{u} × Ordinal.{u})) :
      d < e → Mlt ((h, d) :: Y) ((h, e) :: X)
  /-- Rocq: `SchutteAbsorb.mlt_cons`. -/
  | cons (c : Ordinal.{u} × Ordinal.{u}) (Y X : List (Ordinal.{u} × Ordinal.{u})) :
      Mlt Y X → Mlt (c :: Y) (c :: X)

/-- Heights strictly decrease along the list. Rocq: `SchutteAbsorb.desc`. -/
def Desc : List (Ordinal.{u} × Ordinal.{u}) → Prop
  | [] => True
  | p :: L => (∀ b' a', (b', a') ∈ L → b' < p.1) ∧ Desc L

/-- Rocq: `SchutteAbsorb.poscols`. -/
def PosCols (L : List (Ordinal.{u} × Ordinal.{u})) : Prop := ∀ b a, (b, a) ∈ L → 0 < b ∧ 0 < a

/-- Rocq: `SchutteAbsorb.poscols_tail`. -/
theorem poscols_tail (c : Ordinal.{u} × Ordinal.{u}) (L : List (Ordinal.{u} × Ordinal.{u}))
    (H : PosCols (c :: L)) : PosCols L := fun b a hin => H b a (.tail _ hin)

/-- Rocq: `SchutteAbsorb.crit_eq`. -/
theorem crit_eq (P : Ordinal.{u} → Ordinal.{u}) (β α z z' : Ordinal.{u}) (hP : NormalFunction P)
    (hβ : Complete β) (hz' : Complete z') (E : z ≈ z') (H : SchutteCritical P β α z) :
    SchutteCritical P β α z' := fun b a hb ha hbβ haα =>
  have hF := schutte_column_normal β a P hβ ha hP
  equiv_intro
    (le_trans (schutte_column_monotone _ b z' 0 z 0 hF.monotone E.ge (le_refl 0))
      (le_trans (H b a hb ha hbβ haα).le E.le))
    (schutte_column_inflationary1 b z' 0 _ (normal_inflationary hF) hz' zero_complete)

/-- Rocq: `SchutteAbsorb.crit_mono_α`. -/
theorem crit_mono_α (P : Ordinal.{u} → Ordinal.{u}) (β α α' z : Ordinal.{u}) (hle : α' ≤ α)
    (H : SchutteCritical P β α z) : SchutteCritical P β α' z := fun b a hb ha hbβ haα =>
  H b a hb ha hbβ (lt_of_lt_of_le haα hle)

/-- The value of a positive column list starting with `(h, e)` is critical for
`(h, e)`. Rocq: `SchutteAbsorb.crit_head`. -/
theorem crit_head (G : Ordinal.{u} → Ordinal.{u}) (h e : Ordinal.{u}) (X : List (Ordinal.{u} × Ordinal.{u}))
    (w : Ordinal.{u}) (hG : NormalFunction G) (hh : Complete h) (he : Complete e) (hX : AllComplete X)
    (hw : Complete w) (hpos : PosCols ((h, e) :: X)) :
    SchutteCritical G h e (schutteMatrix G ((h, e) :: X) w) := by
  obtain ⟨hh0, he0⟩ := hpos h e (.head _)
  have hN := schutte_column_normal h e G hh he hG
  match X, hX, hpos with
  | [], _, _ => exact crit_value G h e w hG hh he hw hh0 he0
  | (r, s) :: X, hX, hpos =>
    have hM := schutte_matrix_normal ((r, s) :: X) _ hX hN
    have hz := hM.complete w hw
    obtain ⟨hr0, hs0⟩ := hpos r s (.tail _ (.head _))
    have hfix := schutte_matrix_fixpoint2 ((r, s) :: X) w _ r s hN hX hw (.head _) hr0 hs0 hX.1 hX.2.1
    exact crit_eq G h e _ _ hG hh hz (equiv_intro hfix (normal_inflationary hN _ hz)) (crit_value G h e _ hG hh he hz hh0 he0)

/-- Lowering the entry at the same height. Rocq: `SchutteAbsorb.crit_lower_entry`. -/
theorem crit_lower_entry (G : Ordinal.{u} → Ordinal.{u}) (h d e z : Ordinal.{u}) (hG : NormalFunction G)
    (hh : Complete h) (hd : Complete d) (_he : Complete e) (hz : Complete z) (hde : d < e)
    (H : SchutteCritical G h e z) : SchutteCritical (schutteColumn G h d) h 1 z := fun b a hb ha hbh ha1 =>
  have hGd := schutte_column_normal h d G hh hd hG
  have hGda := schutte_column_normal h a _ hh ha hGd
  equiv_intro
    (le_trans
      (col_base_le _ _ b z 0 hGda hGd
        (fun y _ => le_trans (schutte_column_monotone _ h a y 0 y hGd.monotone (le_zero_of_lt_one ha1) (le_refl y))
          (schutte_column_arg0 h y _ hGd.monotone).le) hb hz zero_complete)
      (H b d hb hd hbh hde).le)
    (schutte_column_inflationary1 b z 0 _ (normal_inflationary hGda) hz zero_complete)

/-- Closure under a list of lower columns with small entries. Rocq: `SchutteAbsorb.close_list`. -/
theorem close_list (L : List (Ordinal.{u} × Ordinal.{u})) (G : Ordinal.{u} → Ordinal.{u}) (h z : Ordinal.{u})
    (hG : NormalFunction G) (hh : Complete h) (hz : Complete z) (hL : AllComplete L) (hh0 : 0 < h)
    (hLz : ∀ b a, (b, a) ∈ L → 0 < b ∧ b < h ∧ a < z) (hc : SchutteCritical G h 1 z) :
    SchutteCritical (schutteMatrix G L) h 1 z := by
  match L, hL, hLz with
  | [], _, _ => exact hc
  | (b, a) :: L', hL, hLz =>
    obtain ⟨hb0, hbh, _⟩ := hLz b a (.head _)
    have h1h : 1 < h := lt_of_le_of_lt (succ_least hb0) hbh
    exact absorb_critical_list _ h 1 G z hG hh one_complete hz hL (.inr h1h)
      (crit_principal G h 1 z hG hh one_complete hz (.inr h1h) hh0 zero_lt_one hc)
      (fix_gt1 G z hG hz (crit_base G h 1 z hG hh one_complete hz hh0 zero_lt_one hc))
      (cols_below_intro h z _ fun b' a' hin => let ⟨_, h1, h2⟩ := hLz b' a' hin; ⟨h1, h2⟩) hc

/-- Rocq: `SchutteAbsorb.close_value`. -/
theorem close_value (L : List (Ordinal.{u} × Ordinal.{u})) (G : Ordinal.{u} → Ordinal.{u}) (h z y : Ordinal.{u})
    (hG : NormalFunction G) (hh : Complete h) (hz : Complete z) (_hy : Complete y) (hL : AllComplete L)
    (hh0 : 0 < h) (hLz : ∀ b a, (b, a) ∈ L → 0 < b ∧ b < h ∧ a < z) (hc : SchutteCritical G h 1 z)
    (hyz : y < z) : schutteMatrix G L y < z :=
  have hM := schutte_matrix_normal L G hL hG
  lt_of_lt_of_le (hM.increasing y z hz hyz)
    (crit_base _ h 1 z hM hh one_complete hz hh0 zero_lt_one (close_list L G h z hG hh hz hL hh0 hLz hc))

/-- Rocq: `SchutteAbsorb.close_fix`. -/
theorem close_fix (L : List (Ordinal.{u} × Ordinal.{u})) (G : Ordinal.{u} → Ordinal.{u}) (h z : Ordinal.{u})
    (hG : NormalFunction G) (hh : Complete h) (hz : Complete z) (hL : AllComplete L) (hh0 : 0 < h)
    (hLz : ∀ b a, (b, a) ∈ L → 0 < b ∧ b < h ∧ a < z) (hc : SchutteCritical G h 1 z) :
    schutteMatrix G L z ≤ z :=
  crit_base _ h 1 z (schutte_matrix_normal L G hL hG) hh one_complete hz hh0 zero_lt_one
    (close_list L G h z hG hh hz hL hh0 hLz hc)

/-- Rocq: `SchutteAbsorb.desc_below`. -/
theorem desc_below (h e : Ordinal.{u}) (Y : List (Ordinal.{u} × Ordinal.{u})) (H : Desc ((h, e) :: Y)) :
    ∀ b a, (b, a) ∈ Y → b < h :=
  H.1

/-- If `Y < X`, a value of `Y` whose entries and argument lie below a value `z`
of `X` is below `z`. Rocq: `SchutteAbsorb.nest`. -/
theorem nest {Y X : List (Ordinal.{u} × Ordinal.{u})} (H : Mlt Y X) :
    ∀ (G : Ordinal.{u} → Ordinal.{u}) (w y : Ordinal.{u}),
    NormalFunction G → AllComplete X → AllComplete Y → Complete w → Complete y →
    Desc X → PosCols X → Desc Y → PosCols Y →
    (∀ b a, (b, a) ∈ Y → a < schutteMatrix G X w) → y < schutteMatrix G X w →
    schutteMatrix G Y y < schutteMatrix G X w := by
  induction H with
  | nil c X =>
    intro G w y hG hX _ hw _ _ hpX _ _ _ hyz
    obtain ⟨r, s⟩ := c
    obtain ⟨hr0, hs0⟩ := hpX r s (.head _)
    have hM := schutte_matrix_normal ((r, s) :: X) G hX hG
    exact lt_of_lt_of_le (hG.increasing _ _ (hM.complete w hw) hyz)
      (schutte_matrix_fixpoint2 ((r, s) :: X) w G r s hG hX hw (.head _) hr0 hs0 hX.1 hX.2.1)
  | height g d h e Y X hgh =>
    intro G w y hG hX hY hw hy _ hpX hdY hpY hYz hyz
    obtain ⟨hh, he, hX'⟩ := hX
    obtain ⟨hg, hd, hY'⟩ := hY
    obtain ⟨hh0, he0⟩ := hpX h e (.head _)
    have hc := crit_head G h e X w hG hh he hX' hw hpX
    have hz : Complete (schutteMatrix G ((h, e) :: X) w) :=
      (schutte_matrix_normal ((h, e) :: X) G ⟨hh, he, hX'⟩ hG).complete w hw
    refine close_value ((g, d) :: Y) G h _ y hG hh hz hy ⟨hg, hd, hY'⟩ hh0 (fun b a hin => ?_)
      (crit_mono_α G h e 1 _ (succ_least he0) hc) hyz
    match hin with
    | .head _ =>
      exact ⟨(hpY _ _ (.head _)).1, hgh, hYz _ _ (.head _)⟩
    | .tail _ hin =>
      exact ⟨(hpY b a (.tail _ hin)).1, lt_trans (desc_below g d Y hdY b a hin) hgh, hYz b a (.tail _ hin)⟩
  | entry h d e Y X hde =>
    intro G w y hG hX hY hw hy _ hpX hdY hpY hYz hyz
    obtain ⟨hh, he, hX'⟩ := hX
    obtain ⟨_, hd, hY'⟩ := hY
    obtain ⟨hh0, _⟩ := hpX h e (.head _)
    have hc := crit_head G h e X w hG hh he hX' hw hpX
    have hz : Complete (schutteMatrix G ((h, e) :: X) w) :=
      (schutte_matrix_normal ((h, e) :: X) G ⟨hh, he, hX'⟩ hG).complete w hw
    exact close_value Y (schutteColumn G h d) h _ y (schutte_column_normal h d G hh hd hG) hh hz hy hY' hh0
      (fun b a hin => ⟨(hpY b a (.tail _ hin)).1, desc_below h d Y hdY b a hin, hYz b a (.tail _ hin)⟩)
      (crit_lower_entry G h d e _ hG hh hd he hz hde hc) hyz
  | cons c Y X _ ih =>
    intro G w y hG hX hY hw hy hdX hpX hdY hpY hYz hyz
    exact ih (schutteColumn G c.1 c.2) w y (schutte_column_normal c.1 c.2 G hX.1 hX.2.1 hG) hX.2.2 hY.2.2 hw hy
      hdX.2 (poscols_tail c X hpX) hdY.2 (poscols_tail c Y hpY) (fun b a hin => hYz b a (.tail _ hin)) hyz

/-- If `X < Y` and the entries of `X` lie below a value `m` of `Y`, then `m` is
a fixpoint of `X`. Rocq: `SchutteAbsorb.fix_gt`. -/
theorem fix_gt {X Y : List (Ordinal.{u} × Ordinal.{u})} (H : Mlt X Y) :
    ∀ (G : Ordinal.{u} → Ordinal.{u}) (y : Ordinal.{u}),
    NormalFunction G → AllComplete X → AllComplete Y → Complete y →
    Desc X → PosCols X → Desc Y → PosCols Y →
    (∀ b a, (b, a) ∈ X → a < schutteMatrix G Y y) →
    schutteMatrix G X (schutteMatrix G Y y) ≤ schutteMatrix G Y y := by
  induction H with
  | nil c Y =>
    intro G y hG _ hY hy _ _ _ hpY _
    obtain ⟨r, s⟩ := c
    obtain ⟨hr0, hs0⟩ := hpY r s (.head _)
    exact schutte_matrix_fixpoint2 ((r, s) :: Y) y G r s hG hY hy (.head _) hr0 hs0 hY.1 hY.2.1
  | height g d h e X Y hgh =>
    intro G y hG hX hY hy hdX hpX _ hpY hXm
    obtain ⟨hg, hd, hX'⟩ := hX
    obtain ⟨hh, he, hY'⟩ := hY
    obtain ⟨hh0, he0⟩ := hpY h e (.head _)
    have hc := crit_head G h e Y y hG hh he hY' hy hpY
    have hz : Complete (schutteMatrix G ((h, e) :: Y) y) :=
      (schutte_matrix_normal ((h, e) :: Y) G ⟨hh, he, hY'⟩ hG).complete y hy
    refine close_fix ((g, d) :: X) G h _ hG hh hz ⟨hg, hd, hX'⟩ hh0 (fun b a hin => ?_)
      (crit_mono_α G h e 1 _ (succ_least he0) hc)
    match hin with
    | .head _ =>
      exact ⟨(hpX _ _ (.head _)).1, hgh, hXm _ _ (.head _)⟩
    | .tail _ hin =>
      exact ⟨(hpX b a (.tail _ hin)).1, lt_trans (desc_below g d X hdX b a hin) hgh, hXm b a (.tail _ hin)⟩
  | entry h d e X Y hde =>
    intro G y hG hX hY hy hdX hpX _ hpY hXm
    obtain ⟨_, hd, hX'⟩ := hX
    obtain ⟨hh, he, hY'⟩ := hY
    obtain ⟨hh0, _⟩ := hpY h e (.head _)
    have hc := crit_head G h e Y y hG hh he hY' hy hpY
    have hz : Complete (schutteMatrix G ((h, e) :: Y) y) :=
      (schutte_matrix_normal ((h, e) :: Y) G ⟨hh, he, hY'⟩ hG).complete y hy
    exact close_fix X (schutteColumn G h d) h _ (schutte_column_normal h d G hh hd hG) hh hz hX' hh0
      (fun b a hin => ⟨(hpX b a (.tail _ hin)).1, desc_below h d X hdX b a hin, hXm b a (.tail _ hin)⟩)
      (crit_lower_entry G h d e _ hG hh hd he hz hde hc)
  | cons c X Y _ ih =>
    intro G y hG hX hY hy hdX hpX hdY hpY hXm
    exact ih (schutteColumn G c.1 c.2) y (schutte_column_normal c.1 c.2 G hY.1 hY.2.1 hG) hX.2.2 hY.2.2 hy
      hdX.2 (poscols_tail c X hpX) hdY.2 (poscols_tail c Y hpY) (fun b a hin => hXm b a (.tail _ hin))

end Ordinal

end ConstructiveOrdinals
