import ConstructiveOrdinals.Notation.SchutteMatrix
import ConstructiveOrdinals.Schutte.Absorb

/-!
# Normalizing arbitrary Schütte matrices

`normalize` (in `Notation/SchutteMatrix`) handles proper matrices only:
strictly decreasing heights. Here every `VForm` is normalized: columns in any
order, repeated heights, zero entries, height-0 columns anywhere. The ordinal
facts are in `Schutte/Absorb`: a column followed by a strictly higher one is
absorbed, at the cost of a shift of the argument (`absorb_shift_list`); equal
heights merge (`schutte_column_merge`); a height-1 column over a translation
is the low-regime exception (`low_regime_veblen`). This file computes the
shifts (`offset`) and assembles the normalizer `normalizeX`.

Ported from the Rocq file `Notation/SchutteImproper.v`.

Lean notes:

- `strip0` splits off the last column by structural recursion instead of
  going through `List.reverse`; it computes the same pair.
- Matches are spelled out without overlapping wildcards (see the README), so
  `step` delegates its two absorbing branches to `stepAbsorb`.
- Rocq's `Forall2` is the local inductive `Forall2`.
-/

namespace ConstructiveOrdinals.SchutteMatrixNotation

open Ordinal

universe u v

namespace VForm

/-! ## Small list facts -/

theorem mem_append_cases {α : Type v} {x : α} : ∀ {xs ys : List α}, x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys
  | [], _, h => .inr h
  | _ :: _, _, .head _ => .inl (.head _)
  | _ :: xs, _, .tail _ h =>
    match mem_append_cases (xs := xs) h with
    | .inl h => .inl (.tail _ h)
    | .inr h => .inr h

theorem append_singleton_ne_nil {α : Type v} : ∀ (L : List α) (c : α), L ++ [c] ≠ []
  | [], _, h => nomatch h
  | _ :: _, _, h => nomatch h

theorem mem_split {α : Type v} {x : α} : ∀ {L : List α}, x ∈ L → ∃ L1 L2, L = L1 ++ x :: L2
  | _ :: L, .head _ => ⟨[], L, rfl⟩
  | y :: _, .tail _ h =>
    let ⟨L1, L2, E⟩ := mem_split h
    ⟨y :: L1, L2, congrArg (y :: ·) E⟩

theorem mem_map_snd {x : VForm} : ∀ {L : List (VForm × VForm)}, x ∈ L.map Prod.snd → ∃ b, (b, x) ∈ L
  | (b, _) :: _, .head _ => ⟨b, .head _⟩
  | _ :: _, .tail _ h => let ⟨b, h⟩ := mem_map_snd h; ⟨b, .tail _ h⟩

theorem mem_map_snd_intro {b a : VForm} : ∀ {L : List (VForm × VForm)}, (b, a) ∈ L → a ∈ L.map Prod.snd
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ h => .tail _ (mem_map_snd_intro h)

theorem foldl_append {α β : Type v} (f : α → β → α) : ∀ (a : α) (l1 l2 : List β),
    List.foldl f a (l1 ++ l2) = List.foldl f (List.foldl f a l1) l2
  | _, [], _ => rfl
  | a, x :: l1, l2 => foldl_append f (f a x) l1 l2

/-- Rocq's `Forall2`. -/
inductive Forall2 {α β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a b xs ys} : R a b → Forall2 R xs ys → Forall2 R (a :: xs) (b :: ys)

/-! ## Denotations of column lists -/

/-- Rocq: `Notation.SchutteImproper.md`. -/
abbrev md : List (VForm × VForm) → List (Ordinal.{0} × Ordinal.{0}) := matrixDenote

theorem md_cons (b a : VForm) (L : List (VForm × VForm)) : md ((b, a) :: L) = (denote b, denote a) :: md L := rfl

/-- The matrix of a column list over `1 + ·`. Rocq: `Notation.SchutteImproper.MX`. -/
def MX (L : List (VForm × VForm)) : Ordinal.{0} → Ordinal.{0} := schutteMatrix (fun y => 1 + y) (md L)

/-- Every entry is normal. Rocq: `Notation.SchutteImproper.nfL`. -/
def NfL (L : List (VForm × VForm)) : Prop := Each (fun c => IsNormal c.1 ∧ IsNormal c.2) L

/-- Rocq: `Notation.SchutteImproper.md_complete`. -/
theorem md_complete (L : List (VForm × VForm)) : AllComplete (md L) := all_complete L

/-- Rocq: `Notation.SchutteImproper.MX_normal`. -/
theorem MX_normal (L : List (VForm × VForm)) : NormalFunction (MX L) :=
  schutte_matrix_normal _ _ (md_complete L) onePlus_normal

/-- Rocq: `Notation.SchutteImproper.normal_eq`. -/
theorem normal_eq {f : Ordinal.{u} → Ordinal.{u}} {x y : Ordinal.{u}} (hf : NormalFunction f) (E : x ≈ y) :
    f x ≈ f y :=
  equiv_intro (hf.monotone _ _ E.le) (hf.monotone _ _ E.ge)

/-- Rocq: `Notation.SchutteImproper.normal_mono'`. -/
theorem normal_mono' {f : Ordinal.{u} → Ordinal.{u}} (hf : NormalFunction f) : ∀ a b, a ≤ b → f a ≤ f b :=
  hf.monotone

/-- Rocq: `Notation.SchutteImproper.md_app`. -/
theorem md_app (L1 L2 : List (VForm × VForm)) : md (L1 ++ L2) = md L1 ++ md L2 := matrix_denote_app L1 L2

/-- Rocq: `Notation.SchutteImproper.VF_denote_N`. -/
theorem denote_N (L : List (VForm × VForm)) : denote (N L) = MX L 0 := rfl

/-- Rocq: `Notation.SchutteImproper.cmp_spec`. -/
theorem cmp_spec (x y : VForm) (hx : IsNormal x) (hy : IsNormal y) :
    OrderingCorrect (compare x y) (denote x) (denote y) :=
  compare_correct x y (normal_proper x hx) (normal_proper y hy)

/-- Rocq: `Notation.SchutteImproper.cmp_eq`. -/
theorem cmp_eq (x y : VForm) (hx : IsNormal x) (hy : IsNormal y) (E : compare x y = .eq) : x = y := by
  have H := cmp_spec x y hx hy
  rw [E] at H
  exact normal_form_unique x y hx hy H

/-- Rocq: `Notation.SchutteImproper.nfL_app`. -/
theorem nfL_app : ∀ L1 L2 : List (VForm × VForm), NfL (L1 ++ L2) ↔ NfL L1 ∧ NfL L2
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: L1, L2 =>
    ⟨fun h => let ⟨a, b⟩ := (nfL_app L1 L2).mp h.2; ⟨⟨h.1, a⟩, b⟩,
     fun h => ⟨h.1.1, (nfL_app L1 L2).mpr ⟨h.1.2, h.2⟩⟩⟩

/-- Rocq: `Notation.SchutteImproper.In_md`. -/
theorem in_md (b a : Ordinal.{0}) (L : List (VForm × VForm)) (h : (b, a) ∈ md L) :
    ∃ b' a', (b', a') ∈ L ∧ b = denote b' ∧ a = denote a' := by
  induction L with
  | nil => exact nomatch h
  | cons c L ih =>
    obtain ⟨b', a'⟩ := c
    rw [md_cons] at h
    cases h with
    | head => exact ⟨b', a', .head _, rfl, rfl⟩
    | tail _ h => obtain ⟨b'', a'', hin, e1, e2⟩ := ih h; exact ⟨b'', a'', .tail _ hin, e1, e2⟩

/-- Rocq: `Notation.SchutteImproper.In_md_intro`. -/
theorem in_md_intro (b a : VForm) : ∀ L : List (VForm × VForm), (b, a) ∈ L → (denote b, denote a) ∈ md L
  | (_, _) :: _, .head _ => by rw [md_cons]; exact .head _
  | (_, _) :: L, .tail _ h => by rw [md_cons]; exact .tail _ (in_md_intro b a L h)

/-- Rocq: `Notation.SchutteImproper.In_nfL`. -/
theorem in_nfL (b a : VForm) : ∀ L : List (VForm × VForm), NfL L → (b, a) ∈ L → IsNormal b ∧ IsNormal a
  | (_, _) :: _, H, .head _ => H.1
  | (_, _) :: L, H, .tail _ h => in_nfL b a L H.2 h

/-! ## Lexicographic comparison of column lists -/

/-- Rocq: `Notation.SchutteImproper.lexcmp`. -/
def lexcmp : List (VForm × VForm) → List (VForm × VForm) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (g, d) :: Y, (h, e) :: X =>
    match compare g h with
    | .eq =>
      match compare d e with
      | .eq => lexcmp Y X
      | .lt => .lt
      | .gt => .gt
    | .lt => .lt
    | .gt => .gt

/-- What `lexcmp` decides: the `match` in the statement of Rocq's `lexcmp_spec`. -/
def LexSpec (Y X : List (VForm × VForm)) : Ordering → Prop
  | .lt => Mlt (md Y) (md X)
  | .eq => Y = X
  | .gt => Mlt (md X) (md Y)

/-- Rocq: `Notation.SchutteImproper.lexcmp_spec`. -/
theorem lexcmp_spec : ∀ Y X : List (VForm × VForm), NfL Y → NfL X → LexSpec Y X (lexcmp Y X)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => Mlt.nil _ _
  | _ :: _, [], _, _ => Mlt.nil _ _
  | (g, d) :: Y, (h, e) :: X, ⟨⟨hg, hd⟩, hY⟩, ⟨⟨hh, he⟩, hX⟩ => by
    have hc := cmp_spec g h hg hh
    have IH := lexcmp_spec Y X hY hX
    dsimp only [lexcmp]
    revert hc
    cases hgh : compare g h with
    | lt => intro hc; exact Mlt.height _ _ _ _ _ _ hc
    | gt => intro hc; exact Mlt.height _ _ _ _ _ _ hc
    | eq =>
      intro _
      have E := cmp_eq g h hg hh hgh
      subst E
      have hc2 := cmp_spec d e hd he
      revert hc2
      cases hde : compare d e with
      | lt => intro hc2; exact Mlt.entry _ _ _ _ _ hc2
      | gt => intro hc2; exact Mlt.entry _ _ _ _ _ hc2
      | eq =>
        intro _
        have E := cmp_eq d e hd he hde
        subst E
        revert IH
        cases lexcmp Y X with
        | lt => intro IH; exact Mlt.cons (denote g, denote d) _ _ IH
        | gt => intro IH; exact Mlt.cons (denote g, denote d) _ _ IH
        | eq => intro IH; show (g, d) :: Y = (g, d) :: X; rw [IH]

/-! ## Structure of proper column lists -/

theorem matrix_proper_tail : ∀ {b a : VForm} {L : List (VForm × VForm)}, MatrixProper ((b, a) :: L) → MatrixProper L
  | _, _, [], _ => trivial
  | _, _, (_, _) :: _, H => H.2.2.2

private theorem proper_desc_head : ∀ (L : List (VForm × VForm)) (b a : VForm), MatrixProper ((b, a) :: L) →
    ∀ b' a', (b', a') ∈ md L → b' < denote b
  | [], _, _, _, _, _, hin => nomatch hin
  | (b2, a2) :: L, b, _, H, b', a', hin => by
    have hlt : denote b2 < denote b := H.2.2.1
    rw [md_cons] at hin
    cases hin with
    | head => exact hlt
    | tail _ hin => exact lt_trans (proper_desc_head L b2 a2 H.2.2.2 b' a' hin) hlt

/-- Rocq: `Notation.SchutteImproper.proper_desc`. -/
theorem proper_desc : ∀ L : List (VForm × VForm), MatrixProper L → Ordinal.Desc (md L)
  | [], _ => trivial
  | (b, a) :: L, H => ⟨proper_desc_head L b a H, proper_desc L (matrix_proper_tail H)⟩

private theorem proper_head_pos : ∀ (b1 a1 : VForm) (rest : List (VForm × VForm)), rest ≠ [] →
    MatrixProper ((b1, a1) :: rest) → 0 < denote b1
  | _, _, [], h, _ => absurd rfl h
  | _, _, (_, _) :: _, _, H => lt_of_le_of_lt (zero_least _) H.2.2.1

/-- Rocq: `Notation.SchutteImproper.proper_heights_nonzero`. -/
theorem proper_heights_nonzero : ∀ (L : List (VForm × VForm)) (c : VForm × VForm),
    MatrixProper (L ++ [c]) → ∀ b a, (b, a) ∈ L → b ≠ Z
  | [], _, _, _, _, hin => nomatch hin
  | (b1, a1) :: L, c, H, b, a, hin =>
    match hin with
    | .head _ => fun E => by
      subst E
      exact lt_irrefl _ (proper_head_pos _ _ _ (append_singleton_ne_nil L c) H)
    | .tail _ hin => proper_heights_nonzero L c (matrix_proper_tail H) b a hin

/-- Every column has nonzero height and entry. Rocq: `Notation.SchutteImproper.posL`. -/
def PosL (L : List (VForm × VForm)) : Prop := ∀ b a, (b, a) ∈ L → b ≠ Z ∧ a ≠ Z

/-- Rocq: `Notation.SchutteImproper.posL_poscols`. -/
theorem posL_poscols (L : List (VForm × VForm)) (H : PosL L) : PosCols (md L) := fun b a hin =>
  let ⟨b', a', hin', e1, e2⟩ := in_md b a L hin
  have h := H b' a' hin'
  e1 ▸ e2 ▸ ⟨(VF_nonzero b').mpr h.1, (VF_nonzero a').mpr h.2⟩

/-- Rocq: `Notation.SchutteImproper.sparse_In`. -/
theorem sparse_in (b a : VForm) : ∀ L : List (VForm × VForm), IsSparse L → (b, a) ∈ L → a ≠ Z
  | (_, _) :: _, H, .head _ => H.1
  | (_, _) :: L, H, .tail _ h => sparse_in b a L H.2 h

/-- `strip0` on a one-column list. -/
def strip0Last : VForm × VForm → List (VForm × VForm) × VForm
  | (Z, y') => ([], y')
  | (N l, a) => ([(N l, a)], Z)

/-- Split off a last column of height 0, returning its argument (or `Z` if
there is none). Rocq: `Notation.SchutteImproper.strip0`. -/
def strip0 : List (VForm × VForm) → List (VForm × VForm) × VForm
  | [] => ([], Z)
  | c :: rest =>
    match rest with
    | [] => strip0Last c
    | c2 :: r => (c :: (strip0 (c2 :: r)).1, (strip0 (c2 :: r)).2)

private theorem singleton_eq_append {α : Type v} {x c : α} : ∀ {L : List α}, [x] = L ++ [c] → c = x
  | [], h => by cases h; rfl
  | _ :: L, h => absurd (List.cons.inj h).2.symm (append_singleton_ne_nil L c)

/-- Rocq: `Notation.SchutteImproper.strip0_spec`. -/
theorem strip0_spec : ∀ ys : List (VForm × VForm),
    ys = (strip0 ys).1 ++ [(Z, (strip0 ys).2)] ∨
      (ys = (strip0 ys).1 ∧ (strip0 ys).2 = Z ∧ ∀ c L, ys = L ++ [c] → c.1 ≠ Z)
  | [] => .inr ⟨rfl, rfl, fun c L h => (append_singleton_ne_nil L c h.symm).elim⟩
  | [(Z, _)] => .inl rfl
  | [(N l, a)] => .inr ⟨rfl, rfl, fun c L h => by
      have E := singleton_eq_append h
      subst E
      exact fun h => nomatch h⟩
  | c :: c2 :: r =>
    match strip0_spec (c2 :: r) with
    | .inl E => .inl (congrArg (c :: ·) E)
    | .inr ⟨E1, E2, H⟩ => .inr ⟨congrArg (c :: ·) E1, E2, fun c' L h =>
        match L, h with
        | [], h => absurd (List.cons.inj h).2 (fun h => nomatch h)
        | _ :: L, h => H c' L (List.cons.inj h).2⟩

/-- Rocq: `Notation.SchutteImproper.VF_normal_N_pos`. -/
theorem normal_N_pos (ys : List (VForm × VForm)) : 0 < denote (N ys) := (MX_normal ys).nonzero 0

private theorem each_mem' {α : Type v} {P : α → Prop} : ∀ {xs : List α} {x : α}, Each P xs → x ∈ xs → P x
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hx => each_mem' h.2 hx

private theorem list_last_cases {α : Type v} (ys : List α) : ys = [] ∨ ∃ L c, ys = L ++ [c] :=
  ConstructiveOrdinals.List.rev_ind (fun ys => ys = [] ∨ ∃ L c, ys = L ++ [c]) (.inl rfl)
    (fun x xs _ => .inr ⟨xs, x, rfl⟩) ys

/-- What a normal matrix looks like after stripping its argument column.
Rocq: `Notation.SchutteImproper.strip0_normal`. -/
theorem strip0_normal (ys : List (VForm × VForm)) (Hn : IsNormal (N ys)) (Y : List (VForm × VForm)) (y' : VForm)
    (hst : strip0 ys = (Y, y')) :
    NfL Y ∧ IsNormal y' ∧ MatrixProper Y ∧ PosL Y ∧
      (∀ b a, (b, a) ∈ Y → denote a < denote (N ys)) ∧ denote y' < denote (N ys) ∧
      denote (N ys) ≈ MX Y (denote y') := by
  obtain ⟨Hsp, Hpr, Hnf, Hlt⟩ := (isNormal_N ys).mp Hn
  have Hlt' : ∀ b a, (b, a) ∈ ys → denote a < denote (N ys) := fun b a hin =>
    each_mem' (P := fun x => denote x.2 < denote (N ys)) Hlt hin
  have Hpos : ∀ Y c, ys = Y ++ [c] → c.1 ≠ Z → PosL ys := fun Y c E hc b a hin => by
    refine ⟨?_, sparse_in b a ys Hsp hin⟩
    rw [E] at hin
    match mem_append_cases hin with
    | .inl hin => exact proper_heights_nonzero Y c (E ▸ Hpr) b a hin
    | .inr (.head _) => exact hc
  have hspec := strip0_spec ys
  rw [hst] at hspec
  match hspec with
  | .inl E =>
    have HnfY : NfL Y := ((nfL_app Y [(Z, y')]).mp (E ▸ Hnf)).1
    have Hy' : IsNormal y' := ((nfL_app Y [(Z, y')]).mp (E ▸ Hnf)).2.1.2
    refine ⟨HnfY, Hy', matrix_proper_app Y [(Z, y')] (E ▸ Hpr), fun b a hin => ⟨?_, ?_⟩, fun b a hin => ?_, ?_, ?_⟩
    · exact proper_heights_nonzero Y (Z, y') (E ▸ Hpr) b a hin
    · exact sparse_in b a ys Hsp (E ▸ List.mem_append_left _ hin)
    · exact Hlt' b a (E ▸ List.mem_append_left _ hin)
    · exact Hlt' Z y' (E ▸ List.mem_append_right Y (.head _))
    · rw [denote_N, E, MX, md_app, schutte_matrix_app]
      exact equiv_trans (schutte_column0 _ _ 0) (normal_eq (MX_normal Y) (add_zero _))
  | .inr ⟨E, Ey', Hlast⟩ =>
    subst E Ey'
    refine ⟨Hnf, trivial, Hpr, ?_, Hlt', normal_N_pos _, equiv_refl _⟩
    match list_last_cases ys with
    | .inl h => intro b a hin; rw [h] at hin; exact nomatch hin
    | .inr ⟨L, c, h⟩ =>
      have := Hpos L c h (Hlast c L h)
      exact this

/-! ## Maximum of a list of notations -/

/-- Rocq: `Notation.SchutteImproper.vmax`. -/
def vmax : List VForm → VForm
  | [] => Z
  | x :: xs =>
    match compare x (vmax xs) with
    | .lt => vmax xs
    | .eq => x
    | .gt => x

/-- Rocq: `Notation.SchutteImproper.vmax_spec`. -/
theorem vmax_spec : ∀ xs : List VForm, Each IsNormal xs →
    IsNormal (vmax xs) ∧ (∀ x, x ∈ xs → denote x ≤ denote (vmax xs)) ∧ (xs = [] ∨ vmax xs ∈ xs)
  | [], _ => ⟨trivial, ⟨fun _ h => (nomatch h), .inl rfl⟩⟩
  | x :: xs, ⟨Hx, Hxs⟩ => by
    obtain ⟨Hm, Hle, Hin⟩ := vmax_spec xs Hxs
    have Hc := cmp_spec x (vmax xs) Hx Hm
    dsimp only [vmax]
    revert Hc
    cases compare x (vmax xs) with
    | lt =>
      intro Hc
      refine ⟨Hm, fun y hy => ?_, .inr ?_⟩
      · match hy with
        | .head _ => exact le_of_lt Hc
        | .tail _ hy => exact Hle y hy
      · match Hin with
        | .inl E =>
          subst E
          exact (lt_irrefl _ (lt_of_le_of_lt (zero_least _) Hc)).elim
        | .inr Hin => exact .tail _ Hin
    | eq =>
      intro Hc
      refine ⟨Hx, fun y hy => ?_, .inr (.head _)⟩
      match hy with
      | .head _ => exact le_refl _
      | .tail _ hy => exact le_trans (Hle y hy) Hc.ge
    | gt =>
      intro Hc
      refine ⟨Hx, fun y hy => ?_, .inr (.head _)⟩
      match hy with
      | .head _ => exact le_refl _
      | .tail _ hy => exact le_trans (Hle y hy) (le_of_lt Hc)

/-- Rocq: `Notation.SchutteImproper.entry_size`. -/
theorem entry_size : ∀ (ys : List (VForm × VForm)) (b a : VForm), (b, a) ∈ ys → termSize a < termSize (N ys)
  | (b, a) :: ys, _, _, .head _ =>
    Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_trans (Nat.le_add_left (termSize a) (termSize b))
      (Nat.le_add_right _ (matrixSize ys))))
  | (b', a') :: ys, b, a, .tail _ hin =>
    Nat.lt_of_lt_of_le (entry_size ys b a hin)
      (Nat.succ_le_succ (Nat.le_succ_of_le (Nat.le_add_left (matrixSize ys) (termSize b' + termSize a'))))

/-! ## Offsets

`offset X m` is the least `t` with `m < M_X(t)`, for a proper list `X` of
positive columns. If `m` is not below `M_X(0)`, compare the matrix of `m`
(argument column removed) with `X`: equal means `m = M_X(y')`; greater means
`m` is a fixpoint of `M_X` (`fix_gt`); smaller means the values of `M_X` above
`m` are those above its largest component (`nest`). -/

/-- Rocq: `Notation.SchutteImproper.offN`. -/
def offN : Nat → List (VForm × VForm) → VForm → VForm
  | 0, _, _ => Z
  | fuel + 1, X, m =>
    match compare m (N X) with
    | .lt => Z
    | .eq => one
    | .gt =>
      match m with
      | Z => Z
      | N ys =>
        match strip0 ys with
        | (Y, y') =>
          match lexcmp Y X with
          | .eq => succ y'
          | .gt => succ (N ys)
          | .lt => offN fuel X (vmax (y' :: Y.map Prod.snd))

/-- Rocq: `Notation.SchutteImproper.VF_offset`. -/
def offset (X : List (VForm × VForm)) (m : VForm) : VForm := offN (termSize m + 1) X m

/-- Rocq: `Notation.SchutteImproper.OffSpec`. -/
def OffSpec (X : List (VForm × VForm)) (m t : VForm) : Prop :=
  IsNormal t ∧ denote m < MX X (denote t) ∧ ∀ y, y < denote t → MX X y ≤ denote m

/-- Rocq: `Notation.SchutteImproper.VF_one_denote`. -/
theorem one_denote : denote one ≈ 1 := add_zero 1

/-- Rocq: `Notation.SchutteImproper.lt_one_le_zero`. -/
theorem lt_one_le_zero {y : Ordinal.{u}} (h : y < 1) : y ≤ 0 := le_zero_of_lt_one h

/-- Rocq: `Notation.SchutteImproper.succ_reflect`. -/
theorem succ_reflect (x : VForm) (hx : IsNormal x) :
    denote (succ x) ≈ Ordinal.succ (denote x) ∧ IsNormal (succ x) :=
  let ⟨E, N'⟩ := succ_reflects (denote x) x ⟨equiv_refl _, hx⟩
  ⟨equiv_symm E, N'⟩

/-- Rocq: `Notation.SchutteImproper.add_reflect`. -/
theorem add_reflect (x y : VForm) (hx : IsNormal x) (hy : IsNormal y) :
    denote (add x y) ≈ denote x + denote y ∧ IsNormal (add x y) :=
  let ⟨E, N'⟩ := add_reflects (denote x) x ⟨equiv_refl _, hx⟩ (denote y) y ⟨equiv_refl _, hy⟩
  ⟨equiv_symm E, N'⟩

/-- Rocq: `Notation.SchutteImproper.le_succ_lt`. -/
theorem le_succ_lt {y x : Ordinal.{u}} (h : y < Ordinal.succ x) : y ≤ x := let ⟨_, h⟩ := lt_elim h; h

/-- Rocq: `Notation.SchutteImproper.entries_below_value`. -/
theorem entries_below_value (X : List (VForm × VForm)) (b a : VForm) (hin : (b, a) ∈ X) :
    denote a ≤ MX X 0 := by
  obtain ⟨L1, L2, E⟩ := mem_split hin
  subst E
  show denote a ≤ schutteMatrix _ (md (L1 ++ (b, a) :: L2)) 0
  rw [md_app]
  exact matrix_member_le (md L1) (md L2) _ (denote b) (denote a) onePlus_normal (md_complete L1) (complete b)
    (complete a) (md_complete L2)

section offset

variable (X : List (VForm × VForm)) (HnfX : NfL X) (HprX : MatrixProper X) (HposX : PosL X)

include HnfX HprX HposX in
/-- Rocq: `Notation.SchutteImproper.offN_correct`. -/
theorem offN_correct : ∀ (fuel : Nat) (m : VForm), termSize m < fuel → IsNormal m → OffSpec X m (offN fuel X m)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, m, Hsz, Hm => by
    have HdX := proper_desc X HprX
    have HpcX := posL_poscols X HposX
    have HFn := MX_normal X
    have HpN : IsProper (N X) := HprX
    have Hc := compare_correct m (N X) (normal_proper m Hm) HpN
    dsimp only [offN]
    revert Hc
    cases compare m (N X) with
    | lt =>
      intro Hc
      exact ⟨trivial, Hc, fun y hy => (lt_irrefl _ (lt_of_le_of_lt (zero_least y) hy)).elim⟩
    | eq =>
      intro Hc
      refine ⟨one_normal, ?_, fun y hy => ?_⟩
      · exact lt_of_le_of_lt Hc.le (HFn.increasing _ _ (complete one) (lt_of_lt_of_le zero_lt_one one_denote.ge))
      · exact le_trans (HFn.monotone _ _ (lt_one_le_zero (lt_of_lt_of_le hy one_denote.le))) Hc.ge
    | gt =>
      intro Hc
      match m, Hm, Hsz, Hc with
      | Z, _, _, Hc => exact (lt_irrefl _ (lt_of_le_of_lt (zero_least _) Hc)).elim
      | N ys, Hm, Hsz, Hc =>
      show OffSpec X (N ys) (match strip0 ys with
        | (Y, y') => match lexcmp Y X with
          | .eq => succ y'
          | .gt => succ (N ys)
          | .lt => offN fuel X (vmax (y' :: Y.map Prod.snd)))
      have Hst0 := strip0_spec ys
      cases hst : strip0 ys with
      | mk Y y' =>
      rw [hst] at Hst0
      obtain ⟨HnfY, Hy', HprY, HposY, HYlt, Hylt, EY⟩ := strip0_normal ys Hm Y y' hst
      have HdY := proper_desc Y HprY
      have HpcY := posL_poscols Y HposY
      have Hlx := lexcmp_spec Y X HnfY HnfX
      show OffSpec X (N ys) (match lexcmp Y X with
          | .eq => succ y'
          | .gt => succ (N ys)
          | .lt => offN fuel X (vmax (y' :: Y.map Prod.snd)))
      revert Hlx
      cases lexcmp Y X with
      | lt =>
        intro Hlx
        -- Y < X: recurse on the largest component
        have Hu : Each IsNormal (y' :: Y.map Prod.snd) := by
          refine ⟨Hy', ?_⟩
          clear Hst0 hst HYlt EY HprY HposY HdY HpcY Hlx
          induction Y with
          | nil => trivial
          | cons c Y ih => exact ⟨HnfY.1.2, ih HnfY.2⟩
        obtain ⟨Hun, Hule, Hin⟩ := vmax_spec _ Hu
        have Hin : vmax (y' :: Y.map Prod.snd) ∈ y' :: Y.map Prod.snd :=
          match Hin with
          | .inl h => nomatch h
          | .inr h => h
        generalize vmax (y' :: Y.map Prod.snd) = u at Hun Hule Hin ⊢
        have Hum : denote u < denote (N ys) :=
          match Hin with
          | .head _ => Hylt
          | .tail _ hin => let ⟨b, hb⟩ := mem_map_snd hin; HYlt b u hb
        have Husz : termSize u < fuel := by
          refine Nat.lt_of_lt_of_le ?_ (Nat.le_of_lt_succ Hsz)
          match Hin with
          | .head _ =>
            match Hst0 with
            | .inl E => exact entry_size ys Z u (E ▸ List.mem_append_right Y (.head _))
            | .inr ⟨_, Ey, _⟩ => subst Ey; exact Nat.succ_pos _
          | .tail _ hin =>
            obtain ⟨b, hb⟩ := mem_map_snd hin
            match Hst0 with
            | .inl E => exact entry_size ys b u (E ▸ List.mem_append_left _ hb)
            | .inr ⟨E, _, _⟩ => exact entry_size ys b u (E ▸ hb)
        obtain ⟨Ht, Hut, Hbelow⟩ := offN_correct fuel u Husz Hun
        refine ⟨Ht, ?_, fun y hy => le_trans (Hbelow y hy) (le_of_lt Hum)⟩
        refine lt_of_le_of_lt EY.le ?_
        refine nest Hlx _ _ _ onePlus_normal (md_complete X) (md_complete Y) (complete _) (complete y') HdX HpcX HdY
          HpcY (fun b a hin => ?_) (lt_of_le_of_lt (Hule y' (.head _)) Hut)
        obtain ⟨b', a', hin', _, E2⟩ := in_md b a Y hin
        subst E2
        exact lt_of_le_of_lt (Hule a' (.tail _ (mem_map_snd_intro hin'))) Hut
      | eq =>
        intro Hlx
        -- Y = X: m is a value of M_X
        subst Hlx
        obtain ⟨Es, Ns⟩ := succ_reflect y' Hy'
        refine ⟨Ns, ?_, fun y hy => ?_⟩
        · exact lt_of_le_of_lt EY.le (lt_of_lt_of_le (HFn.increasing _ _ (succ_complete (complete y')) (succ_lt _))
            (HFn.monotone _ _ Es.ge))
        · exact le_trans (HFn.monotone _ _ (le_succ_lt (lt_of_lt_of_le hy Es.le))) EY.ge
      | gt =>
        intro Hlx
        -- Y > X: m is a fixpoint of M_X
        have Hfix : MX X (denote (N ys)) ≤ denote (N ys) := by
          refine le_trans (HFn.monotone _ _ EY.le) (le_trans ?_ EY.ge)
          refine fix_gt Hlx _ _ onePlus_normal (md_complete X) (md_complete Y) (complete y') HdX HpcX HdY HpcY
            fun b a hin => ?_
          obtain ⟨b', a', hin', _, E2⟩ := in_md b a X hin
          subst E2
          exact lt_of_lt_of_le (lt_of_le_of_lt (entries_below_value X b' a' hin') Hc) EY.le
        obtain ⟨Es, Ns⟩ := succ_reflect (N ys) Hm
        refine ⟨Ns, ?_, fun y hy => ?_⟩
        · exact lt_of_le_of_lt (normal_inflationary HFn _ (complete _))
            (lt_of_lt_of_le (HFn.increasing _ _ (succ_complete (complete _)) (succ_lt _)) (HFn.monotone _ _ Es.ge))
        · exact le_trans (HFn.monotone _ _ (le_succ_lt (lt_of_lt_of_le hy Es.le))) Hfix

include HnfX HprX HposX in
/-- Rocq: `Notation.SchutteImproper.VF_offset_correct`. -/
theorem offset_correct (m : VForm) (Hm : IsNormal m) : OffSpec X m (offset X m) :=
  offN_correct X HnfX HprX HposX _ m (Nat.lt_succ_self _) Hm

end offset

/-! ## The leading exponent of a notation -/

/-- Rocq: `Notation.SchutteImproper.lead`. -/
def lead (d : VForm) : VForm :=
  match decompose d with
  | x :: _ => x
  | [] => Z

/-- Rocq: `Notation.SchutteImproper.cantor_bound`. -/
theorem cantor_bound : ∀ (xs : List VForm) (a : Ordinal.{0}), CantorDecomposition.CantorOrdered denote xs →
    (∀ x, x ∈ xs → denote x ≤ a) → Complete a → CantorDecomposition.cantorDenote denote xs < ω ^ Ordinal.succ a
  | [], _, _, _, _ => pow_pos ω _
  | x :: xs, a, Ho, Hle, Ha =>
    powOmega_additively_closed (succ_complete Ha) _ _
      (pow_lt_pow_right omega_gt1 (lt_of_le_of_lt (Hle x (.head _)) (succ_lt a)))
      (cantor_bound xs a Ho.2 (fun y hy => Hle y (.tail _ hy)) Ha)

private theorem cantor_ordered_le : ∀ (xs : List VForm) (x : VForm),
    CantorDecomposition.CantorOrdered denote (x :: xs) → ∀ y, y ∈ xs → denote y ≤ denote x
  | [], _, _, _, hy => nomatch hy
  | x2 :: xs, _, Ho, y, hy =>
    match hy with
    | .head _ => Ho.1
    | .tail _ hy => le_trans (cantor_ordered_le xs x2 Ho.2 y hy) Ho.1

/-- Rocq: `Notation.SchutteImproper.lead_spec`. -/
theorem lead_spec (d : VForm) (Hd : IsNormal d) (Hpos : 0 < denote d) :
    IsNormal (lead d) ∧ ω ^ denote (lead d) ≤ denote d ∧ denote d < ω ^ Ordinal.succ (denote (lead d)) := by
  have H := decompose_correct d Hd
  revert H
  dsimp only [lead]
  cases decompose d with
  | nil =>
    intro H
    exact (lt_irrefl _ (lt_of_lt_of_le Hpos H.2.2.le)).elim
  | cons x xs =>
    intro H
    obtain ⟨⟨Hx, _⟩, Ho, E⟩ := H
    refine ⟨Hx, le_trans (le_add_right _ _) E.ge, lt_of_le_of_lt E.le ?_⟩
    refine cantor_bound (x :: xs) (denote x) Ho (fun y hy => ?_) (complete x)
    match hy with
    | .head _ => exact le_refl _
    | .tail _ hy => exact cantor_ordered_le xs x Ho y hy

/-! ## Pushing a column onto a proper list, merging equal heights -/

/-- Rocq: `Notation.SchutteImproper.mpush`. -/
def mpush : List (VForm × VForm) → VForm → VForm → List (VForm × VForm)
  | [], h, e => [(h, e)]
  | [(b, a)], h, e =>
    match compare b h with
    | .eq => [(b, add a e)]
    | .lt => [(b, a), (h, e)]
    | .gt => [(b, a), (h, e)]
  | c :: c2 :: L, h, e => c :: mpush (c2 :: L) h e

/-- Rocq: `Notation.SchutteImproper.mpush_head`. -/
theorem mpush_head (c : VForm × VForm) (L : List (VForm × VForm)) (h e : VForm) :
    ∃ a' L', mpush (c :: L) h e = (c.1, a') :: L' := by
  match L with
  | [] =>
    obtain ⟨b, a⟩ := c
    dsimp only [mpush]
    cases compare b h with
    | eq => exact ⟨_, _, rfl⟩
    | lt => exact ⟨_, _, rfl⟩
    | gt => exact ⟨_, _, rfl⟩
  | c2 :: L => exact ⟨c.2, mpush (c2 :: L) h e, rfl⟩

/-- Rocq: `Notation.SchutteImproper.VF_nonzero'`. -/
theorem VF_nonzero' (x : VForm) (_hx : IsNormal x) (H : 0 < denote x) : x ≠ Z := fun E => by
  subst E
  exact lt_irrefl _ H

/-- Rocq: `Notation.SchutteImproper.mpush_spec`. -/
theorem mpush_spec : ∀ (L : List (VForm × VForm)) (h e : VForm), NfL L → MatrixProper L → PosL L →
    (∀ b a, (b, a) ∈ L → denote h ≤ denote b) → IsNormal h → IsNormal e → h ≠ Z → e ≠ Z →
    NfL (mpush L h e) ∧ MatrixProper (mpush L h e) ∧ PosL (mpush L h e) ∧
      ∀ (f : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}), NormalFunction f → Complete x →
        schutteMatrix f (md (mpush L h e)) x ≈ schutteColumn (schutteMatrix f (md L)) (denote h) (denote e) x := by
  intro L
  induction L with
  | nil =>
    intro h e _ _ _ _ Hh He Hh0 He0
    refine ⟨⟨⟨Hh, He⟩, trivial⟩, ⟨normal_proper h Hh, normal_proper e He, trivial⟩, fun b a hin => ?_,
      fun _ _ _ _ => equiv_refl _⟩
    match hin with
    | .head _ => exact ⟨Hh0, He0⟩
  | cons c L IH =>
    intro h e HnfL HprL HposL Hge Hh He Hh0 He0
    obtain ⟨b, a⟩ := c
    obtain ⟨⟨Hb, Ha⟩, HnfL'⟩ := HnfL
    obtain ⟨Hb0, Ha0⟩ := HposL b a (.head _)
    have Hpos' : PosL L := fun b' a' hin => HposL b' a' (.tail _ hin)
    match L, IH, HnfL', HprL, Hpos', Hge with
    | [], _, _, _, _, Hge =>
      -- a single column
      have Hc := cmp_spec b h Hb Hh
      have Hhb : denote h ≤ denote b := Hge b a (.head _)
      dsimp only [mpush]
      revert Hc
      cases hbh : compare b h with
      | lt => intro Hc; exact (lt_irrefl _ (lt_of_lt_of_le Hc Hhb)).elim
      | eq =>
        intro _
        have E := cmp_eq b h Hb Hh hbh
        subst E
        obtain ⟨Eae, Nae⟩ := add_reflect a e Ha He
        have Hae0 : add a e ≠ Z := VF_nonzero' _ Nae
          (lt_of_lt_of_le ((VF_nonzero a).mpr Ha0) (le_trans (le_add_right _ _) Eae.ge))
        refine ⟨⟨⟨Hb, Nae⟩, trivial⟩, ⟨normal_proper b Hb, normal_proper _ Nae, trivial⟩, fun b' a' hin => ?_,
          fun f x hf hx => ?_⟩
        · cases hin with
          | head => exact ⟨Hb0, Hae0⟩
          | tail _ h => exact nomatch h
        · exact equiv_trans
            (equiv_intro (schutte_column_monotone f _ _ x _ x hf.monotone Eae.le (le_refl x))
              (schutte_column_monotone f _ _ x _ x hf.monotone Eae.ge (le_refl x)))
            (schutte_column_merge _ _ x _ f hf (complete b) (complete a) (complete e) hx).symm
      | gt =>
        intro Hc
        refine ⟨⟨⟨Hb, Ha⟩, ⟨Hh, He⟩, trivial⟩,
          ⟨normal_proper b Hb, normal_proper a Ha, Hc, normal_proper h Hh, normal_proper e He, trivial⟩,
          fun b' a' hin => ?_, fun _ _ _ _ => equiv_refl _⟩
        match hin with
        | .head _ => exact ⟨Hb0, Ha0⟩
        | .tail _ (.head _) => exact ⟨Hh0, He0⟩
    | (b2, a2') :: L, IH, HnfL', HprL, Hpos', Hge =>
      -- at least two columns: keep the first
      have HprL' : MatrixProper ((b2, a2') :: L) := HprL.2.2.2
      obtain ⟨Hnf', Hpr', Hpo', Hsem⟩ := IH h e HnfL' HprL' Hpos' (fun b' a' hin => Hge b' a' (.tail _ hin))
        Hh He Hh0 He0
      obtain ⟨a2, L2, E2⟩ := mpush_head (b2, a2') L h e
      show NfL ((b, a) :: mpush ((b2, a2') :: L) h e) ∧ MatrixProper ((b, a) :: mpush ((b2, a2') :: L) h e) ∧
        PosL ((b, a) :: mpush ((b2, a2') :: L) h e) ∧ _
      refine ⟨⟨⟨Hb, Ha⟩, Hnf'⟩, ?_, fun b' a' hin => ?_, fun f x hf hx => ?_⟩
      · rw [E2] at Hpr' ⊢
        exact ⟨normal_proper b Hb, normal_proper a Ha, HprL.2.2.1, Hpr'⟩
      · match hin with
        | .head _ => exact ⟨Hb0, Ha0⟩
        | .tail _ hin => exact Hpo' b' a' hin
      · exact Hsem _ x (schutte_column_normal _ _ f (complete b) (complete a) hf) hx

/-! ## Splitting off the suffix of columns lower than `h` -/

/-- Rocq: `Notation.SchutteImproper.split_lower`. -/
def splitLower (h : VForm) : List (VForm × VForm) → List (VForm × VForm) × List (VForm × VForm)
  | [] => ([], [])
  | (b, a) :: L' =>
    match compare b h with
    | .lt => ([], (b, a) :: L')
    | .eq => ((b, a) :: (splitLower h L').1, (splitLower h L').2)
    | .gt => ((b, a) :: (splitLower h L').1, (splitLower h L').2)

/-- Rocq: `Notation.SchutteImproper.split_lower_spec`. -/
theorem split_lower_spec : ∀ (L : List (VForm × VForm)) (h : VForm), NfL L → MatrixProper L → IsNormal h →
    L = (splitLower h L).1 ++ (splitLower h L).2 ∧
      (∀ b a, (b, a) ∈ (splitLower h L).1 → denote h ≤ denote b) ∧
      (∀ b a, (b, a) ∈ (splitLower h L).2 → denote b < denote h)
  | [], _, _, _, _ => ⟨rfl, fun _ _ h => (nomatch h), fun _ _ h => nomatch h⟩
  | (b, a) :: L, h, ⟨⟨Hb, _⟩, HnfL⟩, HprL, Hh => by
    have Hbelow := (proper_desc ((b, a) :: L) HprL).1
    have Hc := cmp_spec b h Hb Hh
    have IH := split_lower_spec L h HnfL (matrix_proper_tail HprL) Hh
    dsimp only [splitLower]
    revert Hc
    cases compare b h with
    | lt =>
      intro Hc
      refine ⟨rfl, fun _ _ h => (nomatch h), fun b' a' hin => ?_⟩
      match hin with
      | .head _ => exact Hc
      | .tail _ hin => exact lt_trans (Hbelow _ _ (in_md_intro b' a' L hin)) Hc
    | eq =>
      intro Hc
      refine ⟨congrArg ((b, a) :: ·) IH.1, fun b' a' hin => ?_, IH.2.2⟩
      match hin with
      | .head _ => exact Hc.ge
      | .tail _ hin => exact IH.2.1 b' a' hin
    | gt =>
      intro Hc
      refine ⟨congrArg ((b, a) :: ·) IH.1, fun b' a' hin => ?_, IH.2.2⟩
      match hin with
      | .head _ => exact le_of_lt Hc
      | .tail _ hin => exact IH.2.1 b' a' hin

/-! ## Small facts used by the step -/

/-- Rocq: `Notation.SchutteImproper.col_base_eq`. -/
theorem col_base_eq (F G : Ordinal.{u} → Ordinal.{u}) (β α x : Ordinal.{u}) (hF : NormalFunction F)
    (hG : NormalFunction G) (h : ∀ y, Complete y → F y ≈ G y) (hβ : Complete β) (hα : Complete α)
    (hx : Complete x) : schutteColumn F β α x ≈ schutteColumn G β α x :=
  equiv_intro (col_base_le F G β α x hF hG (fun y hy => (h y hy).le) hβ hα hx)
    (col_base_le G F β α x hG hF (fun y hy => (h y hy).ge) hβ hα hx)

/-- Rocq: `Notation.SchutteImproper.col_height_eq`. -/
theorem col_height_eq (f : Ordinal.{u} → Ordinal.{u}) (β β' α x : Ordinal.{u}) (hf : NormalFunction f)
    (E : β ≈ β') : schutteColumn f β α x ≈ schutteColumn f β' α x :=
  equiv_intro (schutte_column_monotoneβ β β' α x f hf.monotone E.le)
    (schutte_column_monotoneβ β' β α x f hf.monotone E.ge)

/-- Rocq: `Notation.SchutteImproper.MX_snoc`. -/
theorem MX_snoc (L : List (VForm × VForm)) (b a : VForm) (x : Ordinal.{0}) :
    MX (L ++ [(b, a)]) x = schutteColumn (MX L) (denote b) (denote a) x := by
  show schutteMatrix _ (md (L ++ [(b, a)])) x = _
  rw [md_app, schutte_matrix_app]
  rfl

/-- Rocq: `Notation.SchutteImproper.MX_app`. -/
theorem MX_app (L1 L2 : List (VForm × VForm)) (x : Ordinal.{0}) :
    MX (L1 ++ L2) x = schutteMatrix (MX L1) (md L2) x := by
  show schutteMatrix _ (md (L1 ++ L2)) x = _
  rw [md_app, schutte_matrix_app]
  rfl

/-- Rocq: `Notation.SchutteImproper.proper_snoc0`. -/
theorem proper_snoc0 : ∀ (L : List (VForm × VForm)) (T : VForm), MatrixProper L → PosL L → NfL L → IsNormal T →
    MatrixProper (L ++ [(Z, T)])
  | [], T, _, _, _, HT => ⟨trivial, normal_proper T HT, trivial⟩
  | [(b, a)], T, _, Hpos, ⟨⟨Hb, Ha⟩, _⟩, HT =>
    ⟨normal_proper b Hb, normal_proper a Ha, (VF_nonzero b).mpr (Hpos b a (.head _)).1,
      trivial, normal_proper T HT, trivial⟩
  | (b, a) :: (b2, a2) :: L, T, Hpr, Hpos, ⟨⟨Hb, Ha⟩, Hnf⟩, HT =>
    ⟨normal_proper b Hb, normal_proper a Ha, Hpr.2.2.1,
      proper_snoc0 ((b2, a2) :: L) T Hpr.2.2.2 (fun b' a' hin => Hpos b' a' (.tail _ hin)) Hnf HT⟩

/-- Rocq: `Notation.SchutteImproper.pos_ge1`. -/
theorem pos_ge1 (b : VForm) (_hb : IsNormal b) (H : b ≠ Z) : 1 ≤ denote b :=
  succ_least ((VF_nonzero b).mpr H)

/-- Matrices of height at most 1 over `1 + y` are translations.
Rocq: `Notation.SchutteImproper.low_shape`. -/
theorem low_shape (a0 : VForm) (_ha0 : IsNormal a0) (w : Ordinal.{0}) (hw : Complete w) :
    MX [(one, a0)] w ≈ ω ^ denote a0 + w :=
  calc MX [(one, a0)] w = schutteColumn (fun y => 1 + y) (denote one) (denote a0) w := rfl
    _ ≈ schutteColumn (fun y => 1 + y) 1 (denote a0) w := col_height_eq _ _ _ _ w onePlus_normal one_denote
    _ ≈ veblen (fun y => 1 + y) (denote a0) w := schutte_column_veblen _ w _ onePlus_normal (complete a0) hw
    _ ≈ ω ^ denote a0 + w := veblen_onePlus _ (complete a0) w hw

/-- Rocq: `Notation.SchutteImproper.high`. -/
def high : List (VForm × VForm) → Bool
  | (b, _) :: _ =>
    match compare b one with
    | .gt => true
    | .lt => false
    | .eq => false
  | [] => false

/-- Rocq: `Notation.SchutteImproper.regime`. -/
def regime (h : VForm) (L : List (VForm × VForm)) : Bool :=
  match compare h one with
  | .gt => true
  | .lt => high L
  | .eq => high L

/-! ## One step of the normalizer -/

/-- The absorbing branches of `step`. -/
def stepAbsorb (L : List (VForm × VForm)) (T h e : VForm) (k p : List (VForm × VForm)) :
    List (VForm × VForm) × VForm :=
  match regime h L with
  | true => (mpush k h e, offset (mpush k h e) (vmax (T :: p.map Prod.snd)))
  | false => ([(one, add (lead (normalize (N (L ++ [(Z, T)])))) e)], Z)

/-- Rocq: `Notation.SchutteImproper.step`. -/
def step : List (VForm × VForm) × VForm → VForm × VForm → List (VForm × VForm) × VForm
  | (L, T), (Z, e) => (L, add T e)
  | (L, T), (N _, Z) => (L, T)
  | (L, T), (N hl, N el) =>
    match splitLower (N hl) L with
    | (k, p) =>
      match p, T with
      | [], Z => (mpush L (N hl) (N el), Z)
      | [], N Tl => stepAbsorb L (N Tl) (N hl) (N el) k []
      | c :: p', T => stepAbsorb L T (N hl) (N el) k (c :: p')

/-- Rocq: `Notation.SchutteImproper.Good`. -/
def Good (st : List (VForm × VForm) × VForm) : Prop :=
  NfL st.1 ∧ MatrixProper st.1 ∧ PosL st.1 ∧ IsNormal st.2

/-- Rocq: `Notation.SchutteImproper.Sem`. -/
def Sem (I : List (VForm × VForm)) (st : List (VForm × VForm) × VForm) : Prop :=
  ∀ x, Complete x → MX I x ≈ MX st.1 (denote st.2 + x)

/-- Rocq: `Notation.SchutteImproper.sem_base`. -/
theorem sem_base (I L : List (VForm × VForm)) (T : VForm) (H : Sem I (L, T)) (y : Ordinal.{0}) (hy : Complete y) :
    MX I y ≈ MX (L ++ [(Z, T)]) y := by
  rw [MX_snoc]
  exact equiv_trans (H y hy) (schutte_column0 _ _ y).symm

/-- Rocq: `Notation.SchutteImproper.nfL_sub`. -/
theorem nfL_sub (k p : List (VForm × VForm)) (H : NfL (k ++ p)) : NfL k ∧ NfL p := (nfL_app k p).mp H

/-- Rocq: `Notation.SchutteImproper.posL_app`. -/
theorem posL_app (k p : List (VForm × VForm)) (H : PosL (k ++ p)) : PosL k ∧ PosL p :=
  ⟨fun b a hin => H b a (List.mem_append_left _ hin), fun b a hin => H b a (List.mem_append_right _ hin)⟩

/-- Rocq: `Notation.SchutteImproper.vmax_entries`. -/
theorem vmax_entries (T : VForm) (p : List (VForm × VForm)) (HT : IsNormal T) (Hp : NfL p) :
    IsNormal (vmax (T :: p.map Prod.snd)) ∧
      ∀ z, (∀ b a, (b, a) ∈ md (p ++ [(Z, T)]) → a < z) ↔ denote (vmax (T :: p.map Prod.snd)) < z := by
  have Hn : Each IsNormal (T :: p.map Prod.snd) := by
    refine ⟨HT, ?_⟩
    clear HT
    induction p with
    | nil => trivial
    | cons c p ih => exact ⟨Hp.1.2, ih Hp.2⟩
  obtain ⟨Hm, Hle, Hin⟩ := vmax_spec _ Hn
  have Hin : vmax (T :: p.map Prod.snd) ∈ T :: p.map Prod.snd :=
    match Hin with
    | .inl h => nomatch h
    | .inr h => h
  generalize vmax (T :: p.map Prod.snd) = m at Hm Hle Hin ⊢
  refine ⟨Hm, fun z => ⟨fun H => ?_, fun H b a hin => ?_⟩⟩
  · rw [md_app] at H
    match Hin with
    | .head _ => exact H (denote Z) (denote m) (List.mem_append_right _ (.head _))
    | .tail _ hin =>
      obtain ⟨b, hb⟩ := mem_map_snd hin
      exact H (denote b) (denote m) (List.mem_append_left _ (in_md_intro b m p hb))
  · rw [md_app] at hin
    match mem_append_cases hin with
    | .inl hin =>
      obtain ⟨b', a', hin', _, E2⟩ := in_md b a p hin
      subst E2
      exact lt_of_le_of_lt (Hle a' (.tail _ (mem_map_snd_intro hin'))) H
    | .inr hin =>
      rw [md_cons] at hin
      cases hin with
      | head => exact lt_of_le_of_lt (Hle T (.head _)) H
      | tail _ h => exact nomatch h

/-- Rocq: `Notation.SchutteImproper.no_low_pop`. -/
theorem no_low_pop (L : List (VForm × VForm)) (h : VForm) (p k : List (VForm × VForm)) (Hpos : PosL L)
    (Hnf : NfL L) (E : L = k ++ p) (Hp : ∀ b a, (b, a) ∈ p → denote b < denote h) (Hh : denote h ≤ 1) :
    p = [] := by
  match p, E, Hp with
  | [], _, _ => rfl
  | (b, a) :: p, E, Hp =>
    have Hin : (b, a) ∈ L := E ▸ List.mem_append_right k (.head _)
    have H1 := pos_ge1 b (in_nfL b a L Hnf Hin).1 (Hpos b a Hin).1
    exact (lt_irrefl _ (lt_of_le_of_lt H1 (lt_of_lt_of_le (Hp b a (.head _)) Hh))).elim

/-- Rocq: `Notation.SchutteImproper.high_Prin`. -/
theorem high_Prin (L : List (VForm × VForm)) (Hnf : NfL L) (Hpos : PosL L) (H : high L = true) : Prin (MX L) := by
  match L, Hnf, Hpos, H with
  | [], _, _, H => exact nomatch H
  | (b0, a0) :: L', ⟨⟨Hb0, _⟩, _⟩, Hpos, H =>
    have Hc := cmp_spec b0 one Hb0 one_normal
    revert H Hc
    dsimp only [high]
    cases compare b0 one with
    | lt => intro H; exact nomatch H
    | eq => intro H; exact nomatch H
    | gt =>
      intro _ Hc
      exact Prin_matrix _ _ onePlus_normal (md_complete _)
        (.inr ⟨denote b0, denote a0, .head _, lt_of_le_of_lt one_denote.ge Hc,
          (VF_nonzero a0).mpr (Hpos b0 a0 (.head _)).2⟩)

/-- Rocq: `Notation.SchutteImproper.VF_le_one`. -/
theorem le_one (h : VForm) (Hh : IsNormal h) (H : compare h one ≠ .gt) : denote h ≤ 1 := by
  have Hc := cmp_spec h one Hh one_normal
  revert H Hc
  cases compare h one with
  | lt => intro _ Hc; exact le_of_lt (lt_of_lt_of_le Hc one_denote.le)
  | eq => intro _ Hc; exact le_trans Hc.le one_denote.le
  | gt => intro H; exact absurd rfl H

/-- Rocq: `Notation.SchutteImproper.VF_is_one`. -/
theorem is_one (h : VForm) (Hh : IsNormal h) (H0 : h ≠ Z) (H : compare h one ≠ .gt) : h = one :=
  normal_form_unique h one Hh one_normal
    (equiv_trans (equiv_intro (le_one h Hh H) (pos_ge1 h Hh H0)) (equiv_symm one_denote))

/-- Rocq: `Notation.SchutteImproper.low_step`. -/
theorem low_step (L : List (VForm × VForm)) (T e : VForm) (HnfL : NfL L) (HprL : MatrixProper L) (HposL : PosL L)
    (HT : IsNormal T) (_HT0 : T ≠ Z) (He : IsNormal e) (He0 : e ≠ Z)
    (Hshape : L = [] ∨ ∃ a0, L = [(one, a0)]) :
    Good ([(one, add (lead (normalize (N (L ++ [(Z, T)])))) e)], Z) ∧
      ∀ x, Complete x → schutteColumn (MX (L ++ [(Z, T)])) 1 (denote e) x ≈
        MX [(one, add (lead (normalize (N (L ++ [(Z, T)])))) e)] (0 + x) := by
  have Hpr : IsProper (N (L ++ [(Z, T)])) := proper_snoc0 L T HprL HposL HnfL HT
  obtain ⟨Ed, Nd⟩ := normalize_correct _ Hpr
  generalize normalize (N (L ++ [(Z, T)])) = d at Ed Nd ⊢
  -- the base is a translation y ↦ c0 + y
  have Hc0 : ∃ c0, Complete c0 ∧ ∀ w, Complete w → MX L w ≈ c0 + w := by
    match Hshape with
    | .inl E => subst E; exact ⟨1, one_complete, fun w _ => equiv_refl _⟩
    | .inr ⟨a0, E⟩ =>
      subst E
      exact ⟨ω ^ denote a0, pow_complete omega_gt0 omega_complete (complete a0), low_shape a0 HnfL.1.2⟩
  obtain ⟨c0, Hc0c, Hc0⟩ := Hc0
  have HD := complete d
  have HT' := complete T
  have EB : ∀ y, Complete y → MX (L ++ [(Z, T)]) y ≈ denote d + y := fun y hy =>
    have hD : c0 + denote T ≈ denote d :=
      calc c0 + denote T ≈ c0 + (denote T + 0) := add_congr (equiv_refl _) (add_zero _).symm
        _ ≈ MX L (denote T + 0) := (Hc0 _ (add_complete HT' zero_complete)).symm
        _ ≈ schutteColumn (MX L) (denote Z) (denote T) 0 := (schutte_column0 _ _ 0).symm
        _ = MX (L ++ [(Z, T)]) 0 := (MX_snoc L Z T 0).symm
        _ ≈ denote d := Ed.symm
    calc MX (L ++ [(Z, T)]) y = schutteColumn (MX L) (denote Z) (denote T) y := MX_snoc L Z T y
      _ ≈ MX L (denote T + y) := schutte_column0 _ _ y
      _ ≈ c0 + (denote T + y) := Hc0 _ (add_complete HT' hy)
      _ ≈ c0 + denote T + y := add_assoc _ _ _
      _ ≈ denote d + y := add_congr hD (equiv_refl y)
  have HD0 : 0 < denote d := lt_of_lt_of_le ((MX_normal _).nonzero 0) Ed.ge
  obtain ⟨Nl, Hl1, Hl2⟩ := lead_spec d Nd HD0
  obtain ⟨Ele, Nle⟩ := add_reflect (lead d) e Nl He
  have He' : 0 < denote e := (VF_nonzero e).mpr He0
  have HDn := normal_addOrd (denote d) HD HD0
  refine ⟨⟨⟨⟨one_normal, Nle⟩, trivial⟩, ⟨normal_proper _ one_normal, normal_proper _ Nle, trivial⟩,
    fun b a hin => ?_, trivial⟩, fun x hx => ?_⟩
  · cases hin with
    | head =>
      exact ⟨fun h => (nomatch h),
        VF_nonzero' _ Nle (lt_of_lt_of_le He' (le_trans (le_add_left _ _) Ele.ge))⟩
    | tail _ h => exact nomatch h
  · have hle := complete (add (lead d) e)
    calc schutteColumn (MX (L ++ [(Z, T)])) 1 (denote e) x
        ≈ schutteColumn (denote d + ·) 1 (denote e) x :=
          col_base_eq _ _ 1 _ x (MX_normal _) HDn EB one_complete (complete e) hx
      _ ≈ veblen (denote d + ·) (denote e) x := schutte_column_veblen _ x _ HDn (complete e) hx
      _ ≈ ω ^ (denote (lead d) + denote e) + x :=
          low_regime_veblen (denote e) x (denote d) (denote (lead d)) HD (complete _) (complete e) hx He' Hl1 Hl2
      _ ≈ ω ^ denote (add (lead d) e) + x :=
          add_congr (equiv_intro (pow_le_pow_right ω Ele.ge) (pow_le_pow_right ω Ele.le)) (equiv_refl x)
      _ ≈ veblen (fun y => 1 + y) (denote (add (lead d) e)) x := (veblen_onePlus _ hle x hx).symm
      _ ≈ schutteColumn (fun y => 1 + y) 1 (denote (add (lead d) e)) x :=
          (schutte_column_veblen _ x _ onePlus_normal hle hx).symm
      _ ≈ MX [(one, add (lead d) e)] (0 + x) :=
          equiv_intro
            (schutte_column_monotone_full _ _ _ _ _ _ _ _ onePlus_normal.monotone onePlus_normal.monotone
              (fun _ => le_refl _) one_denote.ge (le_refl _) (zero_add x).ge)
            (schutte_column_monotone_full _ _ _ _ _ _ _ _ onePlus_normal.monotone onePlus_normal.monotone
              (fun _ => le_refl _) one_denote.le (le_refl _) (zero_add x).le)

/-- Rocq: `Notation.SchutteImproper.low_shape_of`. -/
theorem low_shape_of (L : List (VForm × VForm)) (Hnf : NfL L) (Hpr : MatrixProper L) (Hpos : PosL L)
    (Hhi : high L = false) : L = [] ∨ ∃ a0, L = [(one, a0)] := by
  match L, Hnf, Hpr, Hpos, Hhi with
  | [], _, _, _, _ => exact .inl rfl
  | (b0, a0) :: L', ⟨⟨Hb0, _⟩, Hnf'⟩, Hpr, Hpos, Hhi =>
    refine .inr ⟨a0, ?_⟩
    have Hng : compare b0 one ≠ .gt := fun E => by
      have : high ((b0, a0) :: L') = true := by
        dsimp only [high]
        rw [E]
      rw [Hhi] at this
      exact nomatch this
    have E := is_one b0 Hb0 (Hpos b0 a0 (.head _)).1 Hng
    subst E
    match L', Hnf', Hpr, Hpos with
    | [], _, _, _ => rfl
    | (b1, a1) :: L'', ⟨⟨Hb1, _⟩, _⟩, Hpr, Hpos =>
      exact (lt_irrefl _ (lt_of_le_of_lt (pos_ge1 b1 Hb1 (Hpos b1 a1 (.tail _ (.head _))).1)
        (lt_of_lt_of_le Hpr.2.2.1 one_denote.le))).elim

/-- Rocq: `Notation.SchutteImproper.step_correct`. -/
theorem step_correct (I L : List (VForm × VForm)) (T h e : VForm) (HG : Good (L, T)) (HS : Sem I (L, T))
    (Hh : IsNormal h) (He : IsNormal e) :
    Good (step (L, T) (h, e)) ∧ Sem (I ++ [(h, e)]) (step (L, T) (h, e)) := by
  obtain ⟨HnfL, HprL, HposL, HT⟩ := HG
  have HB := sem_base I L T HS
  match h, e, Hh, He with
  | Z, e, _, He =>
    -- a height-0 column adds to the pending shift
    obtain ⟨Ete, Nte⟩ := add_reflect T e HT He
    refine ⟨⟨HnfL, HprL, HposL, Nte⟩, fun x hx => ?_⟩
    show MX (I ++ [(Z, e)]) x ≈ MX L (denote (add T e) + x)
    rw [MX_snoc]
    exact equiv_trans (schutte_column0 _ _ x) (equiv_trans (HS _ (add_complete (complete e) hx))
      (normal_eq (MX_normal L) (equiv_trans (add_assoc _ _ _) (add_congr Ete.symm (equiv_refl x)))))
  | N hl, Z, _, _ =>
    -- zero entry
    refine ⟨⟨HnfL, HprL, HposL, HT⟩, fun x hx => ?_⟩
    show MX (I ++ [(N hl, Z)]) x ≈ MX L (denote T + x)
    rw [MX_snoc]
    exact equiv_trans (schutte_column_arg0 _ x (MX I) (MX_normal I).monotone) (HS x hx)
  | N hl, N el, Hh, He =>
    dsimp only [step]
    have Hh0 : N hl ≠ Z := fun h => nomatch h
    have He0 : N el ≠ Z := fun h => nomatch h
    have Hsp := split_lower_spec L (N hl) HnfL HprL Hh
    generalize N hl = h at Hh Hh0 Hsp ⊢
    generalize N el = e at He He0 ⊢
    have Hhp : 0 < denote h := (VF_nonzero h).mpr Hh0
    have Hep : 0 < denote e := (VF_nonzero e).mpr He0
    have Hsem0 : ∀ x, Complete x →
        MX (I ++ [(h, e)]) x ≈ schutteColumn (MX (L ++ [(Z, T)])) (denote h) (denote e) x := fun x hx => by
      rw [MX_snoc]
      exact col_base_eq _ _ _ _ x (MX_normal I) (MX_normal _) HB (complete h) (complete e) hx
    cases hs : splitLower h L with
    | mk k p =>
    rw [hs] at Hsp
    obtain ⟨EL, Hk, Hp⟩ := Hsp
    have ⟨Hnfk, Hnfp⟩ := nfL_sub k p (EL ▸ HnfL)
    have ⟨Hposk, Hposp⟩ := posL_app k p (EL ▸ HposL)
    have Hprk : MatrixProper k := matrix_proper_app k p (EL ▸ HprL)
    -- the principal-regime outcome, shared by two branches
    have Hprincipal : Reg (MX k) (denote h) →
        Good (mpush k h e, offset (mpush k h e) (vmax (T :: p.map Prod.snd))) ∧
        Sem (I ++ [(h, e)]) (mpush k h e, offset (mpush k h e) (vmax (T :: p.map Prod.snd))) := by
      intro Hreg
      obtain ⟨Hnf', Hpr', Hpos', Hsem'⟩ := mpush_spec k h e Hnfk Hprk Hposk Hk Hh He Hh0 He0
      obtain ⟨Hm, Hmax⟩ := vmax_entries T p HT Hnfp
      generalize vmax (T :: p.map Prod.snd) = m at Hm Hmax ⊢
      obtain ⟨Hs, Hs1, Hs2⟩ := offset_correct (mpush k h e) Hnf' Hpr' Hpos' m Hm
      generalize offset (mpush k h e) m = s at Hs Hs1 Hs2 ⊢
      refine ⟨⟨Hnf', Hpr', Hpos', Hs⟩, fun x hx => ?_⟩
      have EM : ∀ y, MX (L ++ [(Z, T)]) y = schutteMatrix (MX k) (md (p ++ [(Z, T)])) y := fun y => by
        rw [EL, ConstructiveOrdinals.List.append_assoc, MX_app]
      have hsx := add_complete (complete s) hx
      calc MX (I ++ [(h, e)]) x ≈ schutteColumn (MX (L ++ [(Z, T)])) (denote h) (denote e) x := Hsem0 x hx
        _ ≈ schutteColumn (schutteMatrix (MX k) (md (p ++ [(Z, T)]))) (denote h) (denote e) x :=
            col_base_eq _ _ _ _ x (MX_normal _) (schutte_matrix_normal _ _ (md_complete _) (MX_normal k))
              (fun y _ => by rw [EM]) (complete h) (complete e) hx
        _ ≈ schutteColumn (MX k) (denote h) (denote e) (denote s + x) := by
            refine absorb_shift_list (MX k) (md (p ++ [(Z, T)])) (denote h) (denote e) (denote m) (denote s)
              (MX_normal k) (md_complete _) (complete h) (complete e) (complete m) (complete s) Hhp Hep Hreg
              (fun b a hin => ?_) Hmax ?_ (fun y hy => ?_) x hx
            · rw [md_app] at hin
              match mem_append_cases hin with
              | .inl hin =>
                obtain ⟨b', a', hin', E1, _⟩ := in_md b a p hin
                subst E1
                exact Hp b' a' hin'
              | .inr hin =>
                rw [md_cons] at hin
                cases hin with
                | head => exact Hhp
                | tail _ h => exact nomatch h
            · exact lt_of_lt_of_le Hs1 (Hsem' _ _ onePlus_normal (complete s)).le
            · obtain ⟨i, hi⟩ := lt_elim hy
              exact le_trans (colx_mono (MX_normal k) _ _ hi)
                (le_trans (Hsem' _ _ onePlus_normal (complete_subord (complete s) i)).ge
                  (Hs2 _ (index_lt _ i)))
        _ ≈ MX (mpush k h e) (denote s + x) := (Hsem' _ _ onePlus_normal hsx).symm
    match p, T, EL, Hp, Hposp, Hnfp, HT, HB, Hsem0, Hprincipal with
    | [], Z, EL, _, _, _, _, _, Hsem0, _ =>
      -- nothing absorbed
      have Ek : k = L := by rw [EL, ConstructiveOrdinals.List.append_nil]
      subst Ek
      obtain ⟨Hnf', Hpr', Hpos', Hsem'⟩ := mpush_spec k h e HnfL HprL HposL Hk Hh He Hh0 He0
      refine ⟨⟨Hnf', Hpr', Hpos', trivial⟩, fun x hx => ?_⟩
      show MX (I ++ [(h, e)]) x ≈ MX (mpush k h e) (denote Z + x)
      refine equiv_trans (Hsem0 x hx) (equiv_trans ?_ (normal_eq (MX_normal _) (zero_add x).symm))
      refine equiv_trans ?_ (Hsem' _ x onePlus_normal hx).symm
      refine col_base_eq _ _ _ _ x (MX_normal _) (MX_normal k) (fun y _ => ?_) (complete h) (complete e) hx
      rw [MX_snoc]
      exact equiv_trans (schutte_column0 _ _ y) (normal_eq (MX_normal k) (zero_add y))
    | [], N Tl, EL, _, _, _, HT, _, Hsem0, Hprincipal =>
      -- only the pending shift is absorbed
      have Ek : k = L := by rw [EL, ConstructiveOrdinals.List.append_nil]
      subst Ek
      show Good (stepAbsorb k (N Tl) h e k []) ∧ Sem (I ++ [(h, e)]) (stepAbsorb k (N Tl) h e k [])
      dsimp only [stepAbsorb]
      cases Er : regime h k with
      | true =>
        refine Hprincipal ?_
        have Hc := cmp_spec h one Hh one_normal
        revert Er Hc
        dsimp only [regime]
        cases compare h one with
        | lt => intro Er _; exact .inl (high_Prin k HnfL HposL Er)
        | eq => intro Er _; exact .inl (high_Prin k HnfL HposL Er)
        | gt => intro _ Hc; exact .inr (lt_of_le_of_lt one_denote.ge Hc)
      | false =>
        -- the low regime
        have Hng : compare h one ≠ .gt := fun E => by
          have : regime h k = true := by dsimp only [regime]; rw [E]
          rw [Er] at this
          exact nomatch this
        have Hhi : high k = false := by
          revert Er Hng
          dsimp only [regime]
          cases compare h one with
          | lt => intro Er _; exact Er
          | eq => intro Er _; exact Er
          | gt => intro _ H; exact absurd rfl H
        have Eh := is_one h Hh Hh0 Hng
        subst Eh
        have Hshape := low_shape_of k HnfL HprL HposL Hhi
        obtain ⟨Hg, Hs⟩ := low_step k (N Tl) e HnfL HprL HposL HT (fun h => nomatch h) He He0 Hshape
        refine ⟨Hg, fun x hx => ?_⟩
        exact equiv_trans (Hsem0 x hx)
          (equiv_trans (col_height_eq _ _ _ _ x (MX_normal _) one_denote) (Hs x hx))
    | c :: p', T, EL, Hp, _, _, _, _, _, Hprincipal =>
      -- some columns are popped: the height is at least 2
      have Hh1 : compare h one = .gt := by
        cases hc : compare h one with
        | gt => rfl
        | lt =>
          exact nomatch no_low_pop L h (c :: p') k HposL HnfL EL Hp (le_one h Hh (by rw [hc]; intro h; nomatch h))
        | eq =>
          exact nomatch no_low_pop L h (c :: p') k HposL HnfL EL Hp (le_one h Hh (by rw [hc]; intro h; nomatch h))
      have Er : regime h L = true := by dsimp only [regime]; rw [Hh1]
      show Good (stepAbsorb L T h e k (c :: p')) ∧ Sem (I ++ [(h, e)]) (stepAbsorb L T h e k (c :: p'))
      dsimp only [stepAbsorb]
      rw [Er]
      refine Hprincipal (.inr ?_)
      have Hc := cmp_spec h one Hh one_normal
      rw [Hh1] at Hc
      exact lt_of_le_of_lt one_denote.ge Hc

/-! ## The normalizer -/

/-- Rocq: `Notation.SchutteImproper.process`. -/
def process (I : List (VForm × VForm)) : List (VForm × VForm) × VForm := List.foldl step ([], Z) I

/-- Rocq: `Notation.SchutteImproper.process_correct`. -/
theorem process_correct : ∀ I : List (VForm × VForm), NfL I → Good (process I) ∧ Sem I (process I) := by
  intro I
  refine ConstructiveOrdinals.List.rev_ind (fun I => NfL I → Good (process I) ∧ Sem I (process I)) ?_ ?_ I
  · intro _
    exact ⟨⟨trivial, trivial, fun _ _ h => (nomatch h), trivial⟩, fun x _ =>
      add_congr (equiv_refl _) (zero_add x).symm⟩
  · intro c I IH HI
    obtain ⟨HI, ⟨Hh, He⟩, _⟩ := (nfL_app I [c]).mp HI
    obtain ⟨HG, HS⟩ := IH HI
    show Good (List.foldl step ([], Z) (I ++ [c])) ∧ Sem (I ++ [c]) (List.foldl step ([], Z) (I ++ [c]))
    rw [foldl_append]
    show Good (step (process I) c) ∧ Sem (I ++ [c]) (step (process I) c)
    revert HG HS
    generalize process I = st
    obtain ⟨L, T⟩ := st
    obtain ⟨h, e⟩ := c
    intro HG HS
    exact step_correct I L T h e HG HS Hh He

mutual
/-- Normalize an arbitrary form. Rocq: `Notation.SchutteImproper.VF_normalizeX`. -/
def normalizeX : VForm → VForm
  | Z => Z
  | N l =>
    let st := process (normalizeXList l)
    Nnorm (st.1 ++ [(Z, st.2)])

/-- `normalizeX` on each entry: the `map` in Rocq's `VF_normalizeX`. -/
def normalizeXList : List (VForm × VForm) → List (VForm × VForm)
  | [] => []
  | (b, a) :: l => (normalizeX b, normalizeX a) :: normalizeXList l
end

/-- Rocq: `Notation.SchutteImproper.matrix_entries_eq`. -/
theorem matrix_entries_eq (xs ys : List (VForm × VForm)) (f g : Ordinal.{0} → Ordinal.{0}) (y : Ordinal.{0})
    (hf : NormalFunction f) (hg : NormalFunction g) (hfg : ∀ w, Complete w → f w ≈ g w) (hy : Complete y)
    (H : Forall2 (fun c d => denote c.1 ≈ denote d.1 ∧ denote c.2 ≈ denote d.2) xs ys) :
    schutteMatrix f (md xs) y ≈ schutteMatrix g (md ys) y := by
  induction H generalizing f g with
  | nil => exact hfg y hy
  | @cons c d xs ys hcd _ ih =>
    obtain ⟨b, a⟩ := c
    obtain ⟨b', a'⟩ := d
    obtain ⟨Eb, Ea⟩ := hcd
    refine ih _ _ (schutte_column_normal _ _ f (complete b) (complete a) hf)
      (schutte_column_normal _ _ g (complete b') (complete a') hg) fun w hw => ?_
    refine equiv_trans (col_base_eq f g _ _ w hf hg hfg (complete b) (complete a) hw) ?_
    exact equiv_intro
      (schutte_column_monotone_full g g _ _ w _ _ w hg.monotone hg.monotone (fun _ => le_refl _) Eb.le Ea.le
        (le_refl w))
      (schutte_column_monotone_full g g _ _ w _ _ w hg.monotone hg.monotone (fun _ => le_refl _) Eb.ge Ea.ge
        (le_refl w))

/-- Rocq: `Notation.SchutteImproper.VF_normalizeX_correct`. -/
theorem normalizeX_correct : ∀ x : VForm, denote (normalizeX x) ≈ denote x ∧ IsNormal (normalizeX x) := by
  refine induction' _ ⟨equiv_refl _, trivial⟩ fun xs Hxs => ?_
  have Heq : Forall2 (fun c d => denote c.1 ≈ denote d.1 ∧ denote c.2 ≈ denote d.2) (normalizeXList xs) xs := by
    induction xs with
    | nil => exact .nil
    | cons c xs ih =>
      obtain ⟨b, a⟩ := c
      exact .cons ⟨Hxs.1.1.1, Hxs.1.2.1⟩ (ih Hxs.2)
  have Hnf : NfL (normalizeXList xs) := by
    clear Heq
    induction xs with
    | nil => trivial
    | cons c xs ih =>
      obtain ⟨b, a⟩ := c
      exact ⟨⟨Hxs.1.1.2, Hxs.1.2.2⟩, ih Hxs.2⟩
  obtain ⟨HG, HS⟩ := process_correct _ Hnf
  show denote (Nnorm ((process (normalizeXList xs)).1 ++ [(Z, (process (normalizeXList xs)).2)])) ≈ denote (N xs) ∧
    IsNormal (Nnorm ((process (normalizeXList xs)).1 ++ [(Z, (process (normalizeXList xs)).2)]))
  revert HG HS
  generalize process (normalizeXList xs) = st
  obtain ⟨L, T⟩ := st
  intro HG HS
  obtain ⟨HnfL, HprL, HposL, HT⟩ := HG
  have Hpr := proper_snoc0 L T HprL HposL HnfL HT
  refine ⟨equiv_trans (Nnorm_eq _ Hpr) ?_, Nnorm_normal _ ((nfL_app L _).mpr ⟨HnfL, ⟨trivial, HT⟩, trivial⟩) Hpr⟩
  show MX (L ++ [(Z, T)]) 0 ≈ MX xs 0
  rw [MX_snoc]
  refine equiv_trans (schutte_column0 _ _ 0) ?_
  refine equiv_trans (HS 0 zero_complete).symm ?_
  exact matrix_entries_eq _ _ _ _ 0 onePlus_normal onePlus_normal (fun _ _ => equiv_refl _) zero_complete Heq

/-- On proper matrices `normalizeX` agrees with `normalize`.
Rocq: `Notation.SchutteImproper.VF_normalizeX_proper`. -/
theorem normalizeX_proper (x : VForm) (Hx : IsProper x) : normalizeX x = normalize x :=
  let ⟨E1, N1⟩ := normalizeX_correct x
  let ⟨E2, N2⟩ := normalize_correct x Hx
  normal_form_unique _ _ N1 N2 (equiv_trans E1 (equiv_symm E2))

/-- Normal forms are fixed. Rocq: `Notation.SchutteImproper.VF_normalizeX_normal`. -/
theorem normalizeX_normal (x : VForm) (Hx : IsNormal x) : normalizeX x = x :=
  let ⟨E, N1⟩ := normalizeX_correct x
  normal_form_unique _ _ N1 Hx E

/-! ## Examples, by computation -/

/-- Rocq: `Notation.SchutteImproper.VF_Γ0`. -/
def Γ0 : VForm := N [(two, one)]

/-- `[(0,1),(1,1)]`: the first fixpoint of `2 + y` is `ω`. -/
example : normalizeX (N [(Z, one), (one, one)]) = omega := rfl

/-- `[(1,1),(2,1)]`: the column `(1,1)` is absorbed; `Γ₀ > ω`, so no shift. -/
example : normalizeX (N [(one, one), (two, one)]) = Γ0 := rfl

/-- `[(0,Γ₀),(2,1)]` and `[(1,Γ₀),(2,1)]`: the first Γ-number above `Γ₀` is `Γ₁`. -/
example : normalizeX (N [(Z, Γ0), (two, one)]) = N [(two, one), (Z, one)] := rfl

example : normalizeX (N [(one, Γ0), (two, one)]) = N [(two, one), (Z, one)] := rfl

/-- Equal heights merge. -/
example : normalizeX (N [(two, one), (two, one)]) = N [(two, two)] := rfl

/-- `[(1,ω),(0,1),(1,1)]`: `φ` over `y ↦ ω^ω + 1 + y` gives `ω^(ω+1)`. -/
example : normalizeX (N [(one, omega), (Z, one), (one, one)]) = N [(one, N [(one, one), (Z, one)])] := rfl

end VForm

end ConstructiveOrdinals.SchutteMatrixNotation
