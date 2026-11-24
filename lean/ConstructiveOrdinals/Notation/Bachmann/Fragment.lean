import ConstructiveOrdinals.Notation.Bachmann.Notation
import ConstructiveOrdinals.Notation.SchutteMatrix

/-!
# Embedding Schütte's Klammersymbols in the Bachmann notation

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

A matrix with columns `(β₁,α₁), …, (βₙ,αₙ)` of decreasing heights denotes
`schutteMatrix (1+·) _ 0`. A column of height `β = 1+ζ` corresponds to the
index summand `Ω^ζ·α`, by `bach_bexpΩ_rep`; a column of height 0 (necessarily
the last) is the argument.

Ported from the Rocq file `Notation/BachmannFragment.v`.

Lean notes:

- Rocq's `Kl` computes the index and argument with local fixpoints, which
  `Kidx`/`Karg` restate. Here `Kl`, `Kidx` and `Karg` are one mutual
  structural recursion, so `Kl_N` holds by `rfl`.
- `Kinv_correct` is proved by the mutual recursions `Kinv_correct_S` and
  `Kinv_correct_I` (Rocq uses the combined scheme `BNotation_mut`).
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx SchutteMatrixNotation SchutteMatrixNotation.VForm

/-- `1+ζ = s`: undo a leading `1+` when there is one. Rocq: `Notation.BachmannFragment.BS_pred1`. -/
def BS_pred1 : BSmall → BSmall
  | BZ => BZ
  | BN BIZ s' => s'
  | BN (BIC e c r) y => BN (BIC e c r) y

mutual
/-- Rocq: `Notation.BachmannFragment.Kl`. -/
def Kl : VForm → BSmall
  | .Z => BZ
  | .N l => BN (Kidx l) (Karg l)

/-- Rocq: `Notation.BachmannFragment.Kidx`. -/
def Kidx : List (VForm × VForm) → BIdx
  | [] => BIZ
  | (.Z, _) :: l' => Kidx l'
  | (.N lb, a) :: l' => BIC (idx_small (BS_pred1 (BN (Kidx lb) (Karg lb)))) (Kl a) (Kidx l')

/-- Rocq: `Notation.BachmannFragment.Karg`. -/
def Karg : List (VForm × VForm) → BSmall
  | [] => BZ
  | (.Z, a) :: _ => Kl a
  | (.N _, _) :: l' => Karg l'
end

/-- Rocq: `Notation.BachmannFragment.Kl_N`. -/
theorem Kl_N (l : List (VForm × VForm)) : Kl (.N l) = BN (Kidx l) (Karg l) := rfl

/-- Rocq: `Notation.BachmannFragment.Kidx_shape`. -/
theorem Kidx_shape : ∀ l : List (VForm × VForm), idx_shape (Kidx l)
  | [] => trivial
  | (.Z, _) :: l => Kidx_shape l
  | (.N _, _) :: l => ⟨fun h => (nomatch h), Kidx_shape l⟩

/-- Rocq: `Notation.BachmannFragment.Kl_pos`. -/
theorem Kl_pos : ∀ a : VForm, a ≠ .Z → 0 < BS_denote (Kl a)
  | .Z, h => absurd rfl h
  | .N _, _ => BS_pos _ _

/-- Rocq: `Notation.BachmannFragment.Kidx_head_pos`. -/
theorem Kidx_head_pos : ∀ (l : List (VForm × VForm)) (e : BIdx) (c : BSmall) (r : BIdx),
    IsSparse l → Kidx l = BIC e c r → 0 < BS_denote c
  | [], _, _, _, _, E => nomatch E
  | (.Z, _) :: l, e, c, r, Hs, E => Kidx_head_pos l e c r Hs.2 E
  | (.N _, a) :: _, _, _, _, Hs, E => (BIdx.BIC.inj E).2.1 ▸ Kl_pos a Hs.1

/-- The column height `β` is `1 +` (the exponent we assign to it).
Rocq: `Notation.BachmannFragment.pred1_correct`. -/
theorem pred1_correct (b : VForm) (hb : b ≠ .Z) (Hn : IsNormal b) (Heq : denote b ≈ BS_denote (Kl b)) :
    1 + BS_denote (BS_pred1 (Kl b)) ≈ denote b := by
  match b, hb, Hn, Heq with
  | .Z, hb, _, _ => exact absurd rfl hb
  | .N l, _, Hn, Heq =>
    have hd : ∀ e c r, Kidx l = BIC e c r → 0 < BS_denote c := fun e c r => Kidx_head_pos l e c r Hn.1
    show 1 + BS_denote (BS_pred1 (BN (Kidx l) (Karg l))) ≈ denote (.N l)
    have Heq' : denote (.N l) ≈ BS_denote (BN (Kidx l) (Karg l)) := Heq
    revert hd Heq'
    generalize Kidx l = T
    cases T with
    | BIZ => intro _ Heq'; exact equiv_trans (equiv_symm (BS_denote_onePlus _)) (equiv_symm Heq')
    | BIC e c r => intro hd Heq'; exact equiv_trans (BS_denote_absorb e c r _ (hd e c r rfl)) (equiv_symm Heq')

/-- Reading a proper matrix as columns `(1+ζ, α)` followed by an argument.
Rocq: `Notation.BachmannFragment.Kmatrix`. -/
theorem Kmatrix : ∀ (l : List (VForm × VForm)) (G : Ordinal.{0} → Ordinal.{0}), (∀ x y, x ≤ y → G x ≤ G y) →
    MatrixProper l → IsSparse l → Each (fun p => IsNormal p.1 ∧ IsNormal p.2) l →
    Each (fun p => denote p.1 ≈ BS_denote (Kl p.1) ∧ denote p.2 ≈ BS_denote (Kl p.2)) l →
    schutteMatrix G (matrixDenote l) 0 ≈ schutteMatrix G (ocols (olist (Kidx l))) (BS_denote (Karg l))
  | [], _, _, _, _, _, _ => equiv_refl _
  | [(.Z, a)], G, HG, _, _, _, ⟨⟨_, Ea⟩, _⟩ =>
    equiv_trans (schutte_column0 G _ 0)
      (equiv_intro (HG _ _ (le_trans (add_zero _).le Ea.le)) (HG _ _ (le_trans Ea.ge (add_zero _).ge)))
  | (.Z, _) :: (b2, _) :: _, _, _, Hp, _, _, _ => absurd (lt_of_le_of_lt (zero_least (denote b2)) Hp.2.2.1) (lt_irrefl _)
  | (.N lb, a) :: l, G, HG, Hp, Hs, ⟨⟨Hnb, _⟩, Hn⟩, ⟨⟨Eb, Ea⟩, Heq⟩ => by
    have Hζ : 1 + BS_denote (BS_pred1 (Kl (.N lb))) ≈ denote (.N lb) := pred1_correct _ (fun h => nomatch h) Hnb Eb
    have Hl : MatrixProper l := by
      match l, Hp with
      | [], _ => exact trivial
      | (_, _) :: _, Hp => exact Hp.2.2.2
    have HG1 : ∀ x y, x ≤ y → schutteColumn G (denote (.N lb)) (denote a) x ≤ schutteColumn G (denote (.N lb)) (denote a) y :=
      fun x y h => schutte_column_monotone G _ _ x _ y HG (le_refl _) h
    show schutteMatrix (schutteColumn G (denote (.N lb)) (denote a)) (matrixDenote l) 0 ≈
      schutteMatrix (schutteColumn G (1 + BS_denote (BS_pred1 (Kl (.N lb)))) (BS_denote (Kl a)))
        (ocols (olist (Kidx l))) (BS_denote (Karg l))
    refine equiv_trans (Kmatrix l _ HG1 Hl Hs.2 Hn Heq) ?_
    have HG2 : ∀ x y, x ≤ y → schutteColumn G (1 + BS_denote (BS_pred1 (Kl (.N lb)))) (BS_denote (Kl a)) x ≤
        schutteColumn G (1 + BS_denote (BS_pred1 (Kl (.N lb)))) (BS_denote (Kl a)) y :=
      fun x y h => schutte_column_monotone G _ _ x _ y HG (le_refl _) h
    exact equiv_intro
      (schutte_matrix_monotone_func _ _ _ _ HG1 HG2 fun x =>
        schutte_column_monotone_full G G _ _ x _ _ x HG HG (fun _ => le_refl _) Hζ.ge Ea.le (le_refl _))
      (schutte_matrix_monotone_func _ _ _ _ HG2 HG1 fun x =>
        schutte_column_monotone_full G G _ _ x _ _ x HG HG (fun _ => le_refl _) Hζ.le Ea.ge (le_refl _))

theorem olist_complete : ∀ T : BIdx, Each (fun p : Ordinal.{0} × Ordinal.{0} => Complete p.1 ∧ Complete p.2) (olist T)
  | BIZ => trivial
  | BIC _ _ r => ⟨⟨BS_complete _, BS_complete _⟩, olist_complete r⟩

/-- An index below `Ω^Ω` represents the Klammersymbol whose columns are
`(1+ζ, c)` for its summands `Ω^ζ·c`. Rocq: `Notation.BachmannFragment.BI_rep`. -/
theorem BI_rep (T : BIdx) (HT : idx_shape T) :
    BRep (fun x => 1 + x) (BI_denote T) (schutteMatrix (fun x => 1 + x) (ocols (olist T))) :=
  BRep_bequiv _ onePlus_normal.monotone (ofold bzero (olist T)) (BI_denote T) _
    (bequiv_trans (ofold_osum _ _) (bequiv_trans (bequiv_badd_zero_l _) (bequiv_sym (BI_osum T HT))))
    (bfam_ofold _ _ bfam_bzero) (BI_bfam T)
    (ofold_rep _ onePlus_normal.monotone _ _ _ bfam_bzero (bach_zero_rep _ onePlus_normal) (olist_complete T))

theorem each_Kl_correct : ∀ l : List (VForm × VForm),
    Each (fun x => (IsNormal x.1 → denote x.1 ≈ BS_denote (Kl x.1)) ∧ (IsNormal x.2 → denote x.2 ≈ BS_denote (Kl x.2))) l →
    IsNormalList l → Each (fun p => denote p.1 ≈ BS_denote (Kl p.1) ∧ denote p.2 ≈ BS_denote (Kl p.2)) l
  | [], _, _ => trivial
  | (_, _) :: l, ⟨⟨h1, h2⟩, h⟩, ⟨n1, n2, n⟩ => ⟨⟨h1 n1, h2 n2⟩, each_Kl_correct l h n⟩

/-- Every Klammersymbol in normal form denotes the same ordinal as its
translation; in particular Bachmann's `φ` (at the base `1+x`) computes the
Klammersymbol, by `BS_denote_bach`. Rocq: `Notation.BachmannFragment.Kl_correct`. -/
theorem Kl_correct : ∀ x : VForm, IsNormal x → denote x ≈ BS_denote (Kl x) := by
  refine VForm.induction' _ (fun _ => equiv_refl _) fun l IHl Hn => ?_
  obtain ⟨Hs, Hp, Hn', _⟩ := Hn
  have Heq := each_Kl_correct l IHl Hn'
  exact equiv_trans (Kmatrix l _ onePlus_normal.monotone Hp Hs ((isNormalList_iff l).1 Hn') Heq)
    (equiv_symm (equiv_trans (BS_denote_bach _ _) ((BI_rep _ (Kidx_shape l)).2.1 _ (BS_complete _))))

/-! # Sanity check: the fragment below `Ω^Ω` reaches the Large Veblen Ordinal

The notations whose exponents are all small denote exactly the values of
Schütte's Klammersymbols: `Kl` translates Klammersymbols into the fragment,
and `Kinv` translates back, both preserving denotation. So the fragment's
order type is the Large Veblen Ordinal, as for `SchutteMatrix`. -/

mutual
/-- Rocq: `Notation.BachmannFragment.BS_frag`. -/
def BS_frag : BSmall → Prop
  | BZ => True
  | BN T y => BI_frag T ∧ BS_frag y

/-- Rocq: `Notation.BachmannFragment.BI_frag`. -/
def BI_frag : BIdx → Prop
  | BIZ => True
  | BIC e c r =>
    (match e with
      | BIZ => True
      | BIC BIZ s BIZ => BS_frag s
      | BIC BIZ _ (BIC _ _ _) => False
      | BIC (BIC _ _ _) _ _ => False) ∧ BS_frag c ∧ BI_frag r
end

/-- Rocq: `Notation.BachmannFragment.BI_frag_shape`. -/
theorem BI_frag_shape : ∀ T : BIdx, BI_frag T → idx_shape T
  | BIZ, _ => trivial
  | BIC BIZ _ r, ⟨_, _, Hr⟩ => ⟨fun h => (nomatch h), BI_frag_shape r Hr⟩
  | BIC (BIC BIZ _ BIZ) _ r, ⟨_, _, Hr⟩ => ⟨fun h => (nomatch h), BI_frag_shape r Hr⟩
  | BIC (BIC BIZ _ (BIC _ _ _)) _ _, ⟨He, _, _⟩ => He.elim
  | BIC (BIC (BIC _ _ _) _ _) _ _, ⟨He, _, _⟩ => He.elim

/-- Rocq: `Notation.BachmannFragment.frag_pred1`. -/
theorem frag_pred1 : ∀ u : BSmall, BS_frag u → BS_frag (BS_pred1 u)
  | BZ, h => h
  | BN BIZ _, h => h.2
  | BN (BIC _ _ _) _, h => h

/-- Rocq: `Notation.BachmannFragment.Kidx_frag`. -/
theorem Kidx_frag : ∀ l : List (VForm × VForm), Each (fun p => BS_frag (Kl p.1) ∧ BS_frag (Kl p.2)) l →
    BI_frag (Kidx l) ∧ BS_frag (Karg l)
  | [], _ => ⟨trivial, trivial⟩
  | (.Z, _) :: l, ⟨⟨_, Ha⟩, Hl⟩ => ⟨(Kidx_frag l Hl).1, Ha⟩
  | (.N _, _) :: l, ⟨⟨Hb, Ha⟩, Hl⟩ => ⟨⟨frag_pred1 _ Hb, Ha, (Kidx_frag l Hl).1⟩, (Kidx_frag l Hl).2⟩

/-- Rocq: `Notation.BachmannFragment.Kl_frag`. -/
theorem Kl_frag : ∀ x : VForm, BS_frag (Kl x) :=
  VForm.induction' _ trivial fun l IHl => Kidx_frag l IHl

mutual
/-- Rocq: `Notation.BachmannFragment.Kinv`. -/
def Kinv : BSmall → VForm
  | BZ => .Z
  | BN T y => .N (Kinv_cols T ++ [(.Z, Kinv y)])

/-- Rocq: `Notation.BachmannFragment.Kinv_cols`. -/
def Kinv_cols : BIdx → List (VForm × VForm)
  | BIZ => []
  | BIC e c r => (Kinv_exp e, Kinv c) :: Kinv_cols r

/-- Rocq: `Notation.BachmannFragment.Kinv_exp`. -/
def Kinv_exp : BIdx → VForm
  | BIZ => .N []
  | BIC BIZ s BIZ => .N [(.Z, Kinv s)]
  | BIC BIZ _ (BIC _ _ _) => .N []
  | BIC (BIC _ _ _) _ _ => .N []
end

/-- Rocq: `Notation.BachmannFragment.VF_onePlus`. -/
theorem VF_onePlus (v : VForm) : denote (.N [(.Z, v)]) ≈ 1 + denote v :=
  equiv_trans (schutte_column0 (fun x => 1 + x) (denote v) 0) (add_congr (equiv_refl 1) (add_zero _))

theorem matrixDenote_append : ∀ A B : List (VForm × VForm), matrixDenote (A ++ B) = matrixDenote A ++ matrixDenote B
  | [], _ => rfl
  | (_, _) :: A, B => congrArg _ (matrixDenote_append A B)

mutual
theorem Kinv_correct_S : ∀ x : BSmall, BS_frag x → denote (Kinv x) ≈ BS_denote x
  | BZ, _ => equiv_refl _
  | BN T y, ⟨HT, Hy⟩ => by
    have HM := Kinv_correct_I T HT
    have Hv := Kinv_correct_S y Hy
    have Hrep := BI_rep T (BI_frag_shape T HT)
    have E : denote (Kinv (BN T y)) =
        schutteColumn (schutteMatrix (fun x => 1 + x) (matrixDenote (Kinv_cols T))) 0 (denote (Kinv y)) 0 := by
      show schutteMatrix _ (matrixDenote (Kinv_cols T ++ [(.Z, Kinv y)])) 0 = _
      rw [matrixDenote_append, schutte_matrix_app]
      rfl
    rw [E]
    refine equiv_trans (schutte_column0 _ _ _) ?_
    refine equiv_trans (schutte_matrix_meq _ _ HM _ onePlus_normal.monotone _) ?_
    refine equiv_trans (ord_eq_normal _ Hrep.1 _ _ (equiv_trans (add_zero _) Hv)) ?_
    exact equiv_symm (equiv_trans (BS_denote_bach T y) (Hrep.2.1 _ (BS_complete y)))

theorem Kinv_correct_I : ∀ T : BIdx, BI_frag T → meq (matrixDenote (Kinv_cols T)) (ocols (olist T))
  | BIZ, _ => .nil
  | BIC BIZ c r, ⟨_, Hc, Hr⟩ => .cons _ _ _ _ _ _ (equiv_refl _) (Kinv_correct_S c Hc) (Kinv_correct_I r Hr)
  | BIC (BIC BIZ s BIZ) c r, ⟨He, Hc, Hr⟩ =>
    .cons _ _ _ _ _ _ (equiv_trans (VF_onePlus _) (add_congr (equiv_refl 1) (Kinv_correct_S s He)))
      (Kinv_correct_S c Hc) (Kinv_correct_I r Hr)
  | BIC (BIC BIZ _ (BIC _ _ _)) _ _, ⟨He, _, _⟩ => He.elim
  | BIC (BIC (BIC _ _ _) _ _) _ _, ⟨He, _, _⟩ => He.elim
end

/-- Rocq: `Notation.BachmannFragment.Kinv_correct`. -/
theorem Kinv_correct :
    (∀ x, BS_frag x → denote (Kinv x) ≈ BS_denote x) ∧
      ∀ T, BI_frag T → meq (matrixDenote (Kinv_cols T)) (ocols (olist T)) :=
  ⟨Kinv_correct_S, Kinv_correct_I⟩

/-- Rocq: `Notation.BachmannFragment.frag_bounded`. -/
theorem frag_bounded (x : BSmall) (Hx : BS_frag x) : BS_denote x < LargeVeblenOrdinal :=
  lt_of_le_of_lt (Kinv_correct_S x Hx).ge (VForm.bounded _)

/-- Rocq: `Notation.BachmannFragment.FragOrd`. -/
def FragOrd : Ordinal.{0} := mk { x : BSmall // BS_frag x } fun x => BS_denote x.1

/-- Rocq: `Notation.BachmannFragment.FragOrd_LVO`. -/
theorem FragOrd_LVO : FragOrd ≈ LargeVeblenOrdinal :=
  equiv_intro (limit_least fun x => frag_bounded x.1 x.2)
    (le_intro fun a =>
      let ⟨y, Hp, Hle⟩ := LVO_proper_VForm _ (index_lt _ a)
      let Hn := normalize_correct y Hp
      lt_of_le_of_lt (le_trans Hle (le_trans Hn.1.ge (Kl_correct _ Hn.2).le))
        (index_lt FragOrd ⟨Kl (normalize y), Kl_frag _⟩))

end BachmannNotation

end ConstructiveOrdinals
