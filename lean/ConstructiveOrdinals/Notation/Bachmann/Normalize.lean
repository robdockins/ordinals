import ConstructiveOrdinals.Notation.Bachmann.Bound
import ConstructiveOrdinals.Prelude.Relations

/-!
# Normalization by rewriting

Part of the notation system up to the Bachmann–Howard ordinal; see
`Notation/Bachmann/Notation` for an overview.

The rewrite system is defined on proper terms: indices are Ω-Cantor normal
forms (exponents strictly decreasing, coefficients positive), hereditarily.
Properness is a precondition of the rewrite theorems only; the rest of the
development uses `BS_nf` and the smart constructor `smartN` (`smartN_nf`,
`smartN_equal`), and arbitrary notations, with improper indices, are
normalized by `normSX` in `Notation/Bachmann/Improper`. The two are not
unified here because absorbing a summand of an index is sound only together
with a shift of the argument (`hereditary_absorption`, whose proof needs the
interpolants and absorption theory built on this file); the index
equivalences (merging equal exponents, dropping zero terms) are sound
locally. On proper terms there are two redexes, both collapsing `φ_T(y)` to a
proper subterm:

- the argument is a fixpoint: `φ_T(y) ≤ y`, so `φ_T(y) = y`;
- a coefficient `k` of `T` dominates: `φ_T(y) ≤ k`, so (by `dominance`)
  `φ_T(y) = k`.

Every reduction step strictly decreases size, so the system is strongly
normalizing, and its normal forms are exactly `BS_nf`.

Ported from the Rocq file `Notation/BachmannNormalize.v`.

Lean notes:

- Rocq's induction schemes `red_S_mut`, `red_I_mut` and `red_mut` are mutual
  structural recursions on the derivations.
- The `let n := …` of `fix_test_correct` and `coll_test_correct` is inlined.
- The matches in the statements of `nest_le` and `omax_spec` are the
  auxiliary definitions `leadLe`, `OptAll`, `OptLe` and `optOr`.
- `∃!` (not in Lean core) is spelled out as existence plus uniqueness.
- `nf_iff_irreducible` uses `reds_first_step` in place of Rocq's
  `clos_rt_rt1n`.
-/

namespace ConstructiveOrdinals

namespace BachmannNotation

open Ordinal Bachmann BOrd BSmall BIdx

/-! ## Proper terms -/

mutual
/-- Rocq: `Notation.BachmannNormalize.BS_proper`. -/
def BS_proper : BSmall → Prop
  | BZ => True
  | BN T y => BI_proper T ∧ BS_proper y

/-- Rocq: `Notation.BachmannNormalize.BI_proper`. -/
def BI_proper : BIdx → Prop
  | BIZ => True
  | BIC e c r => BI_proper e ∧ BS_proper c ∧ 0 < BS_denote c ∧ BI_proper r ∧ lead_below r e
end

/-- Rocq: `Notation.BachmannNormalize.BI_proper_pos`. -/
theorem BI_proper_pos : ∀ T : BIdx, BI_proper T → BI_pos T
  | BIZ, _ => trivial
  | BIC e _ r, ⟨He, _, Hc, Hr, _⟩ => ⟨BI_proper_pos e He, Hc, BI_proper_pos r Hr⟩

mutual
theorem nf_proper_S : ∀ x : BSmall, BS_nf x → BS_proper x
  | BZ, _ => trivial
  | BN T y, ⟨HT, Hy, _⟩ => ⟨nf_proper_I T HT, nf_proper_S y Hy⟩

theorem nf_proper_I : ∀ T : BIdx, BI_nf T → BI_proper T
  | BIZ, _ => trivial
  | BIC e c r, ⟨He, Hc, Hc0, Hr, Hl⟩ => ⟨nf_proper_I e He, nf_proper_S c Hc, Hc0, nf_proper_I r Hr, Hl⟩
end

/-- Rocq: `Notation.BachmannNormalize.nf_proper`. -/
theorem nf_proper : (∀ x, BS_nf x → BS_proper x) ∧ ∀ T, BI_nf T → BI_proper T := ⟨nf_proper_S, nf_proper_I⟩

/-- Coefficient occurrences, at any depth. Rocq: `Notation.BachmannNormalize.Kin`. -/
def Kin (k : BSmall) : BIdx → Prop
  | BIZ => False
  | BIC e c r => Kin k e ∨ k = c ∨ Kin k r

/-- Rocq: `Notation.BachmannNormalize.Kin_Kge`. -/
theorem Kin_Kge (k : BSmall) : ∀ T : BIdx, Kin k T → Kge (BS_denote k) T
  | BIZ, h => h.elim
  | BIC e _ _, .inl H => .inl (Kin_Kge k e H)
  | BIC _ _ _, .inr (.inl rfl) => .inr (.inl (le_refl _))
  | BIC _ _ r, .inr (.inr H) => .inr (.inr (Kin_Kge k r H))

/-- Rocq: `Notation.BachmannNormalize.Kin_proper`. -/
theorem Kin_proper (k : BSmall) : ∀ T : BIdx, Kin k T → BI_proper T → BS_proper k
  | BIZ, h, _ => h.elim
  | BIC e _ _, .inl H, HT => Kin_proper k e H HT.1
  | BIC _ _ _, .inr (.inl rfl), HT => HT.2.1
  | BIC _ _ r, .inr (.inr H), HT => Kin_proper k r H HT.2.2.2.1

/-- Rocq: `Notation.BachmannNormalize.Kin_size`. -/
theorem Kin_size (k : BSmall) : ∀ T : BIdx, Kin k T → BS_size k < BI_size T
  | BIZ, h => h.elim
  | BIC e c r, .inl H => Nat.lt_trans (Kin_size k e H) (size_C_e e c r)
  | BIC e _ r, .inr (.inl rfl) => size_C_c e k r
  | BIC e c r, .inr (.inr H) => Nat.lt_trans (Kin_size k r H) (size_C_r e c r)

/-! ## The index equivalence -/

/-- Rocq: `Notation.BachmannNormalize.ieq_refl`. -/
theorem ieq_refl : ∀ T : BIdx, ieq T T
  | BIZ => .nil
  | BIC e _ r => .cons _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) (ieq_refl r)

/-- Rocq: `Notation.BachmannNormalize.ieq_trans`. -/
theorem ieq_trans {a b c : BIdx} (H : ieq a b) (H' : ieq b c) : ieq a c := by
  induction H generalizing c with
  | nil => exact H'
  | cons e x r e' x' r' _ Hx _ IHe IHr =>
    cases H' with
    | cons _ _ _ e'' x'' r'' He' Hx' Hr' => exact .cons _ _ _ _ _ _ (IHe He') (equiv_trans Hx Hx') (IHr Hr')

/-- Rocq: `Notation.BachmannNormalize.ilt_ieq`. -/
theorem ilt_ieq {a b : BIdx} (H : ilt a b) : ∀ {a' b' : BIdx}, ieq a a' → ieq b b' → ilt a' b' := by
  induction H with
  | nil e c r =>
    intro a' b' Ha Hb
    cases Ha
    cases Hb
    exact .nil _ _ _
  | exp e c r e' c' r' _ IH =>
    intro a' b' Ha Hb
    cases Ha with
    | cons _ _ _ e1 c1 r1 He1 _ _ =>
      cases Hb with
      | cons _ _ _ e2 c2 r2 He2 _ _ => exact .exp _ _ _ _ _ _ (IH He1 He2)
  | coef e c r e' c' r' Hee Hcc =>
    intro a' b' Ha Hb
    cases Ha with
    | cons _ _ _ e1 c1 r1 He1 Hc1 _ =>
      cases Hb with
      | cons _ _ _ e2 c2 r2 He2 Hc2 _ =>
        exact .coef _ _ _ _ _ _ (ieq_trans (ieq_sym He1) (ieq_trans Hee He2))
          (lt_of_le_of_lt Hc1.ge (lt_of_lt_of_le Hcc Hc2.le))
  | tail e c r e' c' r' Hee Hcc _ IH =>
    intro a' b' Ha Hb
    cases Ha with
    | cons _ _ _ e1 c1 r1 He1 Hc1 Hr1 =>
      cases Hb with
      | cons _ _ _ e2 c2 r2 He2 Hc2 Hr2 =>
        exact .tail _ _ _ _ _ _ (ieq_trans (ieq_sym He1) (ieq_trans Hee He2))
          (equiv_trans (equiv_symm Hc1) (equiv_trans Hcc Hc2)) (IH Hr1 Hr2)

/-! ## The rewrite relation -/

/-- Rocq: `Notation.BachmannNormalize.redex`. -/
inductive redex : BSmall → BSmall → Prop
  /-- Rocq: `Notation.BachmannNormalize.redex_arg`. -/
  | arg (T : BIdx) (y : BSmall) : BS_denote (BN T y) ≤ BS_denote y → redex (BN T y) y
  /-- Rocq: `Notation.BachmannNormalize.redex_coef`. -/
  | coef (T : BIdx) (y k : BSmall) : Kin k T → BS_denote (BN T y) ≤ BS_denote k → redex (BN T y) k

mutual
/-- Rocq: `Notation.BachmannNormalize.red_S`. -/
inductive red_S : BSmall → BSmall → Prop
  /-- Rocq: `Notation.BachmannNormalize.red_top`. -/
  | top (x x' : BSmall) : redex x x' → red_S x x'
  /-- Rocq: `Notation.BachmannNormalize.red_idx`. -/
  | idx (T T' : BIdx) (y : BSmall) : red_I T T' → red_S (BN T y) (BN T' y)
  /-- Rocq: `Notation.BachmannNormalize.red_arg`. -/
  | arg (T : BIdx) (y y' : BSmall) : red_S y y' → red_S (BN T y) (BN T y')

/-- Rocq: `Notation.BachmannNormalize.red_I`. -/
inductive red_I : BIdx → BIdx → Prop
  /-- Rocq: `Notation.BachmannNormalize.red_exp`. -/
  | exp (e e' : BIdx) (c : BSmall) (r : BIdx) : red_I e e' → red_I (BIC e c r) (BIC e' c r)
  /-- Rocq: `Notation.BachmannNormalize.red_coef`. -/
  | coef (e : BIdx) (c c' : BSmall) (r : BIdx) : red_S c c' → red_I (BIC e c r) (BIC e c' r)
  /-- Rocq: `Notation.BachmannNormalize.red_rest`. -/
  | rest (e : BIdx) (c : BSmall) (r r' : BIdx) : red_I r r' → red_I (BIC e c r) (BIC e c r')
end

/-- Rocq: `Notation.BachmannNormalize.redex_sound`. -/
theorem redex_sound (x x' : BSmall) (H : redex x x') (Hx : BS_proper x) : BS_denote x ≈ BS_denote x' :=
  match H, Hx with
  | .arg T y H, _ => equiv_intro H (normal_inflationary (BI_normal T) _ (BS_complete y))
  | .coef T y k Hk H, Hx => equiv_intro H (dominance T y _ (BI_proper_pos T Hx.1) (Kin_Kge k T Hk))

mutual
theorem red_sound_S : ∀ {x x' : BSmall}, red_S x x' → BS_proper x → BS_denote x ≈ BS_denote x'
  | _, _, .top x x' H, Hx => redex_sound x x' H Hx
  | _, _, .idx T T' _ H, Hx => bphi_ieq T T' _ (red_sound_I H Hx.1)
  | _, _, .arg T _ _ H, Hx => ord_eq_normal _ (BI_normal T) _ _ (red_sound_S H Hx.2)

theorem red_sound_I : ∀ {T T' : BIdx}, red_I T T' → BI_proper T → ieq T T'
  | _, _, .exp _ _ _ r H, HT => .cons _ _ _ _ _ _ (red_sound_I H HT.1) (equiv_refl _) (ieq_refl r)
  | _, _, .coef e _ _ r H, HT => .cons _ _ _ _ _ _ (ieq_refl e) (red_sound_S H HT.2.1) (ieq_refl r)
  | _, _, .rest e _ _ _ H, HT => .cons _ _ _ _ _ _ (ieq_refl e) (equiv_refl _) (red_sound_I H HT.2.2.2.1)
end

/-- Rocq: `Notation.BachmannNormalize.red_sound`. -/
theorem red_sound :
    (∀ x x', red_S x x' → BS_proper x → BS_denote x ≈ BS_denote x') ∧
      ∀ T T', red_I T T' → BI_proper T → ieq T T' :=
  ⟨fun _ _ => red_sound_S, fun _ _ => red_sound_I⟩

/-- Rocq: `Notation.BachmannNormalize.lead_below_ieq`. -/
theorem lead_below_ieq (r r' e e' : BIdx) (Hr : ieq r r') (He : ieq e e') (H : lead_below r e) : lead_below r' e' :=
  match Hr, H with
  | .nil, _ => trivial
  | .cons _ _ _ _ _ _ He2 _ _, H => ilt_ieq (H : ilt _ e) He2 He

mutual
theorem red_proper_S : ∀ {x x' : BSmall}, red_S x x' → BS_proper x → BS_proper x'
  | _, _, .top _ _ (.arg _ _ _), Hx => Hx.2
  | _, _, .top _ _ (.coef T _ k Hk _), Hx => Kin_proper k T Hk Hx.1
  | _, _, .idx _ _ _ H, ⟨HT, Hy⟩ => ⟨red_proper_I H HT, Hy⟩
  | _, _, .arg _ _ _ H, ⟨HT, Hy⟩ => ⟨HT, red_proper_S H Hy⟩

theorem red_proper_I : ∀ {T T' : BIdx}, red_I T T' → BI_proper T → BI_proper T'
  | _, _, .exp e e' c r H, ⟨He, Hc, Hc0, Hr, Hl⟩ =>
    ⟨red_proper_I H He, Hc, Hc0, Hr, lead_below_ieq r r e e' (ieq_refl r) (red_sound_I H He) Hl⟩
  | _, _, .coef _ _ _ _ H, ⟨He, Hc, Hc0, Hr, Hl⟩ =>
    ⟨He, red_proper_S H Hc, lt_of_lt_of_le Hc0 (red_sound_S H Hc).le, Hr, Hl⟩
  | _, _, .rest e _ r r' H, ⟨He, Hc, Hc0, Hr, Hl⟩ =>
    ⟨He, Hc, Hc0, red_proper_I H Hr, lead_below_ieq r r' e e (red_sound_I H Hr) (ieq_refl e) Hl⟩
end

/-- Rocq: `Notation.BachmannNormalize.red_proper`. -/
theorem red_proper :
    (∀ x x', red_S x x' → BS_proper x → BS_proper x') ∧ ∀ T T', red_I T T' → BI_proper T → BI_proper T' :=
  ⟨fun _ _ => red_proper_S, fun _ _ => red_proper_I⟩

/-! ## Strong normalization -/

mutual
theorem red_size_S : ∀ {x x' : BSmall}, red_S x x' → BS_size x' < BS_size x
  | _, _, .top _ _ (.arg T y _) => size_N_y T y
  | _, _, .top _ _ (.coef T y k Hk _) => Nat.lt_trans (Kin_size k T Hk) (size_N_T T y)
  | _, _, .idx _ _ _ H => Nat.succ_lt_succ (Nat.add_lt_add_right (red_size_I H) _)
  | _, _, .arg _ _ _ H => Nat.succ_lt_succ (Nat.add_lt_add_left (red_size_S H) _)

theorem red_size_I : ∀ {T T' : BIdx}, red_I T T' → BI_size T' < BI_size T
  | _, _, .exp _ _ _ _ H => Nat.succ_lt_succ (Nat.add_lt_add_right (Nat.add_lt_add_right (red_size_I H) _) _)
  | _, _, .coef _ _ _ _ H => Nat.succ_lt_succ (Nat.add_lt_add_right (Nat.add_lt_add_left (red_size_S H) _) _)
  | _, _, .rest _ _ _ _ H => Nat.succ_lt_succ (Nat.add_lt_add_left (red_size_I H) _)
end

/-- Rocq: `Notation.BachmannNormalize.red_size`. -/
theorem red_size :
    (∀ x x', red_S x x' → BS_size x' < BS_size x) ∧ ∀ T T', red_I T T' → BI_size T' < BI_size T :=
  ⟨fun _ _ => red_size_S, fun _ _ => red_size_I⟩

/-- Rocq: `Notation.BachmannNormalize.strongly_normalizing`. -/
theorem strongly_normalizing : WellFounded fun y x => red_S x y :=
  wf_incl _ (fun y x => BS_size y < BS_size x) (fun _ _ h => red_size_S h) (wf_inverse_image _ BS_size nat_lt_wf)

/-! ## Deciding the argument redex -/

/-- Rocq: `Notation.BachmannNormalize.Klt_mono`. -/
theorem Klt_mono (z z' : Ordinal.{0}) (Hz : z ≤ z') : ∀ T : BIdx, Klt z T → Klt z' T
  | BIZ, _ => trivial
  | BIC e _ r, ⟨H1, H2, H3⟩ => ⟨Klt_mono z z' Hz e H1, lt_of_lt_of_le H2 Hz, Klt_mono z z' Hz r H3⟩

/-- Bachmann's rule, needing only the indices to be normal.
Rocq: `Notation.BachmannNormalize.nest_lt_idx`. -/
theorem nest_lt_idx (T : BIdx) (a : BSmall) (T' : BIdx) (b : BSmall) (HT : BI_nf T) (HT' : BI_nf T')
    (Hlt : ilt T T') (Ha : BS_denote a < BS_denote (BN T' b)) (Hc : Klt (BS_denote (BN T' b)) T) :
    BS_denote (BN T a) < BS_denote (BN T' b) := by
  have Hne : T' ≠ BIZ := by intro E; subst E; cases Hlt
  have Hz := (nest _ (BN_inf T' b HT' Hne) (BI_size T + 1) T (Nat.lt_succ_self _) HT Hc).1 T' HT' Hlt
  have Hi : Nonempty (bsmall (BI_denote T') ⊕ bbig (BI_denote T')) := by
    match T', HT', Hne with
    | BIZ, _, Hne => exact absurd rfl Hne
    | BIC e' c' r', HT', _ => exact BI_inh e' c' r' HT'.2.2.1
  have Hfix := zlt_value (fun x => 1 + x) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b) Hz (BI_good T')
    (BI_bfam T') Hi (BS_complete b)
  exact lt_of_lt_of_le ((BI_normal T).increasing _ _ (BS_complete (BN T' b)) Ha) Hfix

/-- `y` is a fixpoint of `φ_T` iff `y = φ_{T''}(y'')` with `T < T''` and every
coefficient of `T` below `y`. Rocq: `Notation.BachmannNormalize.fix_test`. -/
def fix_test (n : Nat) (T : BIdx) : BSmall → Bool
  | BZ => false
  | BN T'' y'' =>
    match cmpI n T T'' with
    | .lt => coefs_below n T (BN T'' y'')
    | .eq => false
    | .gt => false

/-- Rocq: `Notation.BachmannNormalize.fix_test_correct`. -/
theorem fix_test_correct (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : BS_nf y) :
    (fix_test (BI_size T + BS_size y + 1) T y = true → BS_denote (BN T y) ≤ BS_denote y) ∧
      (fix_test (BI_size T + BS_size y + 1) T y = false → BS_denote y < BS_denote (BN T y)) := by
  match y, Hy with
  | BZ, _ => exact ⟨fun h => (nomatch h), fun _ => BS_pos T BZ⟩
  | BN T'' y'', Hy =>
    have Hy' := Hy
    obtain ⟨HT'', _, Hlt'', HK''⟩ := Hy'
    have HI := (cmp_correct (BI_size T + BS_size (BN T'' y'') + 1)).2 T T''
      (Nat.lt_succ_of_le (Nat.add_le_add_left (Nat.le_of_lt (size_N_T T'' y'')) _)) HT HT''
    show ((match cmpI (BI_size T + BS_size (BN T'' y'') + 1) T T'' with
        | .lt => coefs_below (BI_size T + BS_size (BN T'' y'') + 1) T (BN T'' y'')
        | .eq => false
        | .gt => false) = true → _) ∧ ((match cmpI (BI_size T + BS_size (BN T'' y'') + 1) T T'' with
        | .lt => coefs_below (BI_size T + BS_size (BN T'' y'') + 1) T (BN T'' y'')
        | .eq => false
        | .gt => false) = false → _)
    revert HI
    cases cmpI (BI_size T + BS_size (BN T'' y'') + 1) T T'' with
    | lt =>
      intro HI
      obtain ⟨C1, C2⟩ := coefs_below_spec (BI_size T + BS_size (BN T'' y'') + 1) (BN T'' y'') T
        (fun c hc hcn => (cmp_correct _).1 c (BN T'' y'') (Nat.lt_succ_of_le (Nat.add_le_add_right hc _)) hcn Hy) HT
      revert C1 C2
      cases coefs_below (BI_size T + BS_size (BN T'' y'') + 1) T (BN T'' y'') with
      | true =>
        intro C1 _
        refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
        -- a fixpoint
        have HK := C1 rfl
        have Hne : T'' ≠ BIZ := by intro E; subst E; cases HI
        have Hz := (nest _ (BN_inf T'' y'' HT'' Hne) (BI_size T + 1) T (Nat.lt_succ_self _) HT HK).1 T'' HT'' HI
        have Hi : Nonempty (bsmall (BI_denote T'') ⊕ bbig (BI_denote T'')) := by
          match T'', HT'', Hne with
          | BIZ, _, Hne => exact absurd rfl Hne
          | BIC e' c' r', HT'', _ => exact BI_inh e' c' r' HT''.2.2.1
        exact zlt_value (fun x => 1 + x) onePlus_normal (BI_denote T) (BI_denote T'') (BS_denote y'') Hz (BI_good T'')
          (BI_bfam T'') Hi (BS_complete y'')
      | false =>
        intro _ C2
        -- a coefficient at least `y`: `y ≤ φ_T(0) < φ_T(y)`
        exact ⟨fun h => (nomatch h), fun _ => lt_of_le_of_lt (dominance T BZ _ (BI_nf_pos T HT) (C2 rfl))
          ((BI_normal T).increasing _ _ (BS_complete (BN T'' y'')) (BS_pos T'' y''))⟩
    | eq =>
      intro HI
      exact ⟨fun h => (nomatch h), fun _ => lt_of_lt_of_le
        ((BI_normal T'').increasing _ _ (BS_complete (BN T'' y'')) Hlt'') (bphi_ieq T T'' _ HI).ge⟩
    | gt =>
      intro HI
      have Hinf := normal_inflationary (BI_normal T) _ (BS_complete (BN T'' y''))
      exact ⟨fun h => (nomatch h), fun _ => nest_lt_idx T'' y'' T (BN T'' y'') HT'' HT HI (lt_of_lt_of_le Hlt'' Hinf)
        (Klt_mono _ _ Hinf T'' HK'')⟩

/-! ## The coefficient redex: collapse at the end position

`φ_T(0)` collapses to its largest coefficient `m` exactly when `T` lies below
the index of `m` and `m` occurs only at the end of `T` (the coefficient of the
last summand, or, when that coefficient is 1, the end of its exponent). For
collapse, a non-strict variant of `nest` makes `⟦T⟧` m-reachable from the
index of `m`; otherwise a strict context below `⟦T⟧` carries `m`
(`Kgs_ctx`). -/

/-- Every coefficient is below `z`, except an end occurrence, which is at
most `z`. Rocq: `Notation.BachmannNormalize.Kend`. -/
def Kend (z : Ordinal.{0}) : BIdx → Prop
  | BIZ => True
  | BIC e c r =>
    match r with
    | BIZ => (Klt z e ∧ BS_denote c ≤ z) ∨ (Kend z e ∧ BS_denote c ≈ 1)
    | BIC _ _ _ => Klt z e ∧ BS_denote c < z ∧ Kend z r

/-- Rocq: `Notation.BachmannNormalize.Klt_ieq`. -/
theorem Klt_ieq (z : Ordinal.{0}) {T T' : BIdx} (H : ieq T T') : Klt z T' → Klt z T := by
  induction H with
  | nil => exact id
  | cons _ _ _ _ _ _ _ Hc _ IHe IHr => exact fun ⟨H1, H2, H3⟩ => ⟨IHe H1, lt_of_le_of_lt Hc.le H2, IHr H3⟩

/-- Rocq: `Notation.BachmannNormalize.bleZ_bsub_l`. -/
theorem bleZ_bsub_l (z : Ordinal.{0}) (x' x y : BOrd.{0}) (H1 : bsub x' x) (H2 : bleZ z x y) : bleZ z x' y :=
  bleZ_trans z _ _ _ (.sub _ H1) H2

/-- Rocq: `Notation.BachmannNormalize.bsub_badd_zero`. -/
theorem bsub_badd_zero (x : BOrd.{0}) : bsub (badd x bzero) x := (bequiv_badd_zero_r x).1

/-- Rocq: `Notation.BachmannNormalize.BI_denote_cons`. -/
theorem BI_denote_cons (e : BIdx) (c : BSmall) (r : BIdx) :
    BI_denote (BIC e c r) = badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) := rfl

/-- The target's coefficients only need to satisfy `Kend`. Rocq: `Notation.BachmannNormalize.Klt_Kend`. -/
theorem Klt_Kend (z : Ordinal.{0}) : ∀ T : BIdx, Klt z T → Kend z T
  | BIZ, _ => trivial
  | BIC _ _ r, ⟨He, Hc, Hr⟩ =>
    have ih := Klt_Kend z r Hr
    match r, ih with
    | BIZ, _ => .inl ⟨He, le_of_lt Hc⟩
    | BIC _ _ _, ih => ⟨He, Hc, ih⟩

/-- Rocq: `Notation.BachmannNormalize.Kend_exp`. -/
theorem Kend_exp (z : Ordinal.{0}) (e : BIdx) (c : BSmall) (r : BIdx) (_Hz : OInf z) (H : Kend z (BIC e c r)) :
    Kend z e :=
  match r, H with
  | BIZ, .inl ⟨H, _⟩ => Klt_Kend z e H
  | BIZ, .inr ⟨H, _⟩ => H
  | BIC _ _ _, H => Klt_Kend z e H.1

/-- Rocq: `Notation.BachmannNormalize.Kend_coef`. -/
theorem Kend_coef (z : Ordinal.{0}) (e' : BIdx) (c' : BSmall) (r' : BIdx) (c : BSmall) (H : Kend z (BIC e' c' r'))
    (Hcc : BS_denote c < BS_denote c') (Hc0 : 0 < BS_denote c) : Klt z e' ∧ BS_denote c < z :=
  match r', H with
  | BIZ, .inl ⟨H1, H2⟩ => ⟨H1, lt_of_lt_of_le Hcc H2⟩
  | BIZ, .inr ⟨_, H2⟩ =>
    absurd (lt_of_lt_of_le Hc0 (le_zero_of_lt_one (lt_of_lt_of_le Hcc H2.le))) (lt_irrefl _)
  | BIC _ _ _, H => ⟨H.1, lt_trans Hcc H.2.1⟩

/-- Rocq: `Notation.BachmannNormalize.Kend_tail`. -/
theorem Kend_tail (z : Ordinal.{0}) (e' : BIdx) (c' : BSmall) (r' : BIdx) (Hne : r' ≠ BIZ) (H : Kend z (BIC e' c' r')) :
    Kend z r' :=
  match r', Hne, H with
  | BIZ, Hne, _ => absurd rfl Hne
  | BIC _ _ _, _, H => H.2.2

/-- The second clause of `nest_le`: the match in its Rocq statement. -/
def leadLe (z : Ordinal.{0}) (T : BIdx) (a : BOrd.{0}) : Prop :=
  match T with
  | BIZ => True
  | BIC e _ _ => (Klt z e → zlt z (BI_denote e) a) ∧ (Kend z e → bleZ z (BI_denote e) a)

/-- Rocq: `Notation.BachmannNormalize.nest_le`. -/
theorem nest_le (z : Ordinal.{0}) (Hz : OInf z) : ∀ (n : Nat) (T : BIdx), BI_size T < n → BI_nf T → Kend z T →
    (∀ T', BI_nf T' → Kend z T' → ilt T T' → bleZ z (BI_denote T) (BI_denote T')) ∧
      (∀ a, leadLe z T a → bleZ z (BI_denote T) (bexpΩ a)) := by
  intro n
  induction n with
  | zero => exact fun _ h => absurd h (Nat.not_lt_zero _)
  | succ n IH =>
  intro T hsz HT HK
  -- the reduction of a tail to its exponent
  have Tail : ∀ e r, BI_size r < n → BI_nf r → Kend z r → lead_below r e → BI_nf e → Klt z e →
      bleZ z (BI_denote r) (bexpΩ (BI_denote e)) := by
    intro e r Hr Hrn HrK Hl He HeK
    refine (IH r Hr Hrn HrK).2 _ ?_
    match r, Hr, Hrn, Hl with
    | BIZ, _, _, _ => exact trivial
    | BIC e2 c2 r2, Hr, Hrn, Hl =>
      exact ⟨fun HK2 => (nest z Hz (BI_size e2 + 1) e2 (Nat.lt_succ_self _) Hrn.1 HK2).1 e He Hl,
        fun HK2 => (IH e2 (Nat.lt_trans (size_C_e e2 c2 r2) Hr) Hrn.1 HK2).1 e He (Klt_Kend z e HeK) Hl⟩
  have B : ∀ a, leadLe z T a → bleZ z (BI_denote T) (bexpΩ a) := by
    intro a Ha
    match T, hsz, HT, HK, Ha with
    | BIZ, _, _, _, _ => exact .sub _ (bsub_bzero_l _)
    | BIC e c BIZ, _, _, .inl ⟨HKe, Hcz⟩, ⟨Ha1, _⟩ =>
      exact bleZ_bsub_l z _ (bmul (bexpΩ (BI_denote e)) (embed z)) _
        (bsub_trans (bsub_badd_zero _) (bsub_bmul_r _ _ _ (bsub_embed _ _ Hcz))) (zlt_exp z _ _ (Ha1 HKe) Hz)
    | BIC e c BIZ, _, _, .inr ⟨HKe, Hc1⟩, ⟨_, Ha2⟩ =>
      exact bleZ_bsub_l z _ (bexpΩ (BI_denote e)) _
        (bsub_trans (bsub_badd_zero _) (bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ Hc1.le)) (bsub_bmul_one _).1))
        (bleZ_exp z _ _ Hz (Ha2 HKe))
    | BIC e c (BIC e2 c2 r2), hsz, ⟨He, _, _, Hr, Hl⟩, ⟨HKe, Hcz, HKr⟩, ⟨Ha1, _⟩ =>
      have Hrb := Tail e (BIC e2 c2 r2) (size_lt_pred hsz (size_C_r e c _)) Hr HKr Hl He HKe
      exact bleZ_trans z _ (bmul (bexpΩ (BI_denote e)) (embed z)) _
        (bleZ_mono_r _ _ _ _ (bleZ_shift _ z _ _ Hrb)
          (bsub_trans (bsub_mul_succ _ _) (bsub_bmul_r _ _ _ (bsub_embed _ _ (succ_least Hcz)))))
        (zlt_exp z _ _ (Ha1 HKe) Hz)
  refine ⟨fun T' HT' HKT' Hlt => ?_, B⟩
  cases Hlt with
  | nil e' c' r' => exact .sub _ (bsub_bzero_l _)
  | exp e c r e' c' r' Hee =>
    have HKe' := Kend_exp z e' c' r' Hz HKT'
    refine bleZ_mono_r _ _ _ _ (B (BI_denote e')
      ⟨fun HKe => (nest z Hz (BI_size e + 1) e (Nat.lt_succ_self _) HT.1 HKe).1 e' HT'.1 Hee,
        fun HKe => (IH e (size_lt_pred hsz (size_C_e e c r)) HT.1 HKe).1 e' HT'.1 HKe' Hee⟩) ?_
    exact bsub_trans (bsub_P_Pz _ _ HT'.2.2.1) (bsub_le_badd _ _)
  | coef e c r e' c' r' Hee Hcc =>
    obtain ⟨He, _, Hc0, Hr, Hl⟩ := HT
    obtain ⟨HKe', _⟩ := Kend_coef z e' c' r' c HKT' Hcc Hc0
    have HKe := Klt_ieq z Hee HKe'
    have Hsub : bsub (bmul (bexpΩ (BI_denote e)) (embed (succ (BS_denote c)))) (BI_denote (BIC e' c' r')) :=
      bsub_trans (bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ (succ_least Hcc)))
        (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (ieq_bequiv Hee).1) _)) (bsub_le_badd _ _)
    match r, hsz, Hr, Hl, HK with
    | BIZ, _, _, _, _ =>
      exact .sub _ (bsub_trans (bsub_trans (bsub_badd_zero _) (bsub_bmul_r _ _ _ (bsub_embed _ _ (le_of_lt (succ_lt _)))))
        Hsub)
    | BIC e2 c2 r2, hsz, Hr, Hl, ⟨_, _, HKr⟩ =>
      have Hrb := Tail e (BIC e2 c2 r2) (size_lt_pred hsz (size_C_r e c _)) Hr HKr Hl He HKe
      exact bleZ_mono_r _ _ _ _ (bleZ_shift _ z _ _ Hrb) (bsub_trans (bsub_mul_succ _ _) Hsub)
  | tail e c r e' c' r' Hee Hcc Hrr =>
    obtain ⟨_, _, _, Hr, _⟩ := HT
    have Hr' := HT'.2.2.2.1
    have Hne' : r' ≠ BIZ := by intro E; subst E; cases Hrr
    have HKr' := Kend_tail z e' c' r' Hne' HKT'
    have Hterm : bsub (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (bmul (bexpΩ (BI_denote e')) (embed (BS_denote c'))) :=
      bsub_trans (bsub_bmul_r _ _ _ (bsub_embed _ _ Hcc.le)) (bsub_bmul_l _ _ (bsub_bexpΩ _ _ (ieq_bequiv Hee).1) _)
    match r, hsz, Hr, HK, Hrr with
    | BIZ, _, _, _, _ => exact .sub _ (bsub_trans (bsub_badd_zero _) (bsub_trans Hterm (bsub_le_badd _ _)))
    | BIC e2 c2 r2, hsz, Hr, ⟨_, _, HKr⟩, Hrr =>
      exact bleZ_mono_r z _ (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r')) _
        (bleZ_shift _ z _ _ ((IH (BIC e2 c2 r2) (size_lt_pred hsz (size_C_r e c _)) Hr HKr).1 r' Hr' HKr' Hrr))
        (bsub_badd_l _ _ Hterm (BI_denote r'))

/-- A coefficient at least `z` at a position that is not the end.
Rocq: `Notation.BachmannNormalize.Kgs`. -/
def Kgs (z : Ordinal.{0}) : BIdx → Prop
  | BIZ => False
  | BIC e c r =>
    match r with
    | BIZ => (Kge z e ∧ 1 < BS_denote c) ∨ (BS_denote c ≈ 1 ∧ Kgs z e)
    | BIC _ _ _ => Kge z e ∨ z ≤ BS_denote c ∨ Kgs z r

/-- Rocq: `Notation.BachmannNormalize.bslt_P_Pc`. -/
theorem bslt_P_Pc (P : BOrd.{0}) (c : Ordinal.{0}) (HP : bpos P) (Hc : 1 < c) : bslt P (bmul P (embed c)) := by
  cases c with
  | mk C k =>
  obtain ⟨j, Hj⟩ := lt_elim Hc
  have Hj0 : 0 < k j := lt_of_lt_of_le zero_lt_one Hj
  exact bslt_bsub_l _ (bmul P (embed (k j))) _ (bsub_P_Pz _ _ Hj0)
    (bslt_bsub_r _ (badd (bmul P (embed (k j))) P) _ (bslt_badd_pos _ bzero _ HP) (bsub_bmul_step P (embed (mk C k)) j))

/-- Rocq: `Notation.BachmannNormalize.Kgs_ctx`. -/
theorem Kgs_ctx : ∀ T : BIdx, BI_pos T → ∀ z, Kgs z T →
    ∃ (C : Ordinal.{0} → BOrd.{0}) (ζ : Ordinal.{0}), BCtx C ∧ Complete ζ ∧ z ≤ ζ ∧ bslt (C ζ) (BI_denote T)
  | BIZ, _, _, h => h.elim
  | BIC e c r, ⟨He, Hc0, Hr⟩, z, HK => by
    have ihe := fun z' (h : Kgs z' e) => Kgs_ctx e He z' h
    have ihr := fun z' (h : Kgs z' r) => Kgs_ctx r Hr z' h
    match r, Hr, HK, ihr with
    | BIZ, _, .inl ⟨HKe, Hc1⟩, _ =>
      obtain ⟨C, ζ, HC, Hζ, Hzζ, Hsub⟩ := Kge_ctx e He z HKe
      exact ⟨fun ξ => bexpΩ (C ξ), ζ, bctx_exp C HC, Hζ, Hzζ,
        bslt_bsub_l _ (bexpΩ (BI_denote e)) _ (bsub_bexpΩ _ _ Hsub)
          (bslt_bsub_r _ (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) _ (bslt_P_Pc _ _ (bpos_bexpΩ _) Hc1)
            (bsub_le_badd _ _))⟩
    | BIZ, _, .inr ⟨_, HKe⟩, _ =>
      obtain ⟨C, ζ, HC, Hζ, Hzζ, Hlt⟩ := ihe z HKe
      exact ⟨fun ξ => bexpΩ (C ξ), ζ, bctx_exp C HC, Hζ, Hzζ,
        bslt_bsub_r _ (bexpΩ (BI_denote e)) _ (bslt_bexpΩ _ _ Hlt) (bsub_trans (bsub_P_Pz _ _ Hc0) (bsub_le_badd _ _))⟩
    | BIC e2 c2 r2, Hr, HK, ihr =>
      have Hrpos : bpos (BI_denote (BIC e2 c2 r2)) := lead_pos e2 c2 r2 Hr.2.1
      have Htail : ∀ X, bsub X (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) →
          bslt X (BI_denote (BIC e c (BIC e2 c2 r2))) := fun X HX =>
        bslt_bsub_l _ _ _ HX (bslt_badd_pos _ bzero _ Hrpos)
      match HK with
      | .inl HKe =>
        obtain ⟨C, ζ, HC, Hζ, Hzζ, Hsub⟩ := Kge_ctx e He z HKe
        exact ⟨fun ξ => bexpΩ (C ξ), ζ, bctx_exp C HC, Hζ, Hzζ,
          Htail _ (bsub_trans (bsub_bexpΩ _ _ Hsub) (bsub_P_Pz _ _ Hc0))⟩
      | .inr (.inl Hzc) =>
        exact ⟨fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ), BS_denote c,
          bctx_mul _ _ (bcd_bexpΩ _ (BI_ok e).1) (bpos_bexpΩ _) bctx_embed, BS_complete c, Hzc, Htail _ (bsub_refl _)⟩
      | .inr (.inr HKr) =>
        obtain ⟨C, ζ, HC, Hζ, Hzζ, Hlt⟩ := ihr z HKr
        exact ⟨fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ), ζ,
          bctx_add _ C (idx_term_bcd e c) HC, Hζ, Hzζ, bslt_badd_r _ _ _ Hlt⟩

/-- All coefficients, at any depth, are at most `z`. Rocq: `Notation.BachmannNormalize.Kle`. -/
def Kle (z : Ordinal.{0}) : BIdx → Prop
  | BIZ => True
  | BIC e c r => Kle z e ∧ BS_denote c ≤ z ∧ Kle z r

/-- Rocq: `Notation.BachmannNormalize.Kle_lt`. -/
theorem Kle_lt (z w : Ordinal.{0}) : ∀ T : BIdx, Kle z T → z < w → Klt w T
  | BIZ, _, _ => trivial
  | BIC e _ r, ⟨H1, H2, H3⟩, Hz => ⟨Kle_lt z w e H1 Hz, lt_of_le_of_lt H2 Hz, Kle_lt z w r H3 Hz⟩

/-- Rocq: `Notation.BachmannNormalize.Kge_ieq`. -/
theorem Kge_ieq (z : Ordinal.{0}) {T T' : BIdx} (H : ieq T T') : Kge z T → Kge z T' := by
  induction H with
  | nil => exact id
  | cons _ _ _ _ _ _ _ Hc _ IHe IHr =>
    intro h
    match h with
    | .inl h => exact .inl (IHe h)
    | .inr (.inl h) => exact .inr (.inl (le_trans h Hc.le))
    | .inr (.inr h) => exact .inr (.inr (IHr h))

/-- Rocq: `Notation.BachmannNormalize.Kin_nf`. -/
theorem Kin_nf (k : BSmall) : ∀ T : BIdx, Kin k T → BI_nf T → BS_nf k
  | BIZ, h, _ => h.elim
  | BIC e _ _, .inl H, HT => Kin_nf k e H HT.1
  | BIC _ _ _, .inr (.inl rfl), HT => HT.2.1
  | BIC _ _ r, .inr (.inr H), HT => Kin_nf k r H HT.2.2.2.1

/-- Rocq: `Notation.BachmannNormalize.Kin_size'`. -/
theorem Kin_size' (k : BSmall) (T : BIdx) (H : Kin k T) : BS_size k ≤ BI_size T := Nat.le_of_lt (Kin_size k T H)

/-! ### The largest coefficient -/

/-- Rocq: `Notation.BachmannNormalize.omax`. -/
def omax (n : Nat) : Option BSmall → Option BSmall → Option BSmall
  | none, x => x
  | some u, none => some u
  | some u, some v =>
    match isLT (cmpS n u v) with
    | true => some v
    | false => some u

/-- Rocq: `Notation.BachmannNormalize.kmax`. -/
def kmax (n : Nat) : BIdx → Option BSmall
  | BIZ => none
  | BIC e c r => omax n (omax n (kmax n e) (some c)) (kmax n r)

/-- Rocq: `Notation.BachmannNormalize.kmax_ok`. -/
def kmax_ok (T : BIdx) : Option BSmall → Prop
  | none => T = BIZ
  | some m => Kin m T ∧ Kle (BS_denote m) T

/-- Rocq: `Notation.BachmannNormalize.Kle_mono`. -/
theorem Kle_mono (z z' : Ordinal.{0}) (Hz : z ≤ z') : ∀ T : BIdx, Kle z T → Kle z' T
  | BIZ, _ => trivial
  | BIC e _ r, ⟨H1, H2, H3⟩ => ⟨Kle_mono z z' Hz e H1, le_trans H2 Hz, Kle_mono z z' Hz r H3⟩

/-- `P` holds of the candidate, if any. -/
def OptAll (P : BSmall → Prop) : Option BSmall → Prop
  | none => True
  | some u => P u

/-- The candidate, if any, lies at or below `w`. -/
def OptLe (w : BSmall) : Option BSmall → Prop
  | none => True
  | some u => BS_denote u ≤ BS_denote w

/-- The candidate, or `w` if there is none. -/
def optOr (w : BSmall) : Option BSmall → BSmall
  | none => w
  | some u => u

/-- The max of two coefficient candidates. Rocq: `Notation.BachmannNormalize.omax_spec`. -/
theorem omax_spec (n : Nat) (a b : Option BSmall) (P : BSmall → Prop)
    (Hc : ∀ u v, P u → P v → OrderingCorrect (cmpS n u v) (BS_denote u) (BS_denote v))
    (Ha : OptAll P a) (Hb : OptAll P b) :
    match omax n a b with
    | none => a = none ∧ b = none
    | some w => P w ∧ (w = optOr w a ∨ w = optOr w b) ∧ OptLe w a ∧ OptLe w b := by
  match a, b, Ha, Hb with
  | none, none, _, _ => exact ⟨rfl, rfl⟩
  | none, some v, _, Hb => exact ⟨Hb, .inr rfl, trivial, le_refl _⟩
  | some u, none, Ha, _ => exact ⟨Ha, .inl rfl, le_refl _, trivial⟩
  | some u, some v, Ha, Hb =>
    obtain ⟨S1, S2⟩ := isLT_spec _ _ _ (Hc u v Ha Hb)
    show match (match isLT (cmpS n u v) with
      | true => some v
      | false => some u) with
      | none => _
      | some w => _
    revert S1 S2
    cases isLT (cmpS n u v) with
    | true => intro S1 _; exact ⟨Hb, .inr rfl, le_of_lt (S1 rfl), le_refl _⟩
    | false => intro _ S2; exact ⟨Ha, .inl rfl, le_refl _, S2 rfl⟩

/-- Rocq: `Notation.BachmannNormalize.kmax_spec`. -/
theorem kmax_spec (n : Nat) : ∀ T : BIdx, BI_nf T → BI_size T + BI_size T < n → kmax_ok T (kmax n T)
  | BIZ, _, _ => rfl
  | BIC e c r, ⟨He, Hc, _, Hr, _⟩, Hsz => by
    let P : BSmall → Prop := fun u => BS_nf u ∧ BS_size u ≤ BI_size (BIC e c r) ∧ Kin u (BIC e c r)
    have HP : ∀ u v, P u → P v → OrderingCorrect (cmpS n u v) (BS_denote u) (BS_denote v) :=
      fun u v ⟨Hu, Hsu, _⟩ ⟨Hv, Hsv, _⟩ => (cmp_correct n).1 u v (Nat.lt_of_le_of_lt (Nat.add_le_add Hsu Hsv) Hsz) Hu Hv
    have He' := kmax_spec n e He
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_e e c r)) (Nat.le_of_lt (size_C_e e c r))) Hsz)
    have Hr' := kmax_spec n r Hr
      (Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt (size_C_r e c r)) (Nat.le_of_lt (size_C_r e c r))) Hsz)
    have Pe : OptAll P (kmax n e) := by
      revert He'
      cases kmax n e with
      | none => intro _; exact trivial
      | some u =>
        intro ⟨Hin, _⟩
        exact ⟨Kin_nf u e Hin He, Nat.le_trans (Kin_size' u e Hin) (Nat.le_of_lt (size_C_e e c r)), .inl Hin⟩
    have Pc : P c := ⟨Hc, Nat.le_of_lt (size_C_c e c r), .inr (.inl rfl)⟩
    have Pr : OptAll P (kmax n r) := by
      revert Hr'
      cases kmax n r with
      | none => intro _; exact trivial
      | some u =>
        intro ⟨Hin, _⟩
        exact ⟨Kin_nf u r Hin Hr, Nat.le_trans (Kin_size' u r Hin) (Nat.le_of_lt (size_C_r e c r)), .inr (.inr Hin)⟩
    have S1 := omax_spec n (kmax n e) (some c) P HP Pe Pc
    show kmax_ok (BIC e c r) (omax n (omax n (kmax n e) (some c)) (kmax n r))
    revert S1
    cases omax n (kmax n e) (some c) with
    | none => intro S1; exact (nomatch S1.2)
    | some w1 =>
      intro ⟨Pw1, _, Lw1e, Lw1c⟩
      have S2 := omax_spec n (some w1) (kmax n r) P HP Pw1 Pr
      revert S2
      cases omax n (some w1) (kmax n r) with
      | none => intro S2; exact (nomatch S2.1)
      | some w =>
        intro ⟨Pw, _, Lw1, Lwr⟩
        have Ke : Kle (BS_denote w) e := by
          revert He' Lw1e
          cases kmax n e with
          | none => intro He' _; subst He'; exact trivial
          | some u => intro He' Lu; exact Kle_mono _ _ (le_trans Lu Lw1) e He'.2
        have Kr : Kle (BS_denote w) r := by
          revert Hr' Lwr
          cases kmax n r with
          | none => intro Hr' _; subst Hr'; exact trivial
          | some u => intro Hr' Lu; exact Kle_mono _ _ Lu r Hr'.2
        exact ⟨Pw.2.2, Ke, le_trans Lw1c Lw1, Kr⟩

/-! ### The end test -/

/-- `c ≤ 1`, for a positive normal coefficient: `c = 1`. Rocq: `Notation.BachmannNormalize.le_one`. -/
def le_one (n : Nat) (c : BSmall) : Bool :=
  match cmpS n c BS_one with
  | .gt => false
  | .lt => true
  | .eq => true

/-- Rocq: `Notation.BachmannNormalize.end_test`. -/
def end_test (n : Nat) (m : BSmall) : BIdx → Bool
  | BIZ => true
  | BIC e c r =>
    match r with
    | BIZ => coefs_below n e m || (le_one n c && end_test n m e)
    | BIC _ _ _ => coefs_below n e m && isLT (cmpS n c m) && end_test n m r

/-- Rocq: `Notation.BachmannNormalize.BS_one_nf`. -/
theorem BS_one_nf : BS_nf BS_one := ⟨trivial, trivial, BS_pos _ _, trivial⟩

/-- Rocq: `Notation.BachmannNormalize.BS_one_denote`. -/
theorem BS_one_denote : BS_denote BS_one ≈ 1 := equiv_trans (BS_denote_onePlus BZ) (add_zero 1)

/-- Rocq: `Notation.BachmannNormalize.le_one_spec`. -/
theorem le_one_spec (n : Nat) (c : BSmall) (Hc : BS_nf c) (Hc0 : 0 < BS_denote c) (Hsz : BS_size c + 3 < n) :
    (le_one n c = true → BS_denote c ≈ 1) ∧ (le_one n c = false → 1 < BS_denote c) := by
  have H := (cmp_correct n).1 c BS_one Hsz Hc BS_one_nf
  unfold le_one
  revert H
  cases cmpS n c BS_one with
  | lt => intro H; exact ⟨fun _ => equiv_intro (le_trans (le_of_lt H) BS_one_denote.le) (succ_least Hc0), fun h => (nomatch h)⟩
  | eq => intro H; exact ⟨fun _ => equiv_trans H BS_one_denote, fun h => (nomatch h)⟩
  | gt => intro H; exact ⟨fun h => (nomatch h), fun _ => lt_of_le_of_lt BS_one_denote.ge H⟩

/-- Rocq: `Notation.BachmannNormalize.end_test_spec`. -/
theorem end_test_spec (n : Nat) (m : BSmall) (Hm : BS_nf m) : ∀ T : BIdx, BI_nf T → Kle (BS_denote m) T →
    BI_size T + BS_size m + 3 < n →
    (end_test n m T = true → Kend (BS_denote m) T) ∧ (end_test n m T = false → Kgs (BS_denote m) T)
  | BIZ, _, _, _ => ⟨fun _ => trivial, fun h => (nomatch h)⟩
  | BIC e c r, ⟨He, Hc, Hc0, Hr, _⟩, ⟨HKe, HKc, HKr⟩, Hsz => by
    have hle : ∀ a, a ≤ BI_size (BIC e c r) → a + BS_size m < n := fun a ha =>
      Nat.lt_of_le_of_lt (Nat.add_le_add_right ha _) (Nat.lt_of_le_of_lt (Nat.le_add_right _ 3) Hsz)
    obtain ⟨E1, E2⟩ := end_test_spec n m Hm e He HKe
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_of_lt (size_C_e e c _)) _) _) Hsz)
    obtain ⟨R1, R2⟩ := end_test_spec n m Hm r Hr HKr
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_of_lt (size_C_r e c _)) _) _) Hsz)
    obtain ⟨C1, C2⟩ := coefs_below_spec n m e
      (fun c0 h0 hc0 => (cmp_correct n).1 c0 m (hle _ (Nat.le_trans h0 (Nat.le_of_lt (size_C_e e c _)))) hc0 Hm) He
    obtain ⟨L1, L2⟩ := isLT_spec _ _ _ ((cmp_correct n).1 c m (hle _ (Nat.le_of_lt (size_C_c e c _))) Hc Hm)
    obtain ⟨O1, O2⟩ := le_one_spec n c Hc Hc0
      (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_trans (Nat.le_of_lt (size_C_c e c _)) (Nat.le_add_right _ _)) 3) Hsz)
    clear hle
    match r, R1, R2 with
    | BIZ, _, _ =>
      show ((coefs_below n e m || (le_one n c && end_test n m e)) = true →
          (Klt (BS_denote m) e ∧ BS_denote c ≤ BS_denote m) ∨ (Kend (BS_denote m) e ∧ BS_denote c ≈ 1)) ∧
        ((coefs_below n e m || (le_one n c && end_test n m e)) = false →
          (Kge (BS_denote m) e ∧ 1 < BS_denote c) ∨ (BS_denote c ≈ 1 ∧ Kgs (BS_denote m) e))
      revert E1 E2 C1 C2 O1 O2
      cases coefs_below n e m <;> cases le_one n c <;> cases end_test n m e <;>
        intro E1 E2 C1 C2 O1 O2
      · exact ⟨fun h => (nomatch h), fun _ => .inl ⟨C2 rfl, O2 rfl⟩⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inl ⟨C2 rfl, O2 rfl⟩⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inr ⟨O1 rfl, E2 rfl⟩⟩
      · exact ⟨fun _ => .inr ⟨E1 rfl, O1 rfl⟩, fun h => (nomatch h)⟩
      all_goals exact ⟨fun _ => .inl ⟨C1 rfl, HKc⟩, fun h => (nomatch h)⟩
    | BIC e2 c2 r2, R1, R2 =>
      show ((coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2)) = true →
          Klt (BS_denote m) e ∧ BS_denote c < BS_denote m ∧ Kend (BS_denote m) (BIC e2 c2 r2)) ∧
        ((coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2)) = false →
          Kge (BS_denote m) e ∨ BS_denote m ≤ BS_denote c ∨ Kgs (BS_denote m) (BIC e2 c2 r2))
      revert C1 C2 L1 L2 R1 R2
      cases coefs_below n e m <;> cases isLT (cmpS n c m) <;> cases end_test n m (BIC e2 c2 r2) <;>
        intro C1 C2 L1 L2 R1 R2
      · exact ⟨fun h => (nomatch h), fun _ => .inl (C2 rfl)⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inl (C2 rfl)⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inl (C2 rfl)⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inl (C2 rfl)⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inr (.inl (L2 rfl))⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inr (.inl (L2 rfl))⟩
      · exact ⟨fun h => (nomatch h), fun _ => .inr (.inr (R2 rfl))⟩
      · exact ⟨fun _ => ⟨C1 rfl, L1 rfl, R1 rfl⟩, fun h => (nomatch h)⟩

/-! ### Deciding the coefficient redex -/

/-- Rocq: `Notation.BachmannNormalize.coll_test`. -/
def coll_test (n : Nat) (T : BIdx) : Option BSmall :=
  match kmax n T with
  | none => none
  | some BZ => none
  | some (BN Tm ym) =>
    match cmpI n T Tm with
    | .lt =>
      match end_test n (BN Tm ym) T with
      | true => some (BN Tm ym)
      | false => none
    | .eq => none
    | .gt => none

theorem two_le_four_mul (k : Nat) : k + k ≤ 4 * k :=
  (Nat.two_mul k) ▸ Nat.mul_le_mul_right k (by decide)

/-- Rocq: `Notation.BachmannNormalize.coll_test_correct`. -/
theorem coll_test_correct (T : BIdx) (HT : BI_nf T) :
    (∀ m, coll_test (4 * BI_size T + 4 + 1) T = some m → Kin m T ∧ BS_denote (BN T BZ) ≤ BS_denote m) ∧
      (coll_test (4 * BI_size T + 4 + 1) T = none → Klt (BS_denote (BN T BZ)) T) := by
  have Hn : BI_size T + BI_size T < 4 * BI_size T + 4 + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans (two_le_four_mul _) (Nat.le_add_right _ 4))
  have HK := kmax_spec (4 * BI_size T + 4 + 1) T HT Hn
  unfold coll_test
  revert HK
  cases kmax (4 * BI_size T + 4 + 1) T with
  | none => intro HK; subst HK; exact ⟨fun _ h => (nomatch h), fun _ => trivial⟩
  | some m =>
    intro ⟨Hin, Hle⟩
    have Hm : BS_nf m := Kin_nf m T Hin HT
    have Hms := Kin_size m T Hin
    have Hdom : BS_denote m ≤ BS_denote (BN T BZ) := dominance T BZ _ (BI_nf_pos T HT) (Kin_Kge m T Hin)
    match m, Hin, Hle, Hm, Hms, Hdom with
    | BZ, _, Hle, _, _, _ => exact ⟨fun _ h => (nomatch h), fun _ => Kle_lt _ _ T Hle (BS_pos T BZ)⟩
    | BN Tm ym, Hin, Hle, Hm, Hms, Hdom =>
      dsimp only
      have Hm' := Hm
      obtain ⟨HTm, _, Hymlt, HKm⟩ := Hm'
      have HI := (cmp_correct (4 * BI_size T + 4 + 1)).2 T Tm
        (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_lt (Nat.lt_trans (size_N_T Tm ym) Hms)) _) Hn) HT HTm
      -- `m` below the value suffices for the coefficient condition
      have Hlt_ok : BS_denote (BN Tm ym) < BS_denote (BN T BZ) → Klt (BS_denote (BN T BZ)) T := fun H =>
        Kle_lt _ _ T Hle H
      revert HI
      cases cmpI (4 * BI_size T + 4 + 1) T Tm with
      | lt =>
        intro HI
        obtain ⟨N1, N2⟩ := end_test_spec (4 * BI_size T + 4 + 1) (BN Tm ym) Hm T HT Hle
          (Nat.lt_succ_of_le (Nat.add_le_add (Nat.le_trans (Nat.add_le_add_left (Nat.le_of_lt Hms) _) (two_le_four_mul _))
            (by decide)))
        revert N1 N2
        cases end_test (4 * BI_size T + 4 + 1) (BN Tm ym) T with
        | true =>
          intro N1 _
          refine ⟨fun m' Em' => ?_, fun h => (nomatch h)⟩
          cases Em'
          refine ⟨Hin, ?_⟩
          have Hne : Tm ≠ BIZ := by intro E; subst E; cases HI
          have Hz := BN_inf Tm ym HTm Hne
          have HB := (nest_le _ Hz (BI_size T + 1) T (Nat.lt_succ_self _) HT (N1 rfl)).1 Tm HTm (Klt_Kend _ _ HKm) HI
          have Hi : Nonempty (bsmall (BI_denote Tm) ⊕ bbig (BI_denote Tm)) := by
            match Tm, HTm, Hne with
            | BIZ, _, Hne => exact absurd rfl Hne
            | BIC e' c' r', HTm, _ => exact BI_inh e' c' r' HTm.2.2.1
          exact bleZ_sound (fun x => 1 + x) onePlus_normal _ _ _ HB (BI_denote Tm) (bsub_refl _) (BI_good Tm)
            (BI_bfam Tm) (BS_complete (BN Tm ym))
            (bfix_value_full (fun x => 1 + x) onePlus_normal _ _ (BI_good Tm) Hi (BS_complete ym))
        | false =>
          intro _ N2
          refine ⟨fun _ h => (nomatch h), fun _ => Hlt_ok ?_⟩
          obtain ⟨C, ζ, HC, Hζ, Hmζ, Hlt⟩ := Kgs_ctx T (BI_nf_pos T HT) _ (N2 rfl)
          exact lt_of_le_of_lt (le_trans Hmζ (bctx_dom (fun x => 1 + x) onePlus_normal C HC ζ Hζ))
            (bphi_strict (fun x => 1 + x) onePlus_normal _ _ Hlt (BI_good T) (BI_bfam T))
      | eq =>
        intro HI
        exact ⟨fun _ h => (nomatch h), fun _ =>
          absurd (Kge_lt _ _ Tm (Kge_ieq _ HI (Kin_Kge _ _ Hin)) HKm) (lt_irrefl _)⟩
      | gt =>
        intro HI
        exact ⟨fun _ h => (nomatch h), fun _ => Hlt_ok (nest_lt_idx Tm ym T BZ HTm HT HI
          (lt_of_lt_of_le Hymlt Hdom) (Klt_mono _ _ Hdom Tm HKm))⟩

/-! ## The normalizer -/

/-- Rocq: `Notation.BachmannNormalize.smartN`. -/
def smartN (T : BIdx) (y : BSmall) : BSmall :=
  match fix_test (BI_size T + BS_size y + 1) T y with
  | true => y
  | false =>
    match y with
    | BZ =>
      match coll_test (4 * BI_size T + 4 + 1) T with
      | some m => m
      | none => BN T BZ
    | BN Ty yy => BN T (BN Ty yy)

mutual
/-- Rocq: `Notation.BachmannNormalize.normS`. -/
def normS : BSmall → BSmall
  | BZ => BZ
  | BN T y => smartN (normI T) (normS y)

/-- Rocq: `Notation.BachmannNormalize.normI`. -/
def normI : BIdx → BIdx
  | BIZ => BIZ
  | BIC e c r => BIC (normI e) (normS c) (normI r)
end

/-- Rocq: `Notation.BachmannNormalize.Klt_of_Kge`. -/
theorem Klt_of_Kge (w : Ordinal.{0}) : ∀ T : BIdx, (∀ z, Kge z T → z < w) → Klt w T
  | BIZ, _ => trivial
  | BIC e _ r, H =>
    ⟨Klt_of_Kge w e (fun z hz => H z (.inl hz)), H _ (.inr (.inl (le_refl _))),
      Klt_of_Kge w r (fun z hz => H z (.inr (.inr hz)))⟩

/-- Coefficients of `T` lie below `φ_T(y)` once `y` is positive.
Rocq: `Notation.BachmannNormalize.Klt_pos_arg`. -/
theorem Klt_pos_arg (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : 0 < BS_denote y) : Klt (BS_denote (BN T y)) T :=
  Klt_of_Kge _ T fun z Hz =>
    lt_of_le_of_lt (dominance T BZ z (BI_nf_pos T HT) Hz) ((BI_normal T).increasing _ _ (BS_complete y) Hy)

/-- Rocq: `Notation.BachmannNormalize.smartN_correct`. -/
theorem smartN_correct (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : BS_nf y) :
    BS_nf (smartN T y) ∧ BS_denote (smartN T y) ≈ BS_denote (BN T y) := by
  obtain ⟨F1, F2⟩ := fix_test_correct T y HT Hy
  unfold smartN
  revert F1 F2
  cases fix_test (BI_size T + BS_size y + 1) T y with
  | true => intro F1 _; exact ⟨Hy, equiv_intro (normal_inflationary (BI_normal T) _ (BS_complete y)) (F1 rfl)⟩
  | false =>
    intro _ F2
    have Hlt := F2 rfl
    match y, Hy, Hlt with
    | BZ, _, _ =>
      obtain ⟨C1, C2⟩ := coll_test_correct T HT
      revert C1 C2
      cases coll_test (4 * BI_size T + 4 + 1) T with
      | some m =>
        intro C1 _
        obtain ⟨Hin, Hle⟩ := C1 m rfl
        exact ⟨Kin_nf m T Hin HT, equiv_intro (dominance T BZ _ (BI_nf_pos T HT) (Kin_Kge _ _ Hin)) Hle⟩
      | none => intro _ C2; exact ⟨⟨HT, trivial, BS_pos T BZ, C2 rfl⟩, equiv_refl _⟩
    | BN Ty yy, Hy, Hlt => exact ⟨⟨HT, Hy, Hlt, Klt_pos_arg T _ HT (BS_pos Ty yy)⟩, equiv_refl _⟩

mutual
theorem normalize_correct_S : ∀ x : BSmall, BS_proper x → BS_nf (normS x) ∧ BS_denote (normS x) ≈ BS_denote x
  | BZ, _ => ⟨trivial, equiv_refl _⟩
  | BN T y, ⟨HT, Hy⟩ =>
    let ⟨HT', HTe⟩ := normalize_correct_I T HT
    let ⟨Hy', Hye⟩ := normalize_correct_S y Hy
    let ⟨N1, N2⟩ := smartN_correct _ _ HT' Hy'
    ⟨N1, equiv_trans N2 (equiv_trans (bphi_ieq _ _ _ HTe) (ord_eq_normal _ (BI_normal T) _ _ Hye))⟩

theorem normalize_correct_I : ∀ T : BIdx, BI_proper T → BI_nf (normI T) ∧ ieq (normI T) T
  | BIZ, _ => ⟨trivial, .nil⟩
  | BIC e c r, ⟨He, Hc, Hc0, Hr, Hl⟩ =>
    let ⟨He', Hee⟩ := normalize_correct_I e He
    let ⟨Hc', Hce⟩ := normalize_correct_S c Hc
    let ⟨Hr', Hre⟩ := normalize_correct_I r Hr
    ⟨⟨He', Hc', lt_of_lt_of_le Hc0 Hce.ge, Hr', lead_below_ieq r (normI r) e (normI e) (ieq_sym Hre) (ieq_sym Hee) Hl⟩,
      .cons _ _ _ _ _ _ Hee Hce Hre⟩
end

/-- Rocq: `Notation.BachmannNormalize.normalize_correct`. -/
theorem normalize_correct :
    (∀ x, BS_proper x → BS_nf (normS x) ∧ BS_denote (normS x) ≈ BS_denote x) ∧
      ∀ T, BI_proper T → BI_nf (normI T) ∧ ieq (normI T) T :=
  ⟨normalize_correct_S, normalize_correct_I⟩

/-- Rocq: `Notation.BachmannNormalize.smartN_nf`. -/
theorem smartN_nf (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : BS_nf y) : BS_nf (smartN T y) :=
  (smartN_correct T y HT Hy).1

/-- Rocq: `Notation.BachmannNormalize.smartN_equal`. -/
theorem smartN_equal (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : BS_nf y) :
    BS_denote (smartN T y) ≈ BS_denote (BN T y) :=
  (smartN_correct T y HT Hy).2

/-- Rocq: `Notation.BachmannNormalize.normS_nf`. -/
theorem normS_nf (x : BSmall) (Hx : BS_proper x) : BS_nf (normS x) := (normalize_correct_S x Hx).1

/-- Rocq: `Notation.BachmannNormalize.normS_equal`. -/
theorem normS_equal (x : BSmall) (Hx : BS_proper x) : BS_denote (normS x) ≈ BS_denote x :=
  (normalize_correct_S x Hx).2

/-! ## Reduction to the normal form -/

/-- Rocq: `Notation.BachmannNormalize.reds`. -/
abbrev reds : BSmall → BSmall → Prop := ClosReflTrans red_S

/-- Rocq: `Notation.BachmannNormalize.redsI`. -/
abbrev redsI : BIdx → BIdx → Prop := ClosReflTrans red_I

/-- Rocq: `Notation.BachmannNormalize.reds_trans`. -/
theorem reds_trans (x y z : BSmall) (H1 : reds x y) (H2 : reds y z) : reds x z := .trans H1 H2

/-- Rocq: `Notation.BachmannNormalize.reds_BN_idx`. -/
theorem reds_BN_idx (T T' : BIdx) (y : BSmall) (H : redsI T T') : reds (BN T y) (BN T' y) := by
  induction H with
  | step h => exact .step (.idx _ _ _ h)
  | refl => exact .refl _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Rocq: `Notation.BachmannNormalize.reds_BN_arg`. -/
theorem reds_BN_arg (T : BIdx) (y y' : BSmall) (H : reds y y') : reds (BN T y) (BN T y') := by
  induction H with
  | step h => exact .step (.arg _ _ _ h)
  | refl => exact .refl _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Rocq: `Notation.BachmannNormalize.redsI_exp`. -/
theorem redsI_exp (e e' : BIdx) (c : BSmall) (r : BIdx) (H : redsI e e') : redsI (BIC e c r) (BIC e' c r) := by
  induction H with
  | step h => exact .step (.exp _ _ _ _ h)
  | refl => exact .refl _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Rocq: `Notation.BachmannNormalize.redsI_coef`. -/
theorem redsI_coef (e : BIdx) (c c' : BSmall) (r : BIdx) (H : reds c c') : redsI (BIC e c r) (BIC e c' r) := by
  induction H with
  | step h => exact .step (.coef _ _ _ _ h)
  | refl => exact .refl _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Rocq: `Notation.BachmannNormalize.redsI_rest`. -/
theorem redsI_rest (e : BIdx) (c : BSmall) (r r' : BIdx) (H : redsI r r') : redsI (BIC e c r) (BIC e c r') := by
  induction H with
  | step h => exact .step (.rest _ _ _ _ h)
  | refl => exact .refl _
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- Rocq: `Notation.BachmannNormalize.smartN_reds`. -/
theorem smartN_reds (T : BIdx) (y : BSmall) (HT : BI_nf T) (Hy : BS_nf y) : reds (BN T y) (smartN T y) := by
  obtain ⟨F1, _⟩ := fix_test_correct T y HT Hy
  unfold smartN
  revert F1
  cases fix_test (BI_size T + BS_size y + 1) T y with
  | true => intro F1; exact .step (.top _ _ (.arg _ _ (F1 rfl)))
  | false =>
    intro _
    match y with
    | BN _ _ => exact .refl _
    | BZ =>
      obtain ⟨C1, _⟩ := coll_test_correct T HT
      revert C1
      cases coll_test (4 * BI_size T + 4 + 1) T with
      | none => intro _; exact .refl _
      | some m =>
        intro C1
        obtain ⟨Hin, Hle⟩ := C1 m rfl
        exact .step (.top _ _ (.coef _ _ _ Hin Hle))

mutual
theorem normalize_reds_S : ∀ x : BSmall, BS_proper x → reds x (normS x)
  | BZ, _ => .refl _
  | BN T y, ⟨HT, Hy⟩ =>
    .trans (reds_BN_idx _ _ y (normalize_reds_I T HT))
      (.trans (reds_BN_arg _ _ _ (normalize_reds_S y Hy))
        (smartN_reds _ _ (normalize_correct_I T HT).1 (normalize_correct_S y Hy).1))

theorem normalize_reds_I : ∀ T : BIdx, BI_proper T → redsI T (normI T)
  | BIZ, _ => .refl _
  | BIC e c r, ⟨He, Hc, _, Hr, _⟩ =>
    .trans (redsI_exp _ _ _ _ (normalize_reds_I e He))
      (.trans (redsI_coef _ _ _ _ (normalize_reds_S c Hc)) (redsI_rest _ _ _ _ (normalize_reds_I r Hr)))
end

/-- Rocq: `Notation.BachmannNormalize.normalize_reds`. -/
theorem normalize_reds : (∀ x, BS_proper x → reds x (normS x)) ∧ ∀ T, BI_proper T → redsI T (normI T) :=
  ⟨normalize_reds_S, normalize_reds_I⟩

/-! ## Normal forms are exactly the irreducible terms -/

/-- Rocq: `Notation.BachmannNormalize.Kin_Klt`. -/
theorem Kin_Klt (k : BSmall) (z : Ordinal.{0}) : ∀ T : BIdx, Kin k T → Klt z T → BS_denote k < z
  | BIZ, h, _ => h.elim
  | BIC e _ _, .inl H, HK => Kin_Klt k z e H HK.1
  | BIC _ _ _, .inr (.inl rfl), HK => HK.2.1
  | BIC _ _ r, .inr (.inr H), HK => Kin_Klt k z r H HK.2.2

mutual
theorem nf_irreducible_S : ∀ {x x' : BSmall}, red_S x x' → ¬ BS_nf x
  | _, _, .top _ _ (.arg _ y H), ⟨_, _, Hlt, _⟩ => lt_irrefl (BS_denote y) (lt_of_lt_of_le Hlt H)
  | _, _, .top _ _ (.coef T _ k Hk H), ⟨_, _, _, HK⟩ => lt_irrefl (BS_denote k) (lt_of_lt_of_le (Kin_Klt k _ T Hk HK) H)
  | _, _, .idx _ _ _ H, ⟨HT, _⟩ => nf_irreducible_I H HT
  | _, _, .arg _ _ _ H, ⟨_, Hy, _⟩ => nf_irreducible_S H Hy

theorem nf_irreducible_I : ∀ {T T' : BIdx}, red_I T T' → ¬ BI_nf T
  | _, _, .exp _ _ _ _ H, ⟨He, _⟩ => nf_irreducible_I H He
  | _, _, .coef _ _ _ _ H, ⟨_, Hc, _⟩ => nf_irreducible_S H Hc
  | _, _, .rest _ _ _ _ H, ⟨_, _, _, Hr, _⟩ => nf_irreducible_I H Hr
end

/-- Rocq: `Notation.BachmannNormalize.nf_irreducible`. -/
theorem nf_irreducible : (∀ x x', red_S x x' → ¬ BS_nf x) ∧ ∀ T T', red_I T T' → ¬ BI_nf T :=
  ⟨fun _ _ => nf_irreducible_S, fun _ _ => nf_irreducible_I⟩

/-- A reduction sequence is empty or starts with a step. -/
theorem reds_first_step {x w : BSmall} (H : reds x w) : x = w ∨ ∃ x', red_S x x' := by
  induction H with
  | step h => exact .inr ⟨_, h⟩
  | refl => exact .inl rfl
  | trans _ _ ih1 ih2 =>
    match ih1 with
    | .inr e => exact .inr e
    | .inl rfl => exact ih2

/-- Rocq: `Notation.BachmannNormalize.nf_iff_irreducible`. -/
theorem nf_iff_irreducible (x : BSmall) (Hx : BS_proper x) : BS_nf x ↔ ¬ ∃ x', red_S x x' :=
  ⟨fun Hn ⟨_, H⟩ => nf_irreducible_S H Hn, fun Hirr =>
    match reds_first_step (normalize_reds_S x Hx) with
    | .inl E => E ▸ normS_nf x Hx
    | .inr e => absurd e Hirr⟩

/-! ## Unique normal forms and confluence -/

/-- Rocq: `Notation.BachmannNormalize.reds_sound`. -/
theorem reds_sound (x y : BSmall) (Hx : BS_proper x) (H : reds x y) : BS_proper y ∧ BS_denote x ≈ BS_denote y := by
  induction H with
  | step h => exact ⟨red_proper_S h Hx, red_sound_S h Hx⟩
  | refl => exact ⟨Hx, equiv_refl _⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨Hy, Hxy⟩ := ih1 Hx
    obtain ⟨Hz, Hyz⟩ := ih2 Hy
    exact ⟨Hz, equiv_trans Hxy Hyz⟩

/-- Rocq: `Notation.BachmannNormalize.normalizes`. -/
def normalizes (x y : BSmall) : Prop := reds x y ∧ BS_nf y

/-- Rocq: `Notation.BachmannNormalize.normalizes_iff`. -/
theorem normalizes_iff (x y : BSmall) (Hx : BS_proper x) : normalizes x y ↔ BS_nf y ∧ BS_denote x ≈ BS_denote y :=
  ⟨fun ⟨H, Hy⟩ => ⟨Hy, (reds_sound x y Hx H).2⟩, fun ⟨Hy, Heq⟩ =>
    have E : normS x = y := BS_nf_unique _ _ (normS_nf x Hx) Hy (equiv_trans (normS_equal x Hx) Heq)
    ⟨E ▸ normalize_reds_S x Hx, Hy⟩⟩

/-- Rocq: `Notation.BachmannNormalize.normalizes_unique`. -/
theorem normalizes_unique (x : BSmall) (Hx : BS_proper x) :
    ∃ y, normalizes x y ∧ ∀ y', normalizes x y' → y' = normS x :=
  ⟨normS x, ⟨normalize_reds_S x Hx, normS_nf x Hx⟩, fun y Hy =>
    let ⟨Hy, Heq⟩ := (normalizes_iff x y Hx).1 Hy
    BS_nf_unique _ _ Hy (normS_nf x Hx) (equiv_trans (equiv_symm Heq) (equiv_symm (normS_equal x Hx)))⟩

/-- Rocq: `Notation.BachmannNormalize.reduce_confluent`. -/
theorem reduce_confluent (x y1 y2 : BSmall) (Hx : BS_proper x) (H1 : reds x y1) (H2 : reds x y2) :
    ∃ w, reds y1 w ∧ reds y2 w :=
  let ⟨Hy1, E1⟩ := reds_sound x y1 Hx H1
  let ⟨Hy2, E2⟩ := reds_sound x y2 Hx H2
  have E : normS y2 = normS y1 := BS_nf_unique _ _ (normS_nf y2 Hy2) (normS_nf y1 Hy1)
    (equiv_trans (normS_equal y2 Hy2) (equiv_trans (equiv_symm E2) (equiv_trans E1 (equiv_symm (normS_equal y1 Hy1)))))
  ⟨normS y1, normalize_reds_S y1 Hy1, E ▸ normalize_reds_S y2 Hy2⟩

/-! ## Examples, by computation -/

/-- `φ_1(ε₀) = ω + ε₀ = ε₀`: the argument is a fixpoint. -/
example : normS (BN BI_one (BN BI_Ω BZ)) = BN BI_Ω BZ := rfl

/-- `φ_{Ω^0·ε₀}(0) = ω^{ε₀} = ε₀`: collapse to the coefficient. -/
example : normS (BN (BIC BIZ (BN BI_Ω BZ) BIZ) BZ) = BN BI_Ω BZ := rfl

/-- `ε₀ + 1 = ω^{ε₀} + 1` is normal, and `φ_{Ω^0·(ε₀+1)}(0) = ω^{ε₀+1}` does not
collapse. Rocq: `Notation.BachmannNormalize.BS_ε0_plus1`. -/
def BS_ε0_plus1 : BSmall := BN (BIC BIZ (BN BI_Ω BZ) BIZ) BS_one

example : normS BS_ε0_plus1 = BS_ε0_plus1 := rfl

example : normS (BN (BIC BIZ BS_ε0_plus1 BIZ) BZ) = BN (BIC BIZ BS_ε0_plus1 BIZ) BZ := rfl

end BachmannNotation

end ConstructiveOrdinals
