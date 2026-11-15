import ConstructiveOrdinals.Arith

/-!
# Termination of hereditary substitution, by an ordinal measure

Port of `Ordinal/HereditarySubst.v`.

Hereditary substitution `[M/x]^τ N` substitutes the canonical term `M` of type
`τ` for the variable `x` in the canonical term `N`, and reduces every redex
this creates on the spot, so that the result is canonical again (Watkins,
Cervesato, Pfenning and Walker, CMU-CS-02-101). Here its termination is given
by a single ordinal measure:

- the ordinal of a type is `|base| = 0` and `|a → b| = (|a| ⊔ |b|) + ω`, that
  is `ω · height` (`tyOrd_eq`);
- substituting into a term or spine `N` at type `τ` has measure
  `|τ| + size N`, and applying a substituted term to a spine at type `τ` has
  measure `|τ|`.

Every recursive call decreases the measure (`measure_*`), and every measure
at type `τ` lies below `ω · (height τ + 1)` (`measure_bound`). Termination is
the totality of the graph `HS` of the equations (`hsub_total`), by
well-founded induction on the measure; the equations then hold by determinism
of `HS` (`hsub_lam`, …).

Lean notes:

- `hsub_total` is defined with `WellFounded.fix` on the inverse image of `<`
  under the measure; the functions are read off with the specification lemmas,
  not by computation.
- `res_ok` spells out every case, since a wildcard would make it depend on
  `propext`.
-/

namespace ConstructiveOrdinals.HereditarySubst

open Ordinal

/-! ## Simple types and canonical terms in spine form -/

/-- Rocq: `HereditarySubst.ty`. -/
inductive Ty : Type where
  | base : Ty
  | arr : Ty → Ty → Ty

open Ty

/-- Rocq: `HereditarySubst.height`. -/
def height : Ty → Nat
  | base => 0
  | arr a b => Nat.max (height a) (height b) + 1

mutual
/-- Canonical terms, with de Bruijn indices: `lam t`, or a variable applied
to a spine of arguments. Rocq: `HereditarySubst.nf`. -/
inductive Nf : Type where
  | lam : Nf → Nf
  | ne : Nat → Spine → Nf
/-- Rocq: `HereditarySubst.spine`. -/
inductive Spine : Type where
  | snil : Spine
  | scons : Nf → Spine → Spine
end

open Nf Spine

mutual
/-- Rocq: `HereditarySubst.size`. -/
def size : Nf → Nat
  | lam t => size t + 1
  | ne _ sp => sizeSp sp + 1
/-- Rocq: `HereditarySubst.size_sp`. -/
def sizeSp : Spine → Nat
  | snil => 0
  | scons t sp => size t + sizeSp sp + 1
end

mutual
/-- Shifting the free variables `≥ k` up by one. Rocq: `HereditarySubst.lift`. -/
def lift (k : Nat) : Nf → Nf
  | lam t => lam (lift (k + 1) t)
  | ne y sp => ne (if y < k then y else y + 1) (liftSp k sp)
/-- Rocq: `HereditarySubst.lift_sp`. -/
def liftSp (k : Nat) : Spine → Spine
  | snil => snil
  | scons t sp => scons (lift k t) (liftSp k sp)
end

/-- After substituting for `x`, the variables above `x` move down.
Rocq: `HereditarySubst.unshift`. -/
def unshift (x y : Nat) : Nat := if y < x then y else y - 1

/-! ## The graph of hereditary substitution

There are three kinds of call: substitution into a term, substitution into a
spine, and application of a substituted term to a spine. -/

/-- Rocq: `HereditarySubst.call`. -/
inductive Call : Type where
  /-- `[M/x]^τ N` -/
  | CH : Ty → Nf → Nat → Nf → Call
  /-- `[M/x]^τ sp` -/
  | CS : Ty → Nf → Nat → Spine → Call
  /-- `M · sp` at `τ` -/
  | CA : Ty → Nf → Spine → Call

/-- Rocq: `HereditarySubst.res`. -/
inductive Res : Type where
  | rn : Nf → Res
  | rs : Spine → Res

open Call Res

/-- Rocq: `HereditarySubst.HS`. -/
inductive HS : Call → Res → Prop where
  | hs_lam (τ : Ty) (M : Nf) (x : Nat) (t r : Nf) :
      HS (CH τ (lift 0 M) (x + 1) t) (rn r) → HS (CH τ M x (lam t)) (rn (lam r))
  | hs_var (τ : Ty) (M : Nf) (x y : Nat) (sp sp' : Spine) :
      x ≠ y → HS (CS τ M x sp) (rs sp') → HS (CH τ M x (ne y sp)) (rn (ne (unshift x y) sp'))
  | hs_head (τ : Ty) (M : Nf) (x : Nat) (sp sp' : Spine) (r : Nf) :
      HS (CS τ M x sp) (rs sp') → HS (CA τ M sp') (rn r) → HS (CH τ M x (ne x sp)) (rn r)
  | hs_snil (τ : Ty) (M : Nf) (x : Nat) : HS (CS τ M x snil) (rs snil)
  | hs_scons (τ : Ty) (M : Nf) (x : Nat) (t : Nf) (sp : Spine) (t' : Nf) (sp' : Spine) :
      HS (CH τ M x t) (rn t') → HS (CS τ M x sp) (rs sp') → HS (CS τ M x (scons t sp)) (rs (scons t' sp'))
  | ha_nil (τ : Ty) (M : Nf) : HS (CA τ M snil) (rn M)
  | ha_beta (a b : Ty) (t N : Nf) (sp : Spine) (r1 r : Nf) :
      HS (CH a N 0 t) (rn r1) → HS (CA b r1 sp) (rn r) → HS (CA (arr a b) (lam t) (scons N sp)) (rn r)
  | ha_base (M N : Nf) (sp : Spine) : HS (CA base M (scons N sp)) (rn M)
  | ha_ne (a b : Ty) (y : Nat) (sp0 : Spine) (N : Nf) (sp : Spine) :
      HS (CA (arr a b) (ne y sp0) (scons N sp)) (rn (ne y sp0))

/-- Rocq: `HereditarySubst.HS_det`. -/
theorem HS_det {c : Call} {r1 : Res} (h : HS c r1) : ∀ {r2 : Res}, HS c r2 → r1 = r2 := by
  induction h with
  | hs_lam τ M x t r _ ih =>
    intro r2 h2; cases h2 with
    | hs_lam _ _ _ _ r' h' => cases ih h'; rfl
  | hs_var τ M x y sp sp' hxy _ ih =>
    intro r2 h2; cases h2 with
    | hs_var _ _ _ _ _ _ _ h' => cases ih h'; rfl
    | hs_head => exact absurd rfl hxy
  | hs_head τ M x sp sp' r _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | hs_var _ _ _ _ _ _ hxy => exact absurd rfl hxy
    | hs_head _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
  | hs_snil => intro r2 h2; cases h2; rfl
  | hs_scons τ M x t sp t' sp' _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | hs_scons _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; cases ih2 h2'; rfl
  | ha_nil => intro r2 h2; cases h2; rfl
  | ha_beta a b t N sp r1 r _ _ ih1 ih2 =>
    intro r2 h2; cases h2 with
    | ha_beta _ _ _ _ _ _ _ h1 h2' => cases ih1 h1; exact ih2 h2'
  | ha_base => intro r2 h2; cases h2; rfl
  | ha_ne => intro r2 h2; cases h2; rfl

/-- Calls on terms and applications return terms, calls on spines return
spines. Rocq: `HereditarySubst.res_ok`. -/
def ResOk : Call → Res → Prop
  | CS _ _ _ _, rs _ => True
  | CS _ _ _ _, rn _ => False
  | CH _ _ _ _, rn _ => True
  | CH _ _ _ _, rs _ => False
  | CA _ _ _, rn _ => True
  | CA _ _ _, rs _ => False

/-- Rocq: `HereditarySubst.HS_res_ok`. -/
theorem HS_res_ok {c : Call} {r : Res} (h : HS c r) : ResOk c r := by
  cases h <;> trivial

/-! ## The ordinal measure -/

/-- Rocq: `HereditarySubst.tyOrd`. -/
def tyOrd : Ty → Ordinal.{0}
  | base => 0
  | arr a b => (tyOrd a ⊔ tyOrd b) + ω

/-- Rocq: `HereditarySubst.measure`. -/
def measure : Call → Ordinal.{0}
  | CH τ _ _ N => tyOrd τ + ofNat (size N)
  | CS τ _ _ sp => tyOrd τ + ofNat (sizeSp sp)
  | CA τ _ _ => tyOrd τ

/-- Rocq: `HereditarySubst.tyOrd_dom`. -/
theorem tyOrd_dom (a b : Ty) (k : Nat) : tyOrd a + ofNat k < tyOrd (arr a b) :=
  lt_of_lt_of_le (add_lt_add_left _ (index_lt ω ⟨k⟩)) (add_le_add (lub_le1 _ _) (le_refl ω))

/-- Rocq: `HereditarySubst.tyOrd_cod`. -/
theorem tyOrd_cod (a b : Ty) : tyOrd b < tyOrd (arr a b) :=
  lt_of_le_of_lt (lub_le2 (tyOrd a) _)
    (lt_of_le_of_lt (add_zero _).ge (add_lt_add_left _ omega_gt0))

/-- Rocq: `HereditarySubst.add_nat_lt`. -/
theorem add_nat_lt (α : Ordinal.{0}) {m n : Nat} (h : m < n) : α + ofNat m < α + ofNat n :=
  add_lt_add_left α (ofNat_increasing h)

/-! Every recursive call decreases the measure. -/

/-- Rocq: `HereditarySubst.measure_lam`. -/
theorem measure_lam (τ : Ty) (M : Nf) (x : Nat) (t : Nf) :
    measure (CH τ (lift 0 M) (x + 1) t) < measure (CH τ M x (lam t)) :=
  add_nat_lt _ (Nat.lt_succ_self _)

/-- Rocq: `HereditarySubst.measure_spine`. -/
theorem measure_spine (τ : Ty) (M : Nf) (x y : Nat) (sp : Spine) :
    measure (CS τ M x sp) < measure (CH τ M x (ne y sp)) :=
  add_nat_lt _ (Nat.lt_succ_self _)

/-- Rocq: `HereditarySubst.measure_head`. -/
theorem measure_head (τ : Ty) (M : Nf) (x : Nat) (sp sp' : Spine) :
    measure (CA τ M sp') < measure (CH τ M x (ne x sp)) :=
  lt_of_le_of_lt (le_add_right (tyOrd τ) (ofNat 0)) (add_nat_lt _ (Nat.zero_lt_succ _))

/-- Rocq: `HereditarySubst.measure_scons_hd`. -/
theorem measure_scons_hd (τ : Ty) (M : Nf) (x : Nat) (t : Nf) (sp : Spine) :
    measure (CH τ M x t) < measure (CS τ M x (scons t sp)) :=
  add_nat_lt _ (Nat.lt_succ_of_le (Nat.le_add_right _ _))

/-- Rocq: `HereditarySubst.measure_scons_tl`. -/
theorem measure_scons_tl (τ : Ty) (M : Nf) (x : Nat) (t : Nf) (sp : Spine) :
    measure (CS τ M x sp) < measure (CS τ M x (scons t sp)) :=
  add_nat_lt _ (Nat.lt_succ_of_le (Nat.le_add_left _ _))

/-- Rocq: `HereditarySubst.measure_beta_arg`. -/
theorem measure_beta_arg (a b : Ty) (N t M : Nf) (sp : Spine) :
    measure (CH a N 0 t) < measure (CA (arr a b) M sp) :=
  tyOrd_dom a b _

/-- Rocq: `HereditarySubst.measure_beta_rest`. -/
theorem measure_beta_rest (a b : Ty) (r1 M : Nf) (sp sp' : Spine) :
    measure (CA b r1 sp) < measure (CA (arr a b) M sp') :=
  tyOrd_cod a b

/-! ## Termination: the graph is total -/

/-- Rocq: `HereditarySubst.hsub_total`. -/
def hsub_total : (c : Call) → { r // HS c r } :=
  (InvImage.wf measure lt_wf).fix fun c IH =>
    match c with
    | CH τ M x (lam t) =>
      match IH _ (measure_lam τ M x t) with
      | ⟨rn r, h⟩ => ⟨rn (lam r), .hs_lam _ _ _ _ _ h⟩
      | ⟨rs _, h⟩ => (HS_res_ok h).elim
    | CH τ M x (ne y sp) =>
      match IH _ (measure_spine τ M x y sp) with
      | ⟨rn _, h⟩ => (HS_res_ok h).elim
      | ⟨rs sp', hsp⟩ =>
        if hxy : x = y then by
          subst hxy
          exact match IH _ (measure_head τ M x sp sp') with
            | ⟨rn r, h⟩ => ⟨rn r, .hs_head _ _ _ _ _ _ hsp h⟩
            | ⟨rs _, h⟩ => (HS_res_ok h).elim
        else ⟨rn (ne (unshift x y) sp'), .hs_var _ _ _ _ _ _ hxy hsp⟩
    | CS _ _ _ snil => ⟨rs snil, .hs_snil _ _ _⟩
    | CS τ M x (scons t sp) =>
      match IH _ (measure_scons_hd τ M x t sp) with
      | ⟨rs _, h⟩ => (HS_res_ok h).elim
      | ⟨rn t', ht⟩ =>
        match IH _ (measure_scons_tl τ M x t sp) with
        | ⟨rn _, h⟩ => (HS_res_ok h).elim
        | ⟨rs sp', hsp⟩ => ⟨rs (scons t' sp'), .hs_scons _ _ _ _ _ _ _ ht hsp⟩
    | CA _ M snil => ⟨rn M, .ha_nil _ _⟩
    | CA base M (scons N sp) => ⟨rn M, .ha_base _ _ _⟩
    | CA (arr a b) (lam t) (scons N sp) =>
      match IH _ (measure_beta_arg a b N t (lam t) (scons N sp)) with
      | ⟨rs _, h⟩ => (HS_res_ok h).elim
      | ⟨rn r1, h1⟩ =>
        match IH _ (measure_beta_rest a b r1 (lam t) sp (scons N sp)) with
        | ⟨rs _, h⟩ => (HS_res_ok h).elim
        | ⟨rn r, h2⟩ => ⟨rn r, .ha_beta _ _ _ _ _ _ _ h1 h2⟩
    | CA (arr _ _) (ne y sp0) (scons N sp) => ⟨rn (ne y sp0), .ha_ne _ _ _ _ _ _⟩

/-! ## The functions and their equations -/

/-- Rocq: `HereditarySubst.hsub`. -/
def hsub (τ : Ty) (M : Nf) (x : Nat) (N : Nf) : Nf :=
  match (hsub_total (CH τ M x N)).1 with
  | rn r => r
  | rs _ => N

/-- Rocq: `HereditarySubst.hsub_sp`. -/
def hsubSp (τ : Ty) (M : Nf) (x : Nat) (sp : Spine) : Spine :=
  match (hsub_total (CS τ M x sp)).1 with
  | rs s => s
  | rn _ => sp

/-- Rocq: `HereditarySubst.happ`. -/
def happ (τ : Ty) (M : Nf) (sp : Spine) : Nf :=
  match (hsub_total (CA τ M sp)).1 with
  | rn r => r
  | rs _ => M

/-- Rocq: `HereditarySubst.hsub_spec`. -/
theorem hsub_spec {τ : Ty} {M : Nf} {x : Nat} {N r : Nf} (h : HS (CH τ M x N) (rn r)) :
    hsub τ M x N = r := by
  unfold hsub; rw [HS_det (hsub_total (CH τ M x N)).2 h]

/-- Rocq: `HereditarySubst.hsub_sp_spec`. -/
theorem hsubSp_spec {τ : Ty} {M : Nf} {x : Nat} {sp s : Spine} (h : HS (CS τ M x sp) (rs s)) :
    hsubSp τ M x sp = s := by
  unfold hsubSp; rw [HS_det (hsub_total (CS τ M x sp)).2 h]

/-- Rocq: `HereditarySubst.happ_spec`. -/
theorem happ_spec {τ : Ty} {M : Nf} {sp : Spine} {r : Nf} (h : HS (CA τ M sp) (rn r)) :
    happ τ M sp = r := by
  unfold happ; rw [HS_det (hsub_total (CA τ M sp)).2 h]

/-- Rocq: `HereditarySubst.hsub_HS`. -/
theorem hsub_HS (τ : Ty) (M : Nf) (x : Nat) (N : Nf) : HS (CH τ M x N) (rn (hsub τ M x N)) := by
  have h := (hsub_total (CH τ M x N)).2
  unfold hsub
  generalize (hsub_total (CH τ M x N)).1 = q at h ⊢
  cases q with
  | rn r => exact h
  | rs _ => exact (HS_res_ok h).elim

/-- Rocq: `HereditarySubst.hsub_sp_HS`. -/
theorem hsubSp_HS (τ : Ty) (M : Nf) (x : Nat) (sp : Spine) : HS (CS τ M x sp) (rs (hsubSp τ M x sp)) := by
  have h := (hsub_total (CS τ M x sp)).2
  unfold hsubSp
  generalize (hsub_total (CS τ M x sp)).1 = q at h ⊢
  cases q with
  | rs s => exact h
  | rn _ => exact (HS_res_ok h).elim

/-- Rocq: `HereditarySubst.happ_HS`. -/
theorem happ_HS (τ : Ty) (M : Nf) (sp : Spine) : HS (CA τ M sp) (rn (happ τ M sp)) := by
  have h := (hsub_total (CA τ M sp)).2
  unfold happ
  generalize (hsub_total (CA τ M sp)).1 = q at h ⊢
  cases q with
  | rn r => exact h
  | rs _ => exact (HS_res_ok h).elim

/-- Rocq: `HereditarySubst.hsub_lam`. -/
theorem hsub_lam (τ : Ty) (M : Nf) (x : Nat) (t : Nf) :
    hsub τ M x (lam t) = lam (hsub τ (lift 0 M) (x + 1) t) :=
  hsub_spec (.hs_lam _ _ _ _ _ (hsub_HS _ _ _ _))

/-- Rocq: `HereditarySubst.hsub_var`. -/
theorem hsub_var (τ : Ty) (M : Nf) {x y : Nat} (sp : Spine) (h : x ≠ y) :
    hsub τ M x (ne y sp) = ne (unshift x y) (hsubSp τ M x sp) :=
  hsub_spec (.hs_var _ _ _ _ _ _ h (hsubSp_HS _ _ _ _))

/-- Rocq: `HereditarySubst.hsub_head`. -/
theorem hsub_head (τ : Ty) (M : Nf) (x : Nat) (sp : Spine) :
    hsub τ M x (ne x sp) = happ τ M (hsubSp τ M x sp) :=
  hsub_spec (.hs_head _ _ _ _ _ _ (hsubSp_HS _ _ _ _) (happ_HS _ _ _))

/-- Rocq: `HereditarySubst.hsub_sp_nil`. -/
theorem hsubSp_nil (τ : Ty) (M : Nf) (x : Nat) : hsubSp τ M x snil = snil :=
  hsubSp_spec (.hs_snil _ _ _)

/-- Rocq: `HereditarySubst.hsub_sp_cons`. -/
theorem hsubSp_cons (τ : Ty) (M : Nf) (x : Nat) (t : Nf) (sp : Spine) :
    hsubSp τ M x (scons t sp) = scons (hsub τ M x t) (hsubSp τ M x sp) :=
  hsubSp_spec (.hs_scons _ _ _ _ _ _ _ (hsub_HS _ _ _ _) (hsubSp_HS _ _ _ _))

/-- Rocq: `HereditarySubst.happ_nil`. -/
theorem happ_nil (τ : Ty) (M : Nf) : happ τ M snil = M := happ_spec (.ha_nil _ _)

/-- Rocq: `HereditarySubst.happ_beta`. -/
theorem happ_beta (a b : Ty) (t N : Nf) (sp : Spine) :
    happ (arr a b) (lam t) (scons N sp) = happ b (hsub a N 0 t) sp :=
  happ_spec (.ha_beta _ _ _ _ _ _ _ (hsub_HS _ _ _ _) (happ_HS _ _ _))

/-- `[λz.z / 0]^(base→base) (0 · (1))` is `0`: the head redex `(λz.z) 0` is
reduced on the spot. Rocq example `hsub_example`. -/
theorem hsub_example :
    hsub (arr base base) (lam (ne 0 snil)) 0 (ne 0 (scons (ne 1 snil) snil)) = ne 0 snil := by
  rw [hsub_head, hsubSp_cons, hsub_var _ _ _ (fun h => Nat.noConfusion h), hsubSp_nil, happ_beta,
    hsub_head, hsubSp_nil, happ_nil, happ_nil]
  rfl

/-! ## The measure is below `ω · (height + 1)`

The ordinal of a type is `ω · height`, so every measure at type `τ` is below
`ω · (height τ + 1)`, and all measures are below `ω · ω`. -/

/-- Rocq: `HereditarySubst.omega_mul_max`. -/
theorem omega_mul_max (m n : Nat) : ofNat.{0} m ≤ ofNat n ∨ ofNat.{0} n ≤ ofNat m :=
  match Nat.le_total m n with
  | .inl h => .inl (ofNat_monotone h)
  | .inr h => .inr (ofNat_monotone h)

/-- Rocq: `HereditarySubst.tyOrd_eq`. -/
theorem tyOrd_eq : ∀ τ : Ty, tyOrd τ ≈ ω * ofNat (height τ)
  | base => equiv_symm (mul_zero ω)
  | arr a b => by
    have IHa := tyOrd_eq a
    have IHb := tyOrd_eq b
    refine equiv_trans (add_congr ?_ (equiv_refl ω)) (equiv_symm (mul_succ ω _))
    show tyOrd a ⊔ tyOrd b ≈ ω * ofNat (if height a ≤ height b then height b else height a)
    by_cases h : height a ≤ height b
    · rw [ite_eq_left h]
      exact equiv_intro (lub_least (le_trans IHa.le (mul_le_mul_left ω (ofNat_monotone h))) IHb.le)
        (le_trans IHb.ge (lub_le2 _ _))
    · rw [ite_eq_right h]
      exact equiv_intro
        (lub_least IHa.le (le_trans IHb.le (mul_le_mul_left ω
          (ofNat_monotone (Nat.le_of_lt (Nat.lt_of_not_le h))))))
        (le_trans IHa.ge (lub_le1 _ _))

/-- Rocq: `HereditarySubst.call_ty`. -/
def callTy : Call → Ty
  | CH τ _ _ _ => τ
  | CS τ _ _ _ => τ
  | CA τ _ _ => τ

/-- Rocq: `HereditarySubst.measure_bound`. -/
theorem measure_bound (c : Call) : measure c < ω * ofNat (height (callTy c) + 1) := by
  have H : ∀ τ k, tyOrd τ + ofNat k < ω * ofNat (height τ + 1) := fun τ k =>
    lt_of_lt_of_le (add_lt_add_left _ (index_lt ω ⟨k⟩))
      (le_trans (add_le_add (tyOrd_eq τ).le (le_refl ω)) (mul_succ ω _).ge)
  match c with
  | CH τ _ _ _ => exact H τ _
  | CS τ _ _ _ => exact H τ _
  | CA τ _ _ => exact lt_of_le_of_lt (add_zero (tyOrd τ)).ge (H τ 0)

/-- Rocq: `HereditarySubst.measure_below_omega2`. -/
theorem measure_below_omega2 (c : Call) : measure c < ω * ω :=
  lt_of_lt_of_le (measure_bound c) (mul_le_mul_left ω (le_of_lt (index_lt ω ⟨height (callTy c) + 1⟩)))

end ConstructiveOrdinals.HereditarySubst
