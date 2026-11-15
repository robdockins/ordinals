import ConstructiveOrdinals.Notation.V
import ConstructiveOrdinals.Notation.CantorProduct

/-!
# Strong normalization of combinatory System T below ε₀

Port of `Ordinal/SystemTCL.v`.

Gödel's T in combinatory form, with pairs, and the ordinal assignment of
Howard and Schütte: each term gets a vector of ordinals below ε₀, indexed by
type levels, and every reduction step decreases it. The projections reduce
like `K`, so pairs need nothing new.

Lean notes:

- Rocq's canonical structure `ONo` is the `Sized ON` instance.
- Rocq's `Proper` instances for the natural product are
  `NaturalProduct.nmul_monotone` and `NaturalProduct.nmul_congr`.
- Rocq's `Opaque` hint has no counterpart: Lean's unifier does not unfold the
  operations on V forms here.
- Arithmetic on levels is done by hand, since `omega` uses `propext`.
-/

namespace ConstructiveOrdinals.SystemTCL

open Ordinal VNotation NaturalProduct

/-! ## Ordinals: normal V forms

The vectors hold normal V forms (`VNotation`), with the natural sum `♯`, the
natural product and `ω ^ ·`, computed on normal forms. On notations these
satisfy the usual laws constructively (`CantorProduct`). -/

/-- Normal V forms. Rocq: `SystemTCL.ON`. -/
structure ON : Type where
  /-- The form. -/
  v : VForm
  /-- It is normal. -/
  n : VForm.IsNormal v

/-- Rocq: `SystemTCL.ON_denote`. -/
def ON.denote (x : ON) : Ordinal.{0} := x.v.denote

/-- Rocq: `SystemTCL.ONo`. -/
instance instSizedON : Sized ON := ⟨ON.denote⟩

/-- Rocq: `SystemTCL.ON_complete`. -/
theorem ON_complete (x : ON) : Complete (sz x) := VForm.complete x.v

/-- Rocq: `SystemTCL.ON_below_ε0`. -/
theorem ON_below_ε0 (x : ON) : sz x < ε 0 := VForm.below_ε₀ x.v

/-- Rocq: `SystemTCL.nadd_ok`. -/
theorem nadd_ok {a b : VForm} (ha : a.IsNormal) (hb : b.IsNormal) :
    (VForm.nadd a b).denote ≈ a.denote ♯ b.denote ∧ (VForm.nadd a b).IsNormal :=
  let h := VForm.reflects_nadd a.denote a ⟨equiv_refl _, ha⟩ b.denote b ⟨equiv_refl _, hb⟩
  ⟨equiv_symm h.1, h.2⟩

/-- Rocq: `SystemTCL.nmul_ok`. -/
theorem nmul_ok {a b : VForm} (ha : a.IsNormal) (hb : b.IsNormal) :
    (VForm.nmul a b).denote ≈ nmul a.denote b.denote ∧ (VForm.nmul a b).IsNormal :=
  let h := VForm.reflects_nmul a.denote a ⟨equiv_refl _, ha⟩ b.denote b ⟨equiv_refl _, hb⟩
  ⟨equiv_symm h.1, h.2⟩

/-- Rocq: `SystemTCL.oadd`. -/
def oadd (x y : ON) : ON := ⟨VForm.nadd x.v y.v, (nadd_ok x.n y.n).2⟩
/-- Rocq: `SystemTCL.omul`. -/
def omul (x y : ON) : ON := ⟨VForm.nmul x.v y.v, (nmul_ok x.n y.n).2⟩
/-- Rocq: `SystemTCL.oexp`. -/
def oexp (x : ON) : ON := ⟨.V x.v .Z, ⟨x.n, trivial, trivial⟩⟩
/-- Rocq: `SystemTCL.ozero`. -/
def ozero : ON := ⟨.Z, trivial⟩
/-- Rocq: `SystemTCL.oone`. -/
def oone : ON := oexp ozero
/-- Rocq: `SystemTCL.onat`. -/
def onat : Nat → ON
  | 0 => ozero
  | n + 1 => oadd (onat n) oone
/-- Rocq: `SystemTCL.oomega`. -/
def oomega : ON := oexp oone

@[inherit_doc] scoped infixr:65 " ⊕' " => oadd
@[inherit_doc] scoped infixr:70 " ⊗' " => omul

/-- Rocq: `SystemTCL.nmul_le_mor`. -/
theorem nmul_le_mor {x y a b : Ordinal.{0}} (h : x ≤ y) (h' : a ≤ b) : nmul x a ≤ nmul y b :=
  nmul_monotone h h'

/-- Rocq: `SystemTCL.nmul_eq_mor`. -/
theorem nmul_eq_mor {x y a b : Ordinal.{0}} (h : x ≈ y) (h' : a ≈ b) : nmul x a ≈ nmul y b :=
  nmul_congr h h'

/-- Rocq: `SystemTCL.oadd_eq`. -/
theorem oadd_eq (x y : ON) : sz (x ⊕' y) ≈ sz x ♯ sz y := (nadd_ok x.n y.n).1

/-- Rocq: `SystemTCL.omul_eq`. -/
theorem omul_eq (x y : ON) : sz (x ⊗' y) ≈ nmul (sz x) (sz y) := (nmul_ok x.n y.n).1

/-- Rocq: `SystemTCL.oexp_eq`. -/
theorem oexp_eq (x : ON) : sz (oexp x) ≈ ω ^ sz x :=
  equiv_trans (veblen_onePlus _ (VForm.complete x.v) _ zero_complete) (add_zero _)

/-- Rocq: `SystemTCL.ozero_eq`. -/
theorem ozero_eq : sz ozero ≈ 0 := equiv_refl _

/-- Rocq: `SystemTCL.oone_eq`. -/
theorem oone_eq : sz oone ≈ 1 := equiv_trans (oexp_eq ozero) (pow_zero ω)

/-- Rocq: `SystemTCL.onat_eq`. -/
theorem onat_eq : ∀ n : Nat, sz (onat n) ≈ ofNat n
  | 0 => equiv_refl _
  | n + 1 =>
    equiv_trans (oadd_eq (onat n) oone)
      (equiv_trans (nadd_congr (onat_eq n) oone_eq)
        (equiv_trans (nadd_succ2 _ _) (succ_congruence (nadd_zero_r _))))

/-- Rocq: `SystemTCL.oomega_eq`. -/
theorem oomega_eq : sz oomega ≈ ω :=
  equiv_trans (oexp_eq oone) (equiv_trans (pow_congr (equiv_refl ω) oone_eq) (pow_one' omega_gt0))

/-! The laws of the natural product, on notations. -/

/-- Rocq: `SystemTCL.omul_comm`. -/
theorem omul_comm (x y : ON) : sz (x ⊗' y) ≈ sz (y ⊗' x) :=
  CantorProduct.cantor_nmul_comm VForm.hasCantorDecomposition x.v y.v x.n y.n

/-- Rocq: `SystemTCL.omul_assoc`. -/
theorem omul_assoc (x y z : ON) : sz ((x ⊗' y) ⊗' z) ≈ sz (x ⊗' (y ⊗' z)) :=
  CantorProduct.cantor_nmul_assoc VForm.hasCantorDecomposition x.v y.v z.v x.n y.n z.n

/-- Rocq: `SystemTCL.omul_distr`. -/
theorem omul_distr (x y z : ON) : sz (x ⊗' (y ⊕' z)) ≈ sz (x ⊗' y) ♯ sz (x ⊗' z) :=
  equiv_trans (CantorProduct.cantor_nmul_nadd_r VForm.hasCantorDecomposition x.v y.v z.v x.n y.n z.n)
    (oadd_eq (x ⊗' y) (x ⊗' z))

/-- Rocq: `SystemTCL.oexp_mul`. -/
theorem oexp_mul (a b : ON) : sz (oexp a ⊗' oexp b) ≈ sz (oexp (a ⊕' b)) :=
  CantorProduct.cantor_nmul_exp VForm.hasCantorDecomposition a.v b.v a.n b.n

/-! ## Powers of ω times an ordinal

`wm w y` is `ω^w ⊗ y`. These are the only products the assignment uses. -/

/-- Rocq: `SystemTCL.wm`. -/
def wm (w y : ON) : ON := oexp w ⊗' y

/-- Rocq: `SystemTCL.wm_eq`. -/
theorem wm_eq (w y : ON) : sz (wm w y) ≈ nmul (ω ^ sz w) (sz y) :=
  equiv_trans (omul_eq _ _) (nmul_congr (oexp_eq w) (equiv_refl _))

/-- Rocq: `SystemTCL.oadd_mono`. -/
theorem oadd_mono {x x' y y' : ON} (hx : sz x ≤ sz x') (hy : sz y ≤ sz y') :
    sz (x ⊕' y) ≤ sz (x' ⊕' y') :=
  le_trans (oadd_eq x y).le (le_trans (nadd_le_nadd hx hy) (oadd_eq x' y').ge)

/-- Rocq: `SystemTCL.oadd_le1`. -/
theorem oadd_le1 (x y : ON) : sz x ≤ sz (x ⊕' y) := le_trans (nadd_le1 _ _) (oadd_eq x y).ge

/-- Rocq: `SystemTCL.oadd_le2`. -/
theorem oadd_le2 (x y : ON) : sz y ≤ sz (x ⊕' y) := le_trans (nadd_le2 _ _) (oadd_eq x y).ge

/-- Rocq: `SystemTCL.oadd_lt1`. -/
theorem oadd_lt1 (x y : ON) (h : 0 < sz y) : sz x < sz (x ⊕' y) :=
  lt_of_le_of_lt (nadd_zero_r (sz x)).ge (lt_of_lt_of_le (nadd_increasing2 _ h) (oadd_eq x y).ge)

/-- Rocq: `SystemTCL.oadd_lt2`. -/
theorem oadd_lt2 (x y : ON) (h : 0 < sz x) : sz y < sz (x ⊕' y) :=
  lt_of_le_of_lt (nadd_zero_l (sz y)).ge (lt_of_lt_of_le (nadd_increasing1 _ h) (oadd_eq x y).ge)

/-- Rocq: `SystemTCL.oadd_pos1`. -/
theorem oadd_pos1 (x y : ON) (h : 0 < sz x) : 0 < sz (x ⊕' y) := lt_of_lt_of_le h (oadd_le1 x y)

/-- Rocq: `SystemTCL.oexp_mono`. -/
theorem oexp_mono {x y : ON} (h : sz x ≤ sz y) : sz (oexp x) ≤ sz (oexp y) :=
  le_trans (oexp_eq x).le (le_trans (pow_le_pow_right ω h) (oexp_eq y).ge)

/-- Rocq: `SystemTCL.oexp_increasing`. -/
theorem oexp_increasing {x y : ON} (h : sz x < sz y) : sz (oexp x) < sz (oexp y) :=
  lt_of_le_of_lt (oexp_eq x).le (lt_of_lt_of_le (pow_lt_pow_right omega_gt1 h) (oexp_eq y).ge)

/-- Rocq: `SystemTCL.oexp_pos`. -/
theorem oexp_pos (x : ON) : 0 < sz (oexp x) := lt_of_lt_of_le (pow_pos ω _) (oexp_eq x).ge

/-- Rocq: `SystemTCL.oexp_ge`. -/
theorem oexp_ge (x : ON) : sz x ≤ sz (oexp x) :=
  le_trans (CantorProduct.le_powOmega _) (oexp_eq x).ge

/-- `ω^c` is closed under the natural sum. Rocq: `SystemTCL.below_oexp`. -/
theorem below_oexp (c : ON) {x y : Ordinal.{0}} (hx : x < sz (oexp c)) (hy : y < sz (oexp c)) :
    x ♯ y < sz (oexp c) :=
  lt_of_lt_of_le
    (nadd_closed_con _ x y (ON_complete c) (lt_of_lt_of_le hx (oexp_eq c).le)
      (lt_of_lt_of_le hy (oexp_eq c).le))
    (oexp_eq c).ge

/-- Rocq: `SystemTCL.wm_mono`. -/
theorem wm_mono {w w' y y' : ON} (hw : sz w ≤ sz w') (hy : sz y ≤ sz y') :
    sz (wm w y) ≤ sz (wm w' y') :=
  le_trans (wm_eq w y).le (le_trans (nmul_monotone (pow_le_pow_right ω hw) hy) (wm_eq w' y').ge)

/-- Rocq: `SystemTCL.wm_increasing`. -/
theorem wm_increasing (w : ON) {y y' : ON} (hy : sz y < sz y') : sz (wm w y) < sz (wm w y') :=
  lt_of_le_of_lt (wm_eq w y).le
    (lt_of_lt_of_le (nmul_increasing2 hy (pow_pos ω _)) (wm_eq w y').ge)

/-- Rocq: `SystemTCL.wm_ge`. -/
theorem wm_ge (w y : ON) : sz y ≤ sz (wm w y) :=
  le_trans (nmul_one (sz y)).ge
    (le_trans (nmul_comm _ _).le
      (le_trans (nmul_monotone (succ_least (pow_pos ω (sz w))) (le_refl _)) (wm_eq w y).ge))

/-- Rocq: `SystemTCL.wm_pos`. -/
theorem wm_pos (w y : ON) (h : 0 < sz y) : 0 < sz (wm w y) := lt_of_lt_of_le h (wm_ge w y)

/-- Rocq: `SystemTCL.wm_ge_exp`. -/
theorem wm_ge_exp (w y : ON) (h : 0 < sz y) : sz (oexp w) ≤ sz (wm w y) :=
  le_trans (oexp_eq w).le
    (le_trans (nmul_one _).ge (le_trans (nmul_monotone (le_refl _) (succ_least h)) (wm_eq w y).ge))

/-- Rocq: `SystemTCL.wm_add`. -/
theorem wm_add (w y z : ON) : sz (wm w (y ⊕' z)) ≈ sz (wm w y) ♯ sz (wm w z) := omul_distr _ _ _

/-- Rocq: `SystemTCL.wm_wm`. -/
theorem wm_wm (a b y : ON) : sz (wm a (wm b y)) ≈ sz (wm (a ⊕' b) y) :=
  equiv_trans (equiv_symm (omul_assoc (oexp a) (oexp b) y))
    (equiv_trans (omul_eq _ _)
      (equiv_trans (nmul_congr (oexp_mul a b) (equiv_refl _)) (equiv_symm (omul_eq _ _))))

/-- Rocq: `SystemTCL.wm_oexp`. -/
theorem wm_oexp (a b : ON) : sz (wm a (oexp b)) ≈ sz (oexp (a ⊕' b)) := oexp_mul a b

/-- Rocq: `SystemTCL.wm_zero`. -/
theorem wm_zero (y : ON) : sz (wm ozero y) ≈ sz y :=
  equiv_trans (wm_eq ozero y)
    (equiv_trans (nmul_congr (pow_zero ω) (equiv_refl _))
      (equiv_trans (nmul_comm _ _) (nmul_one _)))

/-! ### Absorption

A finite natural sum of ordinals below `ω^E ⊗ y` is below `ω^L ⊗ y`, when
`E < L` and `y > 0`: `ω^L ⊗ y ≥ ω^E ⊗ (ω ⊗ y)`. -/

/-- Rocq: `SystemTCL.sumO`. -/
def sumO : List Ordinal.{0} → Ordinal.{0}
  | [] => 0
  | u :: us => u ♯ sumO us

/-- Rocq: `SystemTCL.orep`. -/
def orep : Nat → ON → ON
  | 0, _ => ozero
  | k + 1, y => orep k y ⊕' y

/-- Rocq: `SystemTCL.wm_orep`. -/
theorem wm_orep : ∀ (k : Nat) (w y : ON), sz (wm w (orep k y)) ≈ nrep k (sz (wm w y))
  | 0, w, _ => equiv_trans (wm_eq w ozero) (nmul_zero _)
  | k + 1, w, y => equiv_trans (wm_add w (orep k y) y) (nadd_congr (wm_orep k w y) (equiv_refl _))

/-- Rocq: `SystemTCL.orep_eq`. -/
theorem orep_eq : ∀ (k : Nat) (y : ON), sz (orep k y) ≈ nmul (ofNat k) (sz y)
  | 0, y => equiv_trans (equiv_symm (nmul_zero (sz y))) (nmul_comm _ _)
  | k + 1, y =>
    have e1 : sz (orep (k + 1) y) ≈ sz (y ⊗' onat k) ♯ sz (y ⊗' oone) :=
      equiv_trans (oadd_eq _ _)
        (nadd_congr
          (equiv_trans (orep_eq k y)
            (equiv_trans (nmul_comm _ _)
              (equiv_symm (equiv_trans (omul_eq _ _) (nmul_congr (equiv_refl _) (onat_eq k))))))
          (equiv_trans (equiv_symm (nmul_one _))
            (equiv_symm (equiv_trans (omul_eq _ _) (nmul_congr (equiv_refl _) oone_eq)))))
    equiv_trans e1
      (equiv_trans (equiv_symm (omul_distr y (onat k) oone))
        (equiv_trans (omul_eq _ _) (equiv_trans (nmul_congr (equiv_refl _) (onat_eq (k + 1)))
          (nmul_comm _ _))))

/-- Rocq: `SystemTCL.orep_below_omega`. -/
theorem orep_below_omega (k : Nat) (y : ON) (hy : 0 < sz y) : sz (orep k y) < sz (oomega ⊗' y) :=
  lt_of_le_of_lt (orep_eq k y).le
    (lt_of_lt_of_le (nmul_increasing1 (index_lt ω ⟨k⟩) hy)
      (equiv_symm (equiv_trans (omul_eq _ _) (nmul_congr oomega_eq (equiv_refl _)))).le)

theorem sumO_le_nrep (X : Ordinal.{0}) : ∀ us : List Ordinal.{0}, (∀ u, u ∈ us → u ≤ X) →
    sumO us ≤ nrep us.length X
  | [], _ => le_refl _
  | u :: us, h =>
    le_trans (nadd_comm _ _).le
      (nadd_le_nadd (sumO_le_nrep X us (fun v hv => h v (.tail _ hv))) (h u (.head _)))

/-- Rocq: `SystemTCL.absorb`. -/
theorem absorb (E L y : ON) (us : List Ordinal.{0}) (hy : 0 < sz y) (hEL : sz E < sz L)
    (hus : ∀ u, u ∈ us → u ≤ sz (wm E y)) : sumO us < sz (wm L y) :=
  lt_of_le_of_lt (sumO_le_nrep _ us hus)
    (lt_of_le_of_lt (wm_orep _ E y).ge
      (lt_of_lt_of_le (wm_increasing E (orep_below_omega _ y hy))
        (le_trans (wm_wm E oone y).le
          (wm_mono
            (le_trans (oadd_eq E oone).le
              (le_trans (nadd_congr (equiv_refl _) oone_eq).le
                (le_trans (nadd_succ2 _ _).le
                  (le_trans (succ_congruence (nadd_zero_r _)).le (succ_least hEL)))))
            (le_refl _)))))

/-- Rocq: `SystemTCL.oadd_lt_mono`. -/
theorem oadd_lt_mono {x x' y y' : ON} (hx : sz x' < sz x) (hy : sz y' ≤ sz y) :
    sz (x' ⊕' y') < sz (x ⊕' y) :=
  lt_of_le_of_lt (oadd_eq _ _).le
    (lt_of_lt_of_le ((nadd_increasing_both _ _ _ _).1 hx hy) (oadd_eq _ _).ge)

/-- Rocq: `SystemTCL.oadd_lt_mono2`. -/
theorem oadd_lt_mono2 {x x' y y' : ON} (hx : sz x' ≤ sz x) (hy : sz y' < sz y) :
    sz (x' ⊕' y') < sz (x ⊕' y) :=
  lt_of_le_of_lt (oadd_eq _ _).le
    (lt_of_lt_of_le ((nadd_increasing_both _ _ _ _).2 hx hy) (oadd_eq _ _).ge)

/-! ## Arithmetic on levels

Core's lemmas about subtraction use `propext`; these are the few the port
needs. -/

theorem succ_ne_zero' (n : Nat) : n + 1 ≠ 0 := fun h => Nat.noConfusion h

theorem sub_eq_zero_of_le' : ∀ {n i : Nat}, n ≤ i → n - i = 0
  | 0, i, _ => Nat.zero_sub i
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, i + 1, h => (Nat.succ_sub_succ n i).trans (sub_eq_zero_of_le' (Nat.le_of_succ_le_succ h))

theorem le_of_sub_eq_zero' : ∀ {n i : Nat}, n - i = 0 → n ≤ i
  | 0, _, _ => Nat.zero_le _
  | n + 1, 0, h => absurd h (succ_ne_zero' n)
  | n + 1, i + 1, h => Nat.succ_le_succ (le_of_sub_eq_zero' ((Nat.succ_sub_succ n i).symm.trans h))

theorem lt_of_sub_eq_succ {n i d : Nat} (h : n - i = d + 1) : i < n :=
  Nat.lt_of_not_le fun hle => succ_ne_zero' d (h.symm.trans (sub_eq_zero_of_le' hle))

theorem sub_succ_eq {n i d : Nat} (h : n - i = d + 1) : n - (i + 1) = d :=
  (Nat.sub_succ n i).trans (congrArg Nat.pred h)

theorem lt_or_le (a b : Nat) : a < b ∨ b ≤ a :=
  match Nat.lt_or_ge a b with
  | .inl h => .inl h
  | .inr h => .inr h

/-! ## Vectors and Howard's operation

A vector assigns an ordinal to each type level. Applying a function with
vector `f` to an argument of level `n` with vector `g` gives `box n f g`:
above `n` the vector of the function, and at level `i ≤ n` the value
`ω^(box n f g (i+1)) ⊗ (f i ⊕ g i)`. Each level exponentiates the one above
it, as cut elimination does. -/

/-- Rocq: `SystemTCL.vec`. -/
abbrev vec : Type := Nat → ON

/-- Rocq: `SystemTCL.boxd`. -/
def boxd (f g : vec) : Nat → Nat → ON
  | i, 0 => wm (f (i + 1)) (f i ⊕' g i)
  | i, d + 1 => wm (boxd f g (i + 1) d) (f i ⊕' g i)

/-- Rocq: `SystemTCL.box`. -/
def box (n : Nat) (f g : vec) : vec := fun i => if i ≤ n then boxd f g i (n - i) else f i

/-- Rocq: `SystemTCL.box_hi`. -/
theorem box_hi {n : Nat} (f g : vec) {i : Nat} (h : n < i) : box n f g i = f i :=
  ite_eq_right (Nat.not_le_of_gt h)

/-- Rocq: `SystemTCL.box_lo`. -/
theorem box_lo {n : Nat} (f g : vec) {i : Nat} (h : i ≤ n) :
    box n f g i = wm (box n f g (i + 1)) (f i ⊕' g i) := by
  show (if i ≤ n then boxd f g i (n - i) else f i) = _
  rw [ite_eq_left h]
  cases hd : n - i with
  | zero =>
    have hn : n = i := Nat.le_antisymm (le_of_sub_eq_zero' hd) h
    rw [box_hi f g (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.succ_le_succ (Nat.le_of_eq hn)))]
    rfl
  | succ d =>
    have hlt := lt_of_sub_eq_succ hd
    show wm (boxd f g (i + 1) d) _ = _
    show _ = wm (if i + 1 ≤ n then boxd f g (i + 1) (n - (i + 1)) else f (i + 1)) _
    rw [ite_eq_left (show i + 1 ≤ n from hlt), sub_succ_eq hd]

/-- Downward induction on levels. Rocq: `SystemTCL.down_ind`. -/
theorem down_ind (P : Nat → Prop) (m : Nat)
    (H : ∀ i, i ≤ m → (∀ j, i < j → j ≤ m → P j) → P i) : ∀ i, i ≤ m → P i := by
  have key : ∀ d i, i ≤ m → m ≤ i + d → P i := by
    intro d
    induction d with
    | zero =>
      intro i hi hmi
      exact H i hi (fun j hij hjm =>
        absurd (Nat.lt_of_lt_of_le hij (Nat.le_trans hjm hmi)) (Nat.lt_irrefl i))
    | succ d ih =>
      intro i hi hmi
      refine H i hi (fun j hij hjm => ih j hjm ?_)
      have : i + (d + 1) ≤ j + d := by
        rw [Nat.add_comm d 1, ← Nat.add_assoc]
        exact Nat.add_le_add_right hij d
      exact Nat.le_trans hmi this
  intro i hi
  exact key m i hi (Nat.le_add_left m i)

/-- Rocq: `SystemTCL.box_ge_f`. -/
theorem box_ge_f (n : Nat) (f g : vec) (i : Nat) : sz (f i) ≤ sz (box n f g i) :=
  match lt_or_le n i with
  | .inl h => by rw [box_hi f g h]
  | .inr h => by rw [box_lo f g h]; exact le_trans (oadd_le1 _ _) (wm_ge _ _)

/-- Rocq: `SystemTCL.box_ge_sum`. -/
theorem box_ge_sum {n : Nat} (f g : vec) {i : Nat} (h : i ≤ n) :
    sz (f i ⊕' g i) ≤ sz (box n f g i) := by
  rw [box_lo f g h]; exact wm_ge _ _

/-- Rocq: `SystemTCL.box_pos`. -/
theorem box_pos (n : Nat) (f g : vec) (hf : ∀ j, 0 < sz (f j)) (i : Nat) : 0 < sz (box n f g i) :=
  lt_of_lt_of_le (hf i) (box_ge_f n f g i)

/-- Rocq: `SystemTCL.box_mono`. -/
theorem box_mono {m n : Nat} {f f' g g' : vec} (hnm : n < m)
    (hf : ∀ j, j ≤ m → sz (f' j) ≤ sz (f j)) (hg : ∀ j, j ≤ n → sz (g' j) ≤ sz (g j)) :
    ∀ i, i ≤ m → sz (box n f' g' i) ≤ sz (box n f g i) := by
  refine down_ind _ m (fun i hi ih => ?_)
  match lt_or_le n i with
  | .inl h => rw [box_hi f' g' h, box_hi f g h]; exact hf i hi
  | .inr h =>
    rw [box_lo f' g' h, box_lo f g h]
    exact wm_mono (ih (i + 1) (Nat.lt_succ_self i) (Nat.lt_of_le_of_lt h hnm))
      (oadd_mono (hf i hi) (hg i h))

/-- Rocq: `SystemTCL.box_mono_all`. -/
theorem box_mono_all (n : Nat) {f f' g g' : vec} (hf : ∀ j, sz (f' j) ≤ sz (f j))
    (hg : ∀ j, sz (g' j) ≤ sz (g j)) (i : Nat) : sz (box n f' g' i) ≤ sz (box n f g i) :=
  box_mono (m := n + 1 + i) (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_add_right _ _))
    (fun j _ => hf j) (fun j _ => hg j) i (Nat.le_add_left _ _)

/-- Rocq: `SystemTCL.box_lt0`. -/
theorem box_lt0 {m n : Nat} {f f' g g' : vec} (hnm : n < m)
    (hf : ∀ j, j ≤ m → sz (f' j) ≤ sz (f j)) (hg : ∀ j, j ≤ n → sz (g' j) ≤ sz (g j))
    (h0 : sz (f' 0) < sz (f 0) ∨ sz (g' 0) < sz (g 0)) :
    sz (box n f' g' 0) < sz (box n f g 0) := by
  rw [box_lo f' g' (Nat.zero_le n), box_lo f g (Nat.zero_le n)]
  refine lt_of_le_of_lt (wm_mono (box_mono hnm hf hg 1 (Nat.lt_of_le_of_lt (Nat.zero_le n) hnm))
    (le_refl _)) (wm_increasing _ ?_)
  match h0 with
  | .inl h => exact oadd_lt_mono h (hg 0 (Nat.zero_le n))
  | .inr h => exact oadd_lt_mono2 (hf 0 (Nat.zero_le m)) h

/-- Rocq: `SystemTCL.box_ext`. -/
theorem box_ext (n : Nat) {f f' g g' : vec} (i0 : Nat)
    (hf : ∀ j, i0 ≤ j → j ≤ n + 1 → f j = f' j) (hg : ∀ j, i0 ≤ j → j ≤ n → g j = g' j) :
    ∀ i, i0 ≤ i → i ≤ n + 1 → box n f g i = box n f' g' i := by
  intro i hi0 hi
  revert hi0
  refine down_ind (fun i => i0 ≤ i → box n f g i = box n f' g' i) (n + 1) (fun k hk ih hk0 => ?_) i hi
  match lt_or_le n k with
  | .inl h => rw [box_hi f g h, box_hi f' g' h]; exact hf k hk0 hk
  | .inr h =>
    rw [box_lo f g h, box_lo f' g' h, ih (k + 1) (Nat.lt_succ_self k) (Nat.succ_le_succ h)
      (Nat.le_succ_of_le hk0), hf k hk0 hk, hg k hk0 h]

/-- Rocq: `SystemTCL.sumO3`. -/
theorem sumO3 (a b c : Ordinal.{0}) : sumO [a, b, c] ≈ a ♯ (b ♯ c) :=
  nadd_congr (equiv_refl a) (nadd_congr (equiv_refl b) (nadd_zero_r c))

/-- Rocq: `SystemTCL.le_sumO3`. -/
theorem le_sumO3 (a b c : Ordinal.{0}) : a ≤ sumO [a, b, c] := nadd_le1 _ _

/-- Regrouping sums. Rocq: `SystemTCL.split_head`. -/
theorem split_head (u a b : Ordinal.{0}) (us : List Ordinal.{0}) (h : u ≤ a ♯ b) :
    sumO (u :: us) ≤ sumO (a :: b :: us) :=
  le_trans (nadd_le_nadd h (le_refl _)) (nadd_assoc a b (sumO us)).ge

/-- Rocq: `SystemTCL.le_sumO4`. -/
theorem le_sumO4 (a b c d : Ordinal.{0}) : a ♯ (b ♯ (c ♯ d)) ≤ sumO [a, b, c, d] :=
  nadd_le_nadd (le_refl a) (nadd_le_nadd (le_refl b) (nadd_le_nadd (le_refl c) (nadd_zero_r d).ge))

/-- Rocq: `SystemTCL.split_sum3`. -/
theorem split_sum3 (u a b c : Ordinal.{0}) (h : u ≤ (a ♯ b) ♯ c) : u ≤ sumO [a, b, c] :=
  le_trans h (le_trans (nadd_assoc a b c).ge (sumO3 a b c).ge)

/-- Every element of a list is at most `X`. -/
def AllLe (X : Ordinal.{0}) : List Ordinal.{0} → Prop
  | [] => True
  | u :: us => u ≤ X ∧ AllLe X us

theorem AllLe.mem {X : Ordinal.{0}} : ∀ {us : List Ordinal.{0}}, AllLe X us → ∀ u, u ∈ us → u ≤ X
  | _ :: _, h, _, .head _ => h.1
  | _ :: _, h, _, .tail _ hu => AllLe.mem h.2 _ hu

/-! ## The key inequalities

The combinator `S`: `S a b d` at levels `p, q, r` (the levels of the types of
`a`, `b`, `d`) has a larger vector than `a d (b d)`, whose middle application
is at level `s`, at every level up to `t`. This is Howard's lemma: above `r`
the vector of `S a b` dominates that of `a b` with room to spare, and below
`r` the duplicated `d` is paid for by one extra power of ω at each level. -/

/-- Rocq: `SystemTCL.S_decrease`. -/
theorem S_decrease (p q r s t : Nat) (Sv A B D : vec) (hS : ∀ j, 0 < sz (Sv j))
    (_hA : ∀ j, 0 < sz (A j)) (_hB : ∀ j, 0 < sz (B j)) (_hD : ∀ j, 0 < sz (D j))
    (h1 : r < p) (h2 : r < q) (h3 : s ≤ q) (h4 : s < p) (h5 : t ≤ p) :
    ∀ i, i ≤ t →
      sz (box s (box r A D) (box r B D) i) < sz (box r (box q (box p Sv A) B) D i) := by
  have hSa : ∀ j, 0 < sz (box p Sv A j) := box_pos p Sv A hS
  have hc : ∀ j, 0 < sz (box q (box p Sv A) B j) := box_pos q _ B hSa
  have HRb : ∀ i, r < i → box s (box r A D) (box r B D) i = box s A B i := by
    intro i hi
    match lt_or_le (s + 1) i with
    | .inl hgt =>
      have hsi : s < i := Nat.lt_trans (Nat.lt_succ_self s) hgt
      rw [box_hi _ _ hsi, box_hi _ _ hsi, box_hi _ _ hi]
    | .inr hle =>
      exact box_ext s (r + 1) (fun j hj _ => box_hi A D hj) (fun j hj _ => box_hi B D hj) i hi hle
  -- Above `r`: `S a b` against `a b`.
  have Hup : ∀ i, i ≤ p → r + 1 ≤ i →
      (i ≤ q → sumO [sz (box s A B i), sz (A i), sz (B i)] < sz (box q (box p Sv A) B i)) ∧
        sz (box s A B i) < sz (box q (box p Sv A) B i) := by
    refine down_ind _ p (fun i hip ih hri => ?_)
    match lt_or_le q i with
    | .inl hqi =>
      refine ⟨fun h => absurd (Nat.lt_of_lt_of_le hqi h) (Nat.lt_irrefl q), ?_⟩
      rw [box_hi _ _ hqi, box_hi _ _ (Nat.lt_of_le_of_lt h3 hqi)]
      exact lt_of_lt_of_le (oadd_lt2 _ _ (hS i)) (box_ge_sum Sv A hip)
    | .inr hiq =>
      have HSai : sz (Sv i ⊕' A i) ≤ sz (box p Sv A i) := box_ge_sum Sv A hip
      have HAS : sz (A i) < sz (box p Sv A i) := lt_of_lt_of_le (oadd_lt2 _ _ (hS i)) HSai
      have HAy : sz (A i) < sz (box p Sv A i ⊕' B i) := lt_of_lt_of_le HAS (oadd_le1 _ _)
      have HBy : sz (B i) ≤ sz (box p Sv A i ⊕' B i) := oadd_le2 _ _
      have Hy : 0 < sz (box p Sv A i ⊕' B i) := oadd_pos1 _ _ (hSa i)
      have Hfirst : sumO [sz (box s A B i), sz (A i), sz (B i)] < sz (box q (box p Sv A) B i) := by
        rw [box_lo _ _ hiq]
        match lt_or_le s i with
        | .inr his =>
          have IH1 := (ih (i + 1) (Nat.lt_succ_self i) (Nat.lt_of_le_of_lt his h4)
            (Nat.le_succ_of_le hri)).2
          refine absorb _ _ _ _ Hy IH1 (AllLe.mem ⟨?_, le_trans (le_of_lt HAy) (wm_ge _ _),
            le_trans HBy (wm_ge _ _), trivial⟩)
          rw [box_lo A B his]
          exact wm_mono (le_refl _) (oadd_mono (le_of_lt HAS) (le_refl _))
        | .inl hsi =>
          rw [box_hi A B hsi]
          refine absorb ozero _ _ _ Hy (hc (i + 1)) (AllLe.mem ⟨?_, ?_, ?_, trivial⟩)
          · exact le_trans (le_of_lt HAy) (wm_zero _).ge
          · exact le_trans (le_of_lt HAy) (wm_zero _).ge
          · exact le_trans HBy (wm_zero _).ge
      exact ⟨fun _ => Hfirst, lt_of_le_of_lt (le_sumO3 _ _ _) Hfirst⟩
  -- Below `r`: the duplicated argument.
  have Hlow : ∀ i, i ≤ r + 1 →
      sumO [sz (box s (box r A D) (box r B D) i), sz (box r A D i), sz (box r B D i)] <
        sz (box r (box q (box p Sv A) B) D i) := by
    refine down_ind _ (r + 1) (fun i hi ih => ?_)
    match Nat.eq_or_lt_of_le hi with
    | .inl hir =>
      subst hir
      rw [HRb (r + 1) (Nat.lt_succ_self r), box_hi A D (Nat.lt_succ_self r),
        box_hi B D (Nat.lt_succ_self r), box_hi _ D (Nat.lt_succ_self r)]
      exact (Hup (r + 1) h1 (Nat.le_refl _)).1 h2
    | .inr hir =>
      have hir : i ≤ r := Nat.le_of_lt_succ hir
      let E := box s (box r A D) (box r B D) (i + 1) ⊕' (box r A D (i + 1) ⊕' box r B D (i + 1))
      have HE : sz E < sz (box r (box q (box p Sv A) B) D (i + 1)) :=
        lt_of_le_of_lt
          (le_trans (oadd_eq _ _).le (le_trans (nadd_le_nadd (le_refl _) (oadd_eq _ _).le)
            (sumO3 _ _ _).ge))
          (ih (i + 1) (Nat.lt_succ_self i) (Nat.succ_le_succ hir))
      have hiq : i ≤ q := Nat.le_of_lt (Nat.lt_of_le_of_lt hir h2)
      have hip : i ≤ p := Nat.le_of_lt (Nat.lt_of_le_of_lt hir h1)
      have HAc : sz (A i) ≤ sz (box q (box p Sv A) B i) :=
        le_trans (oadd_le2 _ _) (le_trans (box_ge_sum Sv A hip)
          (le_trans (oadd_le1 _ _) (box_ge_sum _ B hiq)))
      have HBc : sz (B i) ≤ sz (box q (box p Sv A) B i) :=
        le_trans (oadd_le2 _ _) (box_ge_sum _ B hiq)
      have Hy : 0 < sz (box q (box p Sv A) B i ⊕' D i) := oadd_pos1 _ _ (hc i)
      have HX : sz (box r A D i) ≤ sz (wm E (box q (box p Sv A) B i ⊕' D i)) := by
        rw [box_lo A D hir]
        exact wm_mono (le_trans (oadd_le1 _ _) (oadd_le2 _ _)) (oadd_mono HAc (le_refl _))
      have HY : sz (box r B D i) ≤ sz (wm E (box q (box p Sv A) B i ⊕' D i)) := by
        rw [box_lo B D hir]
        exact wm_mono (le_trans (oadd_le2 _ _) (oadd_le2 _ _)) (oadd_mono HBc (le_refl _))
      rw [box_lo (box q (box p Sv A) B) D hir]
      match lt_or_le s i with
      | .inr his =>
        rw [box_lo (box r A D) (box r B D) his]
        refine lt_of_le_of_lt (split_head _ _ _ _ (wm_add _ _ _).le) ?_
        refine absorb E _ _ [_, _, _, _] Hy HE (AllLe.mem ⟨?_, ?_, HX, HY, trivial⟩)
        · rw [box_lo A D hir]
          exact le_trans (wm_wm _ _ _).le
            (wm_mono (oadd_mono (le_refl _) (oadd_le1 _ _)) (oadd_mono HAc (le_refl _)))
        · rw [box_lo B D hir]
          exact le_trans (wm_wm _ _ _).le
            (wm_mono (oadd_mono (le_refl _) (oadd_le2 _ _)) (oadd_mono HBc (le_refl _)))
      | .inl hsi =>
        rw [box_hi (box r A D) (box r B D) hsi]
        exact absorb E _ _ [_, _, _] Hy HE (AllLe.mem ⟨HX, HX, HY, trivial⟩)
  intro i hi
  match lt_or_le r i with
  | .inl hri =>
    rw [HRb i hri, box_hi _ D hri]
    exact (Hup i (Nat.le_trans hi h5) hri).2
  | .inr hir => exact lt_of_le_of_lt (le_sumO3 _ _ _) (Hlow i (Nat.le_succ_of_le hir))

/-! The recursor. `R n̄` at a type of level `k` has the vector `vspec k n`:
`n+1` at level `k+2`, the level of the recursor, and `1` elsewhere; the
unapplied recursor has `ω` there instead (`gen`). -/

/-- Rocq: `SystemTCL.vspec`. -/
def vspec (k n : Nat) : vec := fun j => if j = k + 2 then onat (n + 1) else oone
/-- Rocq: `SystemTCL.gen`. -/
def gen (k : Nat) : vec := fun j => if j = k + 2 then oomega else oone

/-- Rocq: `SystemTCL.oone_pos`. -/
theorem oone_pos : 0 < sz oone := lt_of_lt_of_le (succ_lt 0) oone_eq.ge

/-- Rocq: `SystemTCL.onat_pos`. -/
theorem onat_pos (n : Nat) : 0 < sz (onat (n + 1)) :=
  lt_of_lt_of_le (ofNat_increasing (Nat.zero_lt_succ n)) (onat_eq (n + 1)).ge

/-- Rocq: `SystemTCL.vspec_pos`. -/
theorem vspec_pos (k n j : Nat) : 0 < sz (vspec k n j) := by
  show 0 < sz (if j = k + 2 then onat (n + 1) else oone)
  by_cases h : j = k + 2
  · rw [ite_eq_left h]; exact onat_pos n
  · rw [ite_eq_right h]; exact oone_pos

/-- Rocq: `SystemTCL.gen_pos`. -/
theorem gen_pos (k j : Nat) : 0 < sz (gen k j) := by
  show 0 < sz (if j = k + 2 then oomega else oone)
  by_cases h : j = k + 2
  · rw [ite_eq_left h]; exact lt_of_lt_of_le omega_gt0 oomega_eq.ge
  · rw [ite_eq_right h]; exact oone_pos

/-- Rocq: `SystemTCL.sumO4`. -/
theorem sumO4 (a b c d : Ordinal.{0}) : sumO [a, b, c, d] ≈ a ♯ (b ♯ (c ♯ d)) :=
  nadd_congr (equiv_refl a) (nadd_congr (equiv_refl b) (nadd_congr (equiv_refl c) (nadd_zero_r d)))

theorem oadd3_le (a b c d : ON) : sz (a ⊕' (b ⊕' (c ⊕' d))) ≤ sumO [sz a, sz b, sz c, sz d] :=
  le_trans (oadd_eq _ _).le (le_trans (nadd_le_nadd (le_refl _)
    (le_trans (oadd_eq _ _).le (nadd_le_nadd (le_refl _) (oadd_eq _ _).le))) (le_sumO4 _ _ _ _))

/-- The recursion step `R (n+1) a b ↦ b n (R n a b)`, at a type of level `k`:
the vector of the redex is larger at every level up to `k`. The extra power
of ω at level `k+1`, from `n+2` against `n+1`, pays for the extra application
of `b`. Rocq: `SystemTCL.R_decrease`. -/
theorem R_decrease (k n : Nat) (A B Nv : vec) (_hA : ∀ j, 0 < sz (A j)) (_hB : ∀ j, 0 < sz (B j))
    (hN : sz (Nv 0) < sz (oexp (onat (n + 1)))) :
    ∀ i, i ≤ k →
      sz (box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) i) <
        sz (box (k + 1) (box k (vspec k (n + 1)) A) B i) := by
  have hne : ∀ j, j ≤ k + 1 → ¬ j = k + 2 := fun j hj e =>
    Nat.lt_irrefl (k + 2) (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm) (Nat.lt_succ_of_le hj))
  have HPP : ∀ j, j ≤ k + 1 → box k (vspec k n) A j = box k (vspec k (n + 1)) A j := fun j hj =>
    box_ext k 0 (fun j' _ hj' => (ite_eq_right (hne j' hj')).trans (ite_eq_right (hne j' hj')).symm)
      (fun _ _ _ => rfl) j (Nat.zero_le j) hj
  have HP : ∀ j, 0 < sz (box k (vspec k n) A j) := box_pos k _ A (vspec_pos k n)
  have hk1 : k < k + 1 := Nat.lt_succ_self k
  have hk2 : k < k + 2 := Nat.lt_trans hk1 (Nat.lt_succ_self _)
  have HW1 : box (k + 1) (box k (vspec k n) A) B (k + 1) = wm (onat (n + 1)) (oone ⊕' B (k + 1)) := by
    rw [box_lo _ B (Nat.le_refl _), box_hi _ B (Nat.lt_succ_self _), box_hi _ A hk2, box_hi _ A hk1]
    show wm (if k + 2 = k + 2 then onat (n + 1) else oone)
      ((if k + 1 = k + 2 then onat (n + 1) else oone) ⊕' B (k + 1)) = _
    rw [ite_eq_left rfl, ite_eq_right (hne (k + 1) (Nat.le_refl _))]
  have HL1 : box (k + 1) (box k (vspec k (n + 1)) A) B (k + 1) =
      wm (onat (n + 2)) (oone ⊕' B (k + 1)) := by
    rw [box_lo _ B (Nat.le_refl _), box_hi _ B (Nat.lt_succ_self _), box_hi _ A hk2, box_hi _ A hk1]
    show wm (if k + 2 = k + 2 then onat (n + 1 + 1) else oone)
      ((if k + 1 = k + 2 then onat (n + 1 + 1) else oone) ⊕' B (k + 1)) = _
    rw [ite_eq_left rfl, ite_eq_right (hne (k + 1) (Nat.le_refl _))]
  have Hup : ∀ i, i ≤ k + 1 → 1 ≤ i →
      sumO [sz (box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) i),
            sz (box (k + 1) (box k (vspec k n) A) B i), sz (B i), sz (onat (n + 1))] <
        sz (box (k + 1) (box k (vspec k (n + 1)) A) B i) := by
    refine down_ind _ (k + 1) (fun i hi ih h1i => ?_)
    match Nat.eq_or_lt_of_le hi with
    | .inl hik =>
      subst hik
      rw [box_hi (box 0 B Nv) _ hk1, box_hi B Nv (Nat.zero_lt_succ k), HW1, HL1]
      have Hy : 0 < sz (oone ⊕' B (k + 1)) := oadd_pos1 _ _ oone_pos
      refine absorb (onat (n + 1)) _ _ [_, _, _, _] Hy ?_
        (AllLe.mem ⟨le_trans (oadd_le2 _ _) (wm_ge _ _), le_refl _,
          le_trans (oadd_le2 _ _) (wm_ge _ _), le_trans (oexp_ge _) (wm_ge_exp _ _ Hy), trivial⟩)
      exact lt_of_le_of_lt (onat_eq _).le
        (lt_of_lt_of_le (ofNat_increasing (Nat.lt_succ_self (n + 1))) (onat_eq _).ge)
    | .inr hik =>
      have hik : i ≤ k := Nat.le_of_lt_succ hik
      have Hy : 0 < sz (box k (vspec k n) A i ⊕' B i) := oadd_pos1 _ _ (HP i)
      let E := box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) (i + 1) ⊕'
        (box (k + 1) (box k (vspec k n) A) B (i + 1) ⊕' (B (i + 1) ⊕' onat (n + 1)))
      have HE : sz E < sz (box (k + 1) (box k (vspec k (n + 1)) A) B (i + 1)) :=
        lt_of_le_of_lt (oadd3_le _ _ _ _)
          (ih (i + 1) (Nat.lt_succ_self i) (Nat.succ_le_succ hik) (Nat.le_succ_of_le h1i))
      have HWi : box (k + 1) (box k (vspec k n) A) B i =
          wm (box (k + 1) (box k (vspec k n) A) B (i + 1)) (box k (vspec k n) A i ⊕' B i) :=
        box_lo _ B hi
      rw [box_lo (box k (vspec k (n + 1)) A) B hi, ← HPP i hi]
      refine lt_of_le_of_lt (split_head _
        (sz (wm (box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) (i + 1)) (B i)))
        (sz (wm (box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) (i + 1))
          (box (k + 1) (box k (vspec k n) A) B i))) _ ?_) ?_
      · rw [box_lo (box 0 B Nv) _ hik, box_hi B Nv (Nat.lt_of_lt_of_le Nat.zero_lt_one h1i)]
        exact (wm_add _ _ _).le
      refine absorb E _ _ [_, _, _, _, _] Hy HE (AllLe.mem ⟨?_, ?_, ?_, ?_, ?_, trivial⟩)
      · exact wm_mono (oadd_le1 _ _) (oadd_le2 _ _)
      · rw [HWi]
        exact le_trans (wm_wm _ _ _).le (wm_mono (oadd_mono (le_refl _) (oadd_le1 _ _)) (le_refl _))
      · rw [HWi]
        exact wm_mono (le_trans (oadd_le1 _ _) (oadd_le2 _ _)) (le_refl _)
      · exact le_trans (oadd_le2 _ _) (wm_ge _ _)
      · exact le_trans (le_trans (le_trans (oadd_le2 _ _) (le_trans (oadd_le2 _ _) (oadd_le2 _ _)))
          (oexp_ge E)) (wm_ge_exp _ _ Hy)
  intro i hi
  match i with
  | 0 =>
    have HB0 : box 0 B Nv 0 = wm (B 1) (B 0 ⊕' Nv 0) := by
      rw [box_lo B Nv (Nat.le_refl 0), box_hi B Nv Nat.zero_lt_one]
    have HW0 : box (k + 1) (box k (vspec k n) A) B 0 =
        wm (box (k + 1) (box k (vspec k n) A) B 1) (box k (vspec k n) A 0 ⊕' B 0) :=
      box_lo _ B (Nat.zero_le _)
    have HR0 : box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) 0 =
        wm (box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) 1)
          (box 0 B Nv 0 ⊕' box (k + 1) (box k (vspec k n) A) B 0) :=
      box_lo _ _ (Nat.zero_le _)
    have Hy : 0 < sz (box k (vspec k n) A 0 ⊕' B 0) := oadd_pos1 _ _ (HP 0)
    let Rh1 := box k (box 0 B Nv) (box (k + 1) (box k (vspec k n) A) B) 1
    let E := Rh1 ⊕' (box (k + 1) (box k (vspec k n) A) B 1 ⊕' (B 1 ⊕' onat (n + 1)))
    have HE : sz E < sz (box (k + 1) (box k (vspec k (n + 1)) A) B 1) :=
      lt_of_le_of_lt (oadd3_le _ _ _ _) (Hup 1 (Nat.succ_le_succ (Nat.zero_le k)) (Nat.le_refl 1))
    rw [box_lo (box k (vspec k (n + 1)) A) B (Nat.zero_le _), ← HPP 0 (Nat.zero_le _)]
    refine lt_of_le_of_lt (split_sum3 _ (sz (wm (Rh1 ⊕' B 1) (B 0))) (sz (wm (Rh1 ⊕' B 1) (Nv 0)))
      (sz (wm Rh1 (box (k + 1) (box k (vspec k n) A) B 0))) ?_) ?_
    · rw [HR0]
      refine le_trans (wm_add _ _ _).le (nadd_le_nadd ?_ (le_refl _))
      rw [HB0]
      exact le_trans (wm_wm _ _ _).le (wm_add _ _ _).le
    refine absorb E _ _ [_, _, _] Hy HE (AllLe.mem ⟨?_, ?_, ?_, trivial⟩)
    · exact wm_mono (oadd_mono (le_refl _) (le_trans (oadd_le1 _ _) (oadd_le2 _ _))) (oadd_le2 _ _)
    · refine le_trans (wm_mono (le_refl _) (le_of_lt hN)) (le_trans (wm_oexp _ _).le ?_)
      refine le_trans (oexp_mono ?_) (wm_ge_exp _ _ Hy)
      exact le_trans (oadd_eq _ _).le (le_trans (nadd_le_nadd (oadd_eq _ _).le (le_refl _))
        (le_trans (nadd_assoc _ _ _).ge (le_trans (nadd_le_nadd (le_refl _)
          (le_trans (oadd_eq _ _).ge (oadd_le2 _ _))) (oadd_eq _ _).ge)))
    · rw [HW0]
      exact le_trans (wm_wm _ _ _).le (wm_mono (oadd_mono (le_refl _) (oadd_le1 _ _)) (le_refl _))
  | i + 1 =>
    exact lt_of_le_of_lt (nadd_le1 _ _)
      (Hup (i + 1) (Nat.le_succ_of_le hi) (Nat.succ_le_succ (Nat.zero_le i)))

/-! ## Combinatory System T

Base type `N`, function types and product types. `lev (A × B)` is the larger
of the two levels. -/

/-- Rocq: `SystemTCL.ty`. -/
inductive Ty : Type where
  | TN : Ty
  | TAr : Ty → Ty → Ty
  | TPr : Ty → Ty → Ty
  deriving DecidableEq

open Ty

/-- Rocq: `SystemTCL.lev`. -/
def lev : Ty → Nat
  | TN => 0
  | TAr A B => Nat.max (lev A + 1) (lev B)
  | TPr A B => Nat.max (lev A) (lev B)

/-- Terms; applications are annotated with the type of the argument.
Rocq: `SystemTCL.term`. -/
inductive Term : Type where
  | var : Nat → Term
  /-- `K_{A,B} : A → B → A` -/
  | Kc : Ty → Ty → Term
  /-- `S_{A,B,C} : (A → B → C) → (A → B) → A → C` -/
  | Sc : Ty → Ty → Ty → Term
  | Zc : Term
  | Suc : Term
  /-- `R_C : N → C → (N → C → C) → C` -/
  | Rc : Ty → Term
  /-- `P_{A,B} : A → B → A × B` -/
  | Pc : Ty → Ty → Term
  /-- `π₁ : A × B → A` -/
  | P1c : Ty → Ty → Term
  /-- `π₂ : A × B → B` -/
  | P2c : Ty → Ty → Term
  | app : Ty → Term → Term → Term

open Term

/-- Rocq: `SystemTCL.typing`. -/
inductive Typing (Γ : List Ty) : Term → Ty → Prop where
  | var (x : Nat) (A : Ty) : List.nthError Γ x = some A → Typing Γ (var x) A
  | K (A B : Ty) : Typing Γ (Kc A B) (TAr A (TAr B A))
  | S (A B C : Ty) : Typing Γ (Sc A B C) (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
  | Z : Typing Γ Zc TN
  | Suc : Typing Γ Suc (TAr TN TN)
  | R (C : Ty) : Typing Γ (Rc C) (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
  | P (A B : Ty) : Typing Γ (Pc A B) (TAr A (TAr B (TPr A B)))
  | P1 (A B : Ty) : Typing Γ (P1c A B) (TAr (TPr A B) A)
  | P2 (A B : Ty) : Typing Γ (P2c A B) (TAr (TPr A B) B)
  | app (A B : Ty) (M N : Term) : Typing Γ M (TAr A B) → Typing Γ N A → Typing Γ (app A M N) B

/-- Rocq: `SystemTCL.num`. -/
def num : Nat → Term
  | 0 => Zc
  | n + 1 => app TN Suc (num n)

/-- The numeral, if any, given a function term applied at type `ty` and the
numeral of the argument; every case is spelled out, since a wildcard would
make the definition depend on `propext`. -/
def isNumApp : Ty → Term → Option Nat → Option Nat
  | TN, Suc, o => o.map Nat.succ
  | TN, var _, _ => none
  | TN, Kc _ _, _ => none
  | TN, Sc _ _ _, _ => none
  | TN, Zc, _ => none
  | TN, Rc _, _ => none
  | TN, Pc _ _, _ => none
  | TN, P1c _ _, _ => none
  | TN, P2c _ _, _ => none
  | TN, app _ _ _, _ => none
  | TAr _ _, _, _ => none
  | TPr _ _, _, _ => none

/-- Rocq: `SystemTCL.is_num`. -/
def isNum : Term → Option Nat
  | Zc => some 0
  | app A M t => isNumApp A M (isNum t)
  | var _ => none
  | Kc _ _ => none
  | Sc _ _ _ => none
  | Suc => none
  | Rc _ => none
  | Pc _ _ => none
  | P1c _ _ => none
  | P2c _ _ => none

/-- Rocq: `SystemTCL.is_num_num`. -/
theorem isNum_num : ∀ n, isNum (num n) = some n
  | 0 => rfl
  | n + 1 => by
    show (isNum (num n)).map Nat.succ = some (n + 1)
    rw [isNum_num n]; rfl

theorem isNumApp_spec : ∀ (A : Ty) (M : Term) (o : Option Nat) (n : Nat),
    isNumApp A M o = some n → A = TN ∧ M = Suc ∧ ∃ k, o = some k ∧ n = k + 1
  | TN, Suc, some k, _, h => ⟨rfl, rfl, k, rfl, (Option.some.inj h).symm⟩
  | TN, Suc, none, _, h => nomatch h
  | TN, var _, _, _, h => nomatch h
  | TN, Kc _ _, _, _, h => nomatch h
  | TN, Sc _ _ _, _, _, h => nomatch h
  | TN, Zc, _, _, h => nomatch h
  | TN, Rc _, _, _, h => nomatch h
  | TN, Pc _ _, _, _, h => nomatch h
  | TN, P1c _ _, _, _, h => nomatch h
  | TN, P2c _ _, _, _, h => nomatch h
  | TN, app _ _ _, _, _, h => nomatch h
  | TAr _ _, _, _, _, h => nomatch h
  | TPr _ _, _, _, _, h => nomatch h

/-- Rocq: `SystemTCL.is_num_spec`. -/
theorem isNum_spec : ∀ (t : Term) (n : Nat), isNum t = some n → t = num n
  | Zc, n, h => by cases h; rfl
  | app A M t, n, h => by
    obtain ⟨rfl, rfl, k, hk, rfl⟩ := isNumApp_spec A M (isNum t) n h
    rw [isNum_spec t k hk]; rfl
  | var _, _, h => nomatch h
  | Kc _ _, _, h => nomatch h
  | Sc _ _ _, _, h => nomatch h
  | Suc, _, h => nomatch h
  | Rc _, _, h => nomatch h
  | Pc _ _, _, h => nomatch h
  | P1c _ _, _, h => nomatch h
  | P2c _ _, _, h => nomatch h

/-- Reduction. The recursor reduces when its first argument is a numeral, as
in Howard (1970); every closed term of type `N` still reduces to a numeral
(`T_value`). Rocq: `SystemTCL.step`. -/
inductive Step : Term → Term → Prop where
  | K (A B X Y : Ty) (a b : Term) : Step (app Y (app X (Kc A B) a) b) a
  | S (A B C X Y W : Ty) (a b c : Term) :
      Step (app W (app Y (app X (Sc A B C) a) b) c) (app B (app A a c) (app A b c))
  | R0 (C X Y W : Ty) (t a b : Term) : isNum t = some 0 → Step (app W (app Y (app X (Rc C) t) a) b) a
  | RS (C X Y W : Ty) (t : Term) (n : Nat) (a b : Term) : isNum t = some (n + 1) →
      Step (app W (app Y (app X (Rc C) t) a) b)
        (app C (app TN b (num n)) (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) a) b))
  | P1 (A B C D X Y Z : Ty) (a b : Term) : Step (app X (P1c A B) (app Y (app Z (Pc C D) a) b)) a
  | P2 (A B C D X Y Z : Ty) (a b : Term) : Step (app X (P2c A B) (app Y (app Z (Pc C D) a) b)) b
  | l (A : Ty) (M M' N : Term) : Step M M' → Step (app A M N) (app A M' N)
  | r (A : Ty) (M N N' : Term) : Step N N' → Step (app A M N) (app A M N')

/-- Rocq: `SystemTCL.num_normal`. -/
theorem num_normal : ∀ (n : Nat) (M : Term), Step (num n) M → False
  | 0, _, h => nomatch h
  | n + 1, _, h => by
    cases h with
    | l _ _ _ _ h => nomatch h
    | r _ _ _ _ h => exact num_normal n _ h

/-! ## Typing facts -/

/-- Rocq: `SystemTCL.typing_app`. -/
theorem typing_app {Γ : List Ty} {A : Ty} {M N : Term} {T : Ty} (h : Typing Γ (app A M N) T) :
    Typing Γ M (TAr A T) ∧ Typing Γ N A := by
  cases h with
  | app _ _ _ _ h1 h2 => exact ⟨h1, h2⟩

/-- Rocq: `SystemTCL.typing_unique`. -/
theorem typing_unique {Γ : List Ty} {M : Term} {A : Ty} (h : Typing Γ M A) :
    ∀ {B : Ty}, Typing Γ M B → A = B := by
  induction h with
  | var x A hx => intro B hB; cases hB with | var _ _ hx' => exact Option.some.inj (hx.symm.trans hx')
  | K => intro B hB; cases hB; rfl
  | S => intro B hB; cases hB; rfl
  | Z => intro B hB; cases hB; rfl
  | Suc => intro B hB; cases hB; rfl
  | R => intro B hB; cases hB; rfl
  | P => intro B hB; cases hB; rfl
  | P1 => intro B hB; cases hB; rfl
  | P2 => intro B hB; cases hB; rfl
  | app A B M N _ _ ihM _ =>
    intro B' hB
    cases hB with
    | app _ _ _ _ h1 _ => cases ihM h1; rfl

/-- Rocq: `SystemTCL.typing_num`. -/
theorem typing_num (Γ : List Ty) : ∀ n, Typing Γ (num n) TN
  | 0 => .Z
  | n + 1 => .app _ _ _ _ .Suc (typing_num Γ n)

/-- Rocq: `SystemTCL.subject_reduction`. -/
theorem subject_reduction {Γ : List Ty} {M M' : Term} (h : Step M M') :
    ∀ {A : Ty}, Typing Γ M A → Typing Γ M' A := by
  induction h with
  | K A B X Y a b =>
    intro T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, h2⟩ := typing_app h1
    cases h1; exact h2
  | S A B C X Y W a b c =>
    intro T hT
    obtain ⟨h1, hc⟩ := typing_app hT
    obtain ⟨h1, hb⟩ := typing_app h1
    obtain ⟨h1, ha⟩ := typing_app h1
    cases h1
    exact .app _ _ _ _ (.app _ _ _ _ ha hc) (.app _ _ _ _ hb hc)
  | R0 C X Y W t a b _ =>
    intro T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, ha⟩ := typing_app h1
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1; exact ha
  | RS C X Y W t n a b _ =>
    intro T hT
    obtain ⟨h1, hb⟩ := typing_app hT
    obtain ⟨h1, ha⟩ := typing_app h1
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1
    exact .app _ _ _ _ (.app _ _ _ _ hb (typing_num Γ n))
      (.app _ _ _ _ (.app _ _ _ _ (.app _ _ _ _ (.R _) (typing_num Γ n)) ha) hb)
  | P1 A B C D X Y Z a b =>
    intro T hT
    obtain ⟨h1, hp⟩ := typing_app hT
    cases h1
    obtain ⟨h2, _⟩ := typing_app hp
    obtain ⟨h3, ha⟩ := typing_app h2
    cases h3; exact ha
  | P2 A B C D X Y Z a b =>
    intro T hT
    obtain ⟨h1, hp⟩ := typing_app hT
    cases h1
    obtain ⟨h2, hb⟩ := typing_app hp
    obtain ⟨h3, _⟩ := typing_app h2
    cases h3; exact hb
  | l A M M' N _ ih =>
    intro T hT
    obtain ⟨h1, h2⟩ := typing_app hT
    exact .app _ _ _ _ (ih h1) h2
  | r A M N N' _ ih =>
    intro T hT
    obtain ⟨h1, h2⟩ := typing_app hT
    exact .app _ _ _ _ h1 (ih h2)

/-! ## The ordinal assignment -/

/-- Rocq: `SystemTCL.ones`. -/
def ones : vec := fun _ => oone

/-- The vector of an application, given those of the function and the
argument. A recursor applied to a numeral gets `vspec`. -/
def measApp (A : Ty) (M N : Term) (mM mN : vec) : vec :=
  match M with
  | Rc C =>
    match isNum N with
    | some n => vspec (lev C) n
    | none => box (lev A) (gen (lev C)) mN
  | var _ => box (lev A) mM mN
  | Kc _ _ => box (lev A) mM mN
  | Sc _ _ _ => box (lev A) mM mN
  | Zc => box (lev A) mM mN
  | Suc => box (lev A) mM mN
  | Pc _ _ => box (lev A) mM mN
  | P1c _ _ => box (lev A) mM mN
  | P2c _ _ => box (lev A) mM mN
  | app _ _ _ => box (lev A) mM mN

/-- Rocq: `SystemTCL.meas`. -/
def meas : Term → vec
  | Rc C => gen (lev C)
  | app A M N => measApp A M N (meas M) (meas N)
  | var _ => ones
  | Kc _ _ => ones
  | Sc _ _ _ => ones
  | Zc => ones
  | Suc => ones
  | Pc _ _ => ones
  | P1c _ _ => ones
  | P2c _ _ => ones

/-- Rocq: `SystemTCL.meas_app`. -/
theorem meas_app (A : Ty) {M : Term} (N : Term) (h : ∀ C, M ≠ Rc C) :
    meas (app A M N) = box (lev A) (meas M) (meas N) := by
  cases M with
  | Rc C => exact absurd rfl (h C)
  | _ => rfl

/-- Rocq: `SystemTCL.meas_app_nonum`. -/
theorem meas_app_nonum (A : Ty) (M : Term) {N : Term} (h : isNum N = none) :
    meas (app A M N) = box (lev A) (meas M) (meas N) := by
  cases M with
  | Rc C =>
    show (match isNum N with
      | some n => vspec (lev C) n
      | none => box (lev A) (gen (lev C)) (meas N)) = _
    rw [h]; rfl
  | _ => rfl

/-- Rocq: `SystemTCL.vspec_le_gen`. -/
theorem vspec_le_gen (k n j : Nat) : sz (vspec k n j) ≤ sz (gen k j) := by
  show sz (if j = k + 2 then onat (n + 1) else oone) ≤ sz (if j = k + 2 then oomega else oone)
  by_cases h : j = k + 2
  · rw [ite_eq_left h, ite_eq_left h]
    exact le_of_lt (lt_of_le_of_lt (onat_eq _).le (lt_of_lt_of_le (index_lt ω ⟨n + 1⟩) oomega_eq.ge))
  · rw [ite_eq_right h, ite_eq_right h]

/-- The vector of a numeral-applied recursor is at most that of the unapplied
recursor applied to the numeral. Rocq: `SystemTCL.meas_app_le`. -/
theorem meas_app_le (A : Ty) (M N : Term) (j : Nat) :
    sz (meas (app A M N) j) ≤ sz (box (lev A) (meas M) (meas N) j) := by
  cases M with
  | Rc C =>
    show sz ((match isNum N with
      | some n => vspec (lev C) n
      | none => box (lev A) (gen (lev C)) (meas N)) j) ≤ _
    cases isNum N with
    | some n => exact le_trans (vspec_le_gen _ _ _) (box_ge_f _ _ _ _)
    | none => exact le_refl _
  | _ => exact le_refl _

/-- Rocq: `SystemTCL.ones_pos`. -/
theorem ones_pos (j : Nat) : 0 < sz (ones j) := oone_pos

/-- Rocq: `SystemTCL.meas_pos`. -/
theorem meas_pos : ∀ (M : Term) (j : Nat), 0 < sz (meas M j)
  | Rc C, j => gen_pos _ j
  | app A M N, j => by
    cases M with
    | Rc C =>
      show 0 < sz ((match isNum N with
        | some n => vspec (lev C) n
        | none => box (lev A) (gen (lev C)) (meas N)) j)
      cases isNum N with
      | some n => exact vspec_pos _ _ _
      | none => exact box_pos _ _ _ (gen_pos _) j
    | _ => exact box_pos _ _ _ (meas_pos _) j
  | var _, _ => oone_pos
  | Kc _ _, _ => oone_pos
  | Sc _ _ _, _ => oone_pos
  | Zc, _ => oone_pos
  | Suc, _ => oone_pos
  | Pc _ _, _ => oone_pos
  | P1c _ _, _ => oone_pos
  | P2c _ _, _ => oone_pos

/-- Rocq: `SystemTCL.one_lt_oexp_onat`. -/
theorem one_lt_oexp_onat (n : Nat) : sz oone < sz (oexp (onat (n + 1))) :=
  lt_of_le_of_lt oone_eq.le
    (lt_of_le_of_lt (pow_zero ω).ge
      (lt_of_lt_of_le (pow_lt_pow_right omega_gt1
        (lt_of_lt_of_le (ofNat_increasing (Nat.zero_lt_succ n)) (onat_eq (n + 1)).ge))
        (oexp_eq _).ge))

/-- Rocq: `SystemTCL.num_meas`. -/
theorem num_meas : ∀ n : Nat, sz (meas (num n) 0) < sz (oexp (onat (n + 1)))
  | 0 => one_lt_oexp_onat 0
  | n + 1 => by
    show sz (box 0 ones (meas (num n)) 0) < _
    rw [box_lo ones _ (Nat.le_refl 0), box_hi ones (meas (num n)) Nat.zero_lt_one]
    refine lt_of_lt_of_le (wm_increasing _ (y' := oexp (onat (n + 1)))
      (lt_of_le_of_lt (oadd_eq _ _).le (below_oexp _ (one_lt_oexp_onat n) (num_meas n)))) ?_
    refine le_trans (wm_oexp _ _).le (oexp_mono ?_)
    refine le_trans (oadd_eq _ _).le (le_trans (nadd_congr oone_eq (onat_eq _)).le ?_)
    refine le_trans (nadd_comm _ _).le (le_trans (nadd_succ2 _ _).le ?_)
    exact le_trans (succ_congruence (nadd_zero_r _)).le (onat_eq (n + 2)).ge

/-! ## Every reduction step decreases the assignment

`decr m f g`: `g` is at most `f` at every level up to `m`, and below it at
level `0`. -/

/-- Rocq: `SystemTCL.decr`. -/
def Decr (m : Nat) (f g : vec) : Prop := sz (g 0) < sz (f 0) ∧ ∀ i, i ≤ m → sz (g i) ≤ sz (f i)

/-- Rocq: `SystemTCL.decr_of_lt`. -/
theorem decr_of_lt {m : Nat} {f g : vec} (h : ∀ i, i ≤ m → sz (g i) < sz (f i)) : Decr m f g :=
  ⟨h 0 (Nat.zero_le m), fun i hi => le_of_lt (h i hi)⟩

/-- Rocq: `SystemTCL.meas_R_num`. -/
theorem meas_R_num (A C : Ty) {t : Term} {n : Nat} (h : isNum t = some n) :
    meas (app A (Rc C) t) = vspec (lev C) n := by
  show (match isNum t with
    | some n => vspec (lev C) n
    | none => box (lev A) (gen (lev C)) (meas t)) = _
  rw [h]

theorem max_succ_self (k : Nat) : Nat.max (k + 1) k = k + 1 :=
  ite_eq_right (Nat.not_succ_le_self k)

/-- Rocq: `SystemTCL.lev_rec_step`. -/
theorem lev_rec_step (C : Ty) : lev (TAr TN (TAr C C)) = lev C + 1 := by
  show Nat.max (0 + 1) (Nat.max (lev C + 1) (lev C)) = lev C + 1
  rw [max_succ_self]
  exact ite_eq_left (Nat.succ_le_succ (Nat.zero_le _))

/-- Rocq: `SystemTCL.step_not_Rc`. -/
theorem step_not_Rc (C : Ty) (M : Term) (h : Step (Rc C) M) : False := nomatch h

theorem lt_max_succ (a b : Nat) : a < Nat.max (a + 1) b :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_max_left _ _)

/-- Rocq: `SystemTCL.step_decreases`. -/
theorem step_decreases {M M' : Term} (h : Step M M') :
    ∀ {Γ : List Ty} {T : Ty}, Typing Γ M T → Decr (lev T) (meas M) (meas M') := by
  induction h with
  | K A B X Y a b =>
    intro Γ T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1
    refine decr_of_lt (fun i hi => ?_)
    show sz (meas a i) < sz (box (lev B) (box (lev A) ones (meas a)) (meas b) i)
    exact lt_of_lt_of_le (oadd_lt2 _ _ (ones_pos i))
      (le_trans (box_ge_sum ones (meas a) hi) (box_ge_f _ _ _ _))
  | S A B C X Y W a b c =>
    intro Γ T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, _⟩ := typing_app h1
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1
    refine decr_of_lt (fun i hi => ?_)
    refine lt_of_le_of_lt (le_trans (meas_app_le _ _ _ i)
      (box_mono_all _ (meas_app_le _ _ _) (meas_app_le _ _ _) i)) ?_
    exact S_decrease (lev (TAr A (TAr B C))) (lev (TAr A B)) (lev A) (lev B) (lev C) ones
      (meas a) (meas b) (meas c) ones_pos (meas_pos a) (meas_pos b) (meas_pos c)
      (lt_max_succ _ _) (lt_max_succ _ _) (Nat.le_max_right _ _)
      (Nat.lt_of_lt_of_le (lt_max_succ _ _) (Nat.le_max_right _ _))
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) i hi
  | R0 C X Y W t a b ht =>
    intro Γ T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, _⟩ := typing_app h1
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1
    refine decr_of_lt (fun i hi => ?_)
    show sz (meas a i) < sz (box (lev (TAr TN (TAr C C))) (box (lev C) (meas (app TN (Rc C) t))
      (meas a)) (meas b) i)
    rw [meas_R_num TN C ht]
    exact lt_of_lt_of_le (oadd_lt2 _ _ (vspec_pos _ _ i))
      (le_trans (box_ge_sum _ _ hi) (box_ge_f _ _ _ _))
  | RS C X Y W t n a b ht =>
    intro Γ T hT
    obtain ⟨h1, _⟩ := typing_app hT
    obtain ⟨h1, _⟩ := typing_app h1
    obtain ⟨h1, _⟩ := typing_app h1
    cases h1
    have Erhs : meas (app (TAr TN (TAr C C)) (app C (app TN (Rc C) t) a) b) =
        box (lev C + 1) (box (lev C) (vspec (lev C) (n + 1)) (meas a)) (meas b) := by
      show box (lev (TAr TN (TAr C C))) (box (lev C) (meas (app TN (Rc C) t)) (meas a)) (meas b) = _
      rw [meas_R_num TN C ht, lev_rec_step]
    have Erec : meas (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) a) b) =
        box (lev C + 1) (box (lev C) (vspec (lev C) n) (meas a)) (meas b) := by
      show box (lev (TAr TN (TAr C C))) (box (lev C) (meas (app TN (Rc C) (num n))) (meas a))
        (meas b) = _
      rw [meas_R_num TN C (isNum_num n), lev_rec_step]
    rw [Erhs]
    refine decr_of_lt (fun i hi => ?_)
    refine lt_of_le_of_lt (le_trans (meas_app_le _ _ _ i)
      (box_mono_all _ (meas_app_le _ _ _) (fun j => by rw [Erec]) i)) ?_
    exact R_decrease (lev C) n (meas a) (meas b) (meas (num n)) (meas_pos a) (meas_pos b)
      (num_meas n) i hi
  | P1 A B C D X Y Z a b =>
    intro Γ T hT
    obtain ⟨h1, hp⟩ := typing_app hT
    cases h1
    obtain ⟨h2, _⟩ := typing_app hp
    obtain ⟨h3, _⟩ := typing_app h2
    cases h3
    refine decr_of_lt (fun i hi => ?_)
    show sz (meas a i) < sz (box (lev (TPr A B)) ones
      (box (lev B) (box (lev A) ones (meas a)) (meas b)) i)
    exact lt_of_lt_of_le (oadd_lt2 (ones i) (meas a i) (ones_pos i))
      (le_trans (oadd_mono (le_refl _) (le_trans (oadd_le2 _ _)
          (le_trans (box_ge_sum ones (meas a) hi) (box_ge_f _ _ _ _))))
        (box_ge_sum _ _ (Nat.le_trans hi (Nat.le_max_left _ _))))
  | P2 A B C D X Y Z a b =>
    intro Γ T hT
    obtain ⟨h1, hp⟩ := typing_app hT
    cases h1
    obtain ⟨h2, _⟩ := typing_app hp
    obtain ⟨h3, _⟩ := typing_app h2
    cases h3
    refine decr_of_lt (fun i hi => ?_)
    show sz (meas b i) < sz (box (lev (TPr A B)) ones
      (box (lev B) (box (lev A) ones (meas a)) (meas b)) i)
    exact lt_of_lt_of_le (oadd_lt2 (ones i) (meas b i) (ones_pos i))
      (le_trans (oadd_mono (le_refl _) (le_trans (oadd_le2 _ _) (box_ge_sum _ (meas b) hi)))
        (box_ge_sum _ _ (Nat.le_trans hi (Nat.le_max_right _ _))))
  | l A0 M M' N hs ih =>
    intro Γ T hT
    obtain ⟨hM, _⟩ := typing_app hT
    obtain ⟨IH0, IHle⟩ := ih hM
    have hnr : ∀ C, M ≠ Rc C := fun C e => by subst e; exact step_not_Rc C _ hs
    rw [meas_app A0 N hnr]
    have hnm : lev A0 < lev (TAr A0 T) := lt_max_succ _ _
    exact ⟨lt_of_le_of_lt (meas_app_le _ _ _ 0)
        (box_lt0 hnm IHle (fun _ _ => le_refl _) (.inl IH0)),
      fun i hi => le_trans (meas_app_le _ _ _ i)
        (box_mono hnm IHle (fun _ _ => le_refl _) i (Nat.le_trans hi (Nat.le_max_right _ _)))⟩
  | r A0 M N N' hs ih =>
    intro Γ T hT
    obtain ⟨_, hN⟩ := typing_app hT
    obtain ⟨IH0, IHle⟩ := ih hN
    have hn : isNum N = none := by
      cases e : isNum N with
      | none => rfl
      | some k => rw [isNum_spec N k e] at hs; exact (num_normal k _ hs).elim
    rw [meas_app_nonum A0 M hn]
    have hnm : lev A0 < lev (TAr A0 T) := lt_max_succ _ _
    exact ⟨lt_of_le_of_lt (meas_app_le _ _ _ 0)
        (box_lt0 hnm (fun _ _ => le_refl _) IHle (.inr IH0)),
      fun i hi => le_trans (meas_app_le _ _ _ i)
        (box_mono hnm (fun _ _ => le_refl _) IHle i (Nat.le_trans hi (Nat.le_max_right _ _)))⟩

/-! ## Strong normalization -/

/-- Rocq: `SystemTCL.SN`. -/
def SN (M : Term) : Prop := Acc (fun N M => Step M N) M

/-- Rocq: `SystemTCL.typed_SN`. -/
theorem typed_SN {Γ : List Ty} {M : Term} {A : Ty} (h : Typing Γ M A) : SN M := by
  have key : ∀ x : Ordinal.{0}, ∀ (M : Term) (A : Ty), Typing Γ M A → sz (meas M 0) ≤ x → SN M := by
    intro x
    induction x using lt_wf.induction with
    | _ x ih =>
      intro M A hM hx
      refine Acc.intro M (fun M' hs => ?_)
      exact ih _ (lt_of_lt_of_le (step_decreases hs hM).1 hx) M' A (subject_reduction hs hM) (le_refl _)
  exact key _ M A h (le_refl _)

/-- The ordinal of a term is a notation, so below ε₀. Rocq: `SystemTCL.meas_below_ε0`. -/
theorem meas_below_ε0 (M : Term) : sz (meas M 0) < ε 0 := ON_below_ε0 _

/-! ## Confluence

By Takahashi's method: parallel reduction, and the complete development
`cd M`, which contracts every redex of `M` at once. -/

/-- Rocq: `SystemTCL.star`. -/
inductive Star : Term → Term → Prop where
  | refl (M : Term) : Star M M
  | step (M N P : Term) : Step M N → Star N P → Star M P

/-- Rocq: `SystemTCL.star_trans`. -/
theorem star_trans {M N P : Term} (h : Star M N) (h' : Star N P) : Star M P := by
  induction h with
  | refl => exact h'
  | step _ _ _ hs _ ih => exact .step _ _ _ hs (ih h')

/-- Rocq: `SystemTCL.star_one`. -/
theorem star_one {M N : Term} (h : Step M N) : Star M N := .step _ _ _ h (.refl _)

/-- Rocq: `SystemTCL.star_app_l`. -/
theorem star_app_l (A : Ty) {M M' : Term} (N : Term) (h : Star M M') : Star (app A M N) (app A M' N) := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hs _ ih => exact .step _ _ _ (.l _ _ _ _ hs) ih

/-- Rocq: `SystemTCL.star_app_r`. -/
theorem star_app_r (A : Ty) (M : Term) {N N' : Term} (h : Star N N') : Star (app A M N) (app A M N') := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hs _ ih => exact .step _ _ _ (.r _ _ _ _ hs) ih

/-- Rocq: `SystemTCL.star_app`. -/
theorem star_app (A : Ty) {M M' N N' : Term} (hM : Star M M') (hN : Star N N') :
    Star (app A M N) (app A M' N') :=
  star_trans (star_app_l A N hM) (star_app_r A M' hN)

/-- Rocq: `SystemTCL.par`. -/
inductive Par : Term → Term → Prop where
  | refl (M : Term) : Par M M
  | app (A : Ty) (M M' N N' : Term) : Par M M' → Par N N' → Par (app A M N) (app A M' N')
  | K (A B X Y : Ty) (a a' b : Term) : Par a a' → Par (app Y (app X (Kc A B) a) b) a'
  | S (A B C X Y W : Ty) (a a' b b' c c' : Term) : Par a a' → Par b b' → Par c c' →
      Par (app W (app Y (app X (Sc A B C) a) b) c) (app B (app A a' c') (app A b' c'))
  | R0 (C X Y W : Ty) (t a a' b : Term) : isNum t = some 0 → Par a a' →
      Par (app W (app Y (app X (Rc C) t) a) b) a'
  | RS (C X Y W : Ty) (t : Term) (n : Nat) (a a' b b' : Term) : isNum t = some (n + 1) →
      Par a a' → Par b b' →
      Par (app W (app Y (app X (Rc C) t) a) b)
        (app C (app TN b' (num n)) (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) a') b'))
  | P1 (A B C D X Y Z : Ty) (a a' b : Term) : Par a a' →
      Par (app X (P1c A B) (app Y (app Z (Pc C D) a) b)) a'
  | P2 (A B C D X Y Z : Ty) (a b b' : Term) : Par b b' →
      Par (app X (P2c A B) (app Y (app Z (Pc C D) a) b)) b'

/-- Rocq: `SystemTCL.step_par`. -/
theorem step_par {M N : Term} (h : Step M N) : Par M N := by
  induction h with
  | K => exact .K _ _ _ _ _ _ _ (.refl _)
  | S => exact .S _ _ _ _ _ _ _ _ _ _ _ _ (.refl _) (.refl _) (.refl _)
  | R0 _ _ _ _ _ _ _ ht => exact .R0 _ _ _ _ _ _ _ _ ht (.refl _)
  | RS _ _ _ _ _ _ _ _ ht => exact .RS _ _ _ _ _ _ _ _ _ _ ht (.refl _) (.refl _)
  | P1 => exact .P1 _ _ _ _ _ _ _ _ _ _ (.refl _)
  | P2 => exact .P2 _ _ _ _ _ _ _ _ _ _ (.refl _)
  | l _ _ _ _ _ ih => exact .app _ _ _ _ _ ih (.refl _)
  | r _ _ _ _ _ ih => exact .app _ _ _ _ _ (.refl _) ih

/-- Rocq: `SystemTCL.par_star`. -/
theorem par_star {M N : Term} (h : Par M N) : Star M N := by
  induction h with
  | refl => exact .refl _
  | app _ _ _ _ _ _ _ ih1 ih2 => exact star_app _ ih1 ih2
  | K _ _ _ _ _ _ _ _ ih => exact .step _ _ _ (.K _ _ _ _ _ _) ih
  | S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iha ihb ihc =>
    exact star_trans (star_app _ (star_app _ (star_app_r _ _ iha) ihb) ihc) (star_one (.S _ _ _ _ _ _ _ _ _))
  | R0 _ _ _ _ _ _ _ _ ht _ ih => exact .step _ _ _ (.R0 _ _ _ _ _ _ _ ht) ih
  | RS _ _ _ _ _ _ _ _ _ _ ht _ _ iha ihb =>
    exact star_trans (star_app _ (star_app_r _ _ iha) ihb) (star_one (.RS _ _ _ _ _ _ _ _ ht))
  | P1 _ _ _ _ _ _ _ _ _ _ _ ih => exact .step _ _ _ (.P1 _ _ _ _ _ _ _ _ _) ih
  | P2 _ _ _ _ _ _ _ _ _ _ _ ih => exact .step _ _ _ (.P2 _ _ _ _ _ _ _ _ _) ih

/-- The complete development, which contracts every redex at once. Every case
is spelled out, since a wildcard would make it depend on `propext`.
Rocq: `SystemTCL.cd`. -/
def cd : Term → Term
  | var i => var i
  | Kc A B => Kc A B
  | Sc A B C => Sc A B C
  | Zc => Zc
  | Suc => Suc
  | Rc C => Rc C
  | Pc A B => Pc A B
  | P1c A B => P1c A B
  | P2c A B => P2c A B
  | app W F c =>
    let cF := cd F
    let cc := cd c
    match F with
    | app _ G b =>
      match G with
      | Kc _ _ => cd b
      | app _ H a =>
        match H with
        | Sc A B _ => app B (app A (cd a) cc) (app A (cd b) cc)
        | Rc C =>
          match isNum a with
          | some 0 => cd b
          | some (n + 1) =>
            app C (app TN cc (num n))
              (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) (cd b)) cc)
          | none => app W cF cc
        | var _ => app W cF cc
        | Kc _ _ => app W cF cc
        | Zc => app W cF cc
        | Suc => app W cF cc
        | Pc _ _ => app W cF cc
        | P1c _ _ => app W cF cc
        | P2c _ _ => app W cF cc
        | app _ _ _ => app W cF cc
      | var _ => app W cF cc
      | Sc _ _ _ => app W cF cc
      | Zc => app W cF cc
      | Suc => app W cF cc
      | Rc _ => app W cF cc
      | Pc _ _ => app W cF cc
      | P1c _ _ => app W cF cc
      | P2c _ _ => app W cF cc
    | P1c _ _ =>
      match c with
      | app _ G _ =>
        match G with
        | app _ H a =>
          match H with
          | Pc _ _ => cd a
          | var _ => app W F cc
          | Kc _ _ => app W F cc
          | Sc _ _ _ => app W F cc
          | Zc => app W F cc
          | Suc => app W F cc
          | Rc _ => app W F cc
          | P1c _ _ => app W F cc
          | P2c _ _ => app W F cc
          | app _ _ _ => app W F cc
        | var _ => app W F cc
        | Kc _ _ => app W F cc
        | Sc _ _ _ => app W F cc
        | Zc => app W F cc
        | Suc => app W F cc
        | Rc _ => app W F cc
        | Pc _ _ => app W F cc
        | P1c _ _ => app W F cc
        | P2c _ _ => app W F cc
      | var _ => app W F cc
      | Kc _ _ => app W F cc
      | Sc _ _ _ => app W F cc
      | Zc => app W F cc
      | Suc => app W F cc
      | Rc _ => app W F cc
      | Pc _ _ => app W F cc
      | P1c _ _ => app W F cc
      | P2c _ _ => app W F cc
    | P2c _ _ =>
      match c with
      | app _ G b =>
        match G with
        | app _ H _ =>
          match H with
          | Pc _ _ => cd b
          | var _ => app W F cc
          | Kc _ _ => app W F cc
          | Sc _ _ _ => app W F cc
          | Zc => app W F cc
          | Suc => app W F cc
          | Rc _ => app W F cc
          | P1c _ _ => app W F cc
          | P2c _ _ => app W F cc
          | app _ _ _ => app W F cc
        | var _ => app W F cc
        | Kc _ _ => app W F cc
        | Sc _ _ _ => app W F cc
        | Zc => app W F cc
        | Suc => app W F cc
        | Rc _ => app W F cc
        | Pc _ _ => app W F cc
        | P1c _ _ => app W F cc
        | P2c _ _ => app W F cc
      | var _ => app W F cc
      | Kc _ _ => app W F cc
      | Sc _ _ _ => app W F cc
      | Zc => app W F cc
      | Suc => app W F cc
      | Rc _ => app W F cc
      | Pc _ _ => app W F cc
      | P1c _ _ => app W F cc
      | P2c _ _ => app W F cc
    | var _ => app W cF cc
    | Kc _ _ => app W cF cc
    | Sc _ _ _ => app W cF cc
    | Zc => app W cF cc
    | Suc => app W cF cc
    | Rc _ => app W cF cc
    | Pc _ _ => app W cF cc

/-- Rocq: `SystemTCL.is_pair`. -/
def IsPair (c : Term) : Prop := ∃ Y Z C D a b, c = app Y (app Z (Pc C D) a) b

/-- Rocq: `SystemTCL.pair_dec`. -/
theorem pair_dec (c : Term) : IsPair c ∨ ¬ IsPair c := by
  cases c with
  | app Y G b =>
    cases G with
    | app Z H a =>
      cases H with
      | Pc C D => exact .inl ⟨Y, Z, C, D, a, b, rfl⟩
      | _ => exact .inr fun ⟨_, _, _, _, _, _, h⟩ => by cases h
    | _ => exact .inr fun ⟨_, _, _, _, _, _, h⟩ => by cases h
  | _ => exact .inr fun ⟨_, _, _, _, _, _, h⟩ => by cases h

/-- Rocq: `SystemTCL.cd_P1_nopair`. -/
theorem cd_P1_nopair (W A B : Ty) (c : Term) (hc : ¬ IsPair c) :
    cd (app W (P1c A B) c) = app W (P1c A B) (cd c) := by
  cases c with
  | app Y G b =>
    cases G with
    | app Z H a =>
      cases H with
      | Pc C D => exact absurd ⟨Y, Z, C, D, a, b, rfl⟩ hc
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- Rocq: `SystemTCL.cd_P2_nopair`. -/
theorem cd_P2_nopair (W A B : Ty) (c : Term) (hc : ¬ IsPair c) :
    cd (app W (P2c A B) c) = app W (P2c A B) (cd c) := by
  cases c with
  | app Y G b =>
    cases G with
    | app Z H a =>
      cases H with
      | Pc C D => exact absurd ⟨Y, Z, C, D, a, b, rfl⟩ hc
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- The default branch of `app_view`. -/
local macro "view_default" : tactic => `(tactic| (
  refine .inr (.inr (.inr (.inr (.inr ⟨rfl, ?_, ?_, ?_, ?_⟩))))
  · intro _ _ _ _ h; cases h
  · intro _ _ _ _ _ _ _ h; cases h
  · intro _ _ _ _ _ h; cases h
  · intro ⟨_, _, h⟩; cases h with | inl h => cases h | inr h => cases h))

/-- The shapes of an application, as `cd` sees them. Rocq: `SystemTCL.app_view`. -/
theorem app_view (W : Ty) (F c : Term) :
    (∃ X A B a, F = app X (Kc A B) a) ∨
    (∃ Y X A B C a b, F = app Y (app X (Sc A B C) a) b) ∨
    (∃ Y X C t a n, F = app Y (app X (Rc C) t) a ∧ isNum t = some n) ∨
    (∃ A B Y Z C D a b, F = P1c A B ∧ c = app Y (app Z (Pc C D) a) b) ∨
    (∃ A B Y Z C D a b, F = P2c A B ∧ c = app Y (app Z (Pc C D) a) b) ∨
    (cd (app W F c) = app W (cd F) (cd c) ∧
     (∀ X A B a, F ≠ app X (Kc A B) a) ∧
     (∀ Y X A B C a b, F ≠ app Y (app X (Sc A B C) a) b) ∧
     (∀ Y X C t a, F = app Y (app X (Rc C) t) a → isNum t = none) ∧
     ((∃ A B, F = P1c A B ∨ F = P2c A B) → ¬ IsPair c)) := by
  cases F with
  | app Y G b =>
    cases G with
    | Kc A B => exact .inl ⟨_, _, _, _, rfl⟩
    | app X H a =>
      cases H with
      | Sc A B C => exact .inr (.inl ⟨_, _, _, _, _, _, _, rfl⟩)
      | Rc C =>
        cases e : isNum a with
        | some n => exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, e⟩))
        | none =>
          refine .inr (.inr (.inr (.inr (.inr ⟨?_, ?_, ?_, ?_, ?_⟩))))
          · dsimp only [cd]; rw [e]
          · intro _ _ _ _ h; cases h
          · intro _ _ _ _ _ _ _ h; cases h
          · intro _ _ _ _ _ h; cases h; exact e
          · intro ⟨_, _, h⟩; cases h with | inl h => cases h | inr h => cases h
      | var _ => view_default
      | Kc _ _ => view_default
      | Zc => view_default
      | Suc => view_default
      | Pc _ _ => view_default
      | P1c _ _ => view_default
      | P2c _ _ => view_default
      | app _ _ _ => view_default
    | var _ => view_default
    | Sc _ _ _ => view_default
    | Zc => view_default
    | Suc => view_default
    | Rc _ => view_default
    | Pc _ _ => view_default
    | P1c _ _ => view_default
    | P2c _ _ => view_default
  | P1c A B =>
    cases pair_dec c with
    | inl hp =>
      obtain ⟨Y, Z, C, D, a, b, rfl⟩ := hp
      exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩)))
    | inr hp =>
      refine .inr (.inr (.inr (.inr (.inr ⟨cd_P1_nopair W A B c hp, ?_, ?_, ?_, fun _ => hp⟩))))
      · intro _ _ _ _ h; cases h
      · intro _ _ _ _ _ _ _ h; cases h
      · intro _ _ _ _ _ h; cases h
  | P2c A B =>
    cases pair_dec c with
    | inl hp =>
      obtain ⟨Y, Z, C, D, a, b, rfl⟩ := hp
      exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, rfl⟩))))
    | inr hp =>
      refine .inr (.inr (.inr (.inr (.inr ⟨cd_P2_nopair W A B c hp, ?_, ?_, ?_, fun _ => hp⟩))))
      · intro _ _ _ _ h; cases h
      · intro _ _ _ _ _ _ _ h; cases h
      · intro _ _ _ _ _ h; cases h
  | var _ => view_default
  | Kc _ _ => view_default
  | Sc _ _ _ => view_default
  | Zc => view_default
  | Suc => view_default
  | Rc _ => view_default
  | Pc _ _ => view_default

/-- Rocq: `SystemTCL.par_atom`. -/
theorem par_atom {M N : Term} (h : Par M N) (hm : ∀ A F c, M ≠ app A F c) : N = M := by
  cases h with
  | refl => rfl
  | _ => exact absurd rfl (hm _ _ _)

/-- Rocq: `SystemTCL.par_num`. -/
theorem par_num : ∀ (n : Nat) {N : Term}, Par (num n) N → N = num n
  | 0, _, h => par_atom h (fun _ _ _ e => by cases e)
  | n + 1, _, h => by
    cases h with
    | refl => rfl
    | app _ _ _ _ _ hs hn =>
      rw [par_atom hs (fun _ _ _ e => by cases e), par_num n hn]; rfl

/-- Rocq: `SystemTCL.par_K1`. -/
theorem par_K1 {X A B : Ty} {a N : Term} (h : Par (app X (Kc A B) a) N) :
    ∃ a', N = app X (Kc A B) a' ∧ Par a a' := by
  cases h with
  | refl => exact ⟨a, rfl, .refl _⟩
  | app _ _ _ _ _ hK ha => rw [par_atom hK (fun _ _ _ e => by cases e)]; exact ⟨_, rfl, ha⟩

/-- Rocq: `SystemTCL.par_S1`. -/
theorem par_S1 {X A B C : Ty} {a N : Term} (h : Par (app X (Sc A B C) a) N) :
    ∃ a', N = app X (Sc A B C) a' ∧ Par a a' := by
  cases h with
  | refl => exact ⟨a, rfl, .refl _⟩
  | app _ _ _ _ _ hK ha => rw [par_atom hK (fun _ _ _ e => by cases e)]; exact ⟨_, rfl, ha⟩

/-- Rocq: `SystemTCL.par_S2`. -/
theorem par_S2 {Y X A B C : Ty} {a b N : Term} (h : Par (app Y (app X (Sc A B C) a) b) N) :
    ∃ a' b', N = app Y (app X (Sc A B C) a') b' ∧ Par a a' ∧ Par b b' := by
  cases h with
  | refl => exact ⟨a, b, rfl, .refl _, .refl _⟩
  | app _ _ _ _ _ hF hb =>
    obtain ⟨a', rfl, ha⟩ := par_S1 hF
    exact ⟨a', _, rfl, ha, hb⟩

/-- Rocq: `SystemTCL.par_R1`. -/
theorem par_R1 {X C : Ty} {t N : Term} (h : Par (app X (Rc C) t) N) :
    ∃ t', N = app X (Rc C) t' ∧ Par t t' := by
  cases h with
  | refl => exact ⟨t, rfl, .refl _⟩
  | app _ _ _ _ _ hK ht => rw [par_atom hK (fun _ _ _ e => by cases e)]; exact ⟨_, rfl, ht⟩

/-- Rocq: `SystemTCL.par_R2`. -/
theorem par_R2 {Y X C : Ty} {t a N : Term} (h : Par (app Y (app X (Rc C) t) a) N) :
    ∃ t' a', N = app Y (app X (Rc C) t') a' ∧ Par t t' ∧ Par a a' := by
  cases h with
  | refl => exact ⟨t, a, rfl, .refl _, .refl _⟩
  | app _ _ _ _ _ hF ha =>
    obtain ⟨t', rfl, ht⟩ := par_R1 hF
    exact ⟨t', _, rfl, ht, ha⟩

/-- Rocq: `SystemTCL.par_Pc1`. -/
theorem par_Pc1 {X A B : Ty} {a N : Term} (h : Par (app X (Pc A B) a) N) :
    ∃ a', N = app X (Pc A B) a' ∧ Par a a' := by
  cases h with
  | refl => exact ⟨a, rfl, .refl _⟩
  | app _ _ _ _ _ hK ha => rw [par_atom hK (fun _ _ _ e => by cases e)]; exact ⟨_, rfl, ha⟩

/-- Rocq: `SystemTCL.par_Pc2`. -/
theorem par_Pc2 {Y X A B : Ty} {a b N : Term} (h : Par (app Y (app X (Pc A B) a) b) N) :
    ∃ a' b', N = app Y (app X (Pc A B) a') b' ∧ Par a a' ∧ Par b b' := by
  cases h with
  | refl => exact ⟨a, b, rfl, .refl _, .refl _⟩
  | app _ _ _ _ _ hF hb =>
    obtain ⟨a', rfl, ha⟩ := par_Pc1 hF
    exact ⟨a', _, rfl, ha, hb⟩

theorem cd_num : ∀ n, cd (num n) = num n
  | 0 => rfl
  | n + 1 => by show app TN Suc (cd (num n)) = _; rw [cd_num n]; rfl

/-- Rocq: `SystemTCL.par_self_cd`. -/
theorem par_self_cd : ∀ M : Term, Par M (cd M)
  | var _ => .refl _
  | Kc _ _ => .refl _
  | Sc _ _ _ => .refl _
  | Zc => .refl _
  | Suc => .refl _
  | Rc _ => .refl _
  | Pc _ _ => .refl _
  | P1c _ _ => .refl _
  | P2c _ _ => .refl _
  | app W F c => by
    have ihF := par_self_cd F
    have ihc := par_self_cd c
    rcases app_view W F c with ⟨X, A, B, a, rfl⟩ | ⟨Y, X, A, B, C, a, b, rfl⟩ |
        ⟨Y, X, C, t, a, n, rfl, hn⟩ | ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ |
        ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ | ⟨hcd, -⟩
    · obtain ⟨a', E, ha⟩ := par_K1 ihF
      have E' : app X (Kc A B) (cd a) = app X (Kc A B) a' := E
      injection E' with _ _ e
      show Par _ (cd a)
      rw [e]; exact .K _ _ _ _ _ _ _ ha
    · obtain ⟨a', b', E, ha, hb⟩ := par_S2 ihF
      have E' : app Y (app X (Sc A B C) (cd a)) (cd b) = app Y (app X (Sc A B C) a') b' := E
      injection E' with _ e1 e2
      injection e1 with _ _ e1
      show Par _ (app B (app A (cd a) (cd c)) (app A (cd b) (cd c)))
      rw [e1, e2]; exact .S _ _ _ _ _ _ _ _ _ _ _ _ ha hb ihc
    · obtain ⟨t', a', E, _, ha⟩ := par_R2 ihF
      have E' : app Y (app X (Rc C) (cd t)) (cd a) = app Y (app X (Rc C) t') a' := E
      injection E' with _ _ e
      dsimp only [cd]
      rw [hn]
      cases n with
      | zero => rw [e]; exact .R0 _ _ _ _ _ _ _ _ hn ha
      | succ n => rw [e]; exact .RS _ _ _ _ _ _ _ _ _ _ hn ha ihc
    · obtain ⟨a', b', E, ha, _⟩ := par_Pc2 ihc
      have E' : app Y (app Z (Pc C D) (cd a)) (cd b) = app Y (app Z (Pc C D) a') b' := E
      injection E' with _ e1 _
      injection e1 with _ _ e1
      show Par _ (cd a)
      rw [e1]; exact .P1 _ _ _ _ _ _ _ _ _ _ ha
    · obtain ⟨a', b', E, _, hb⟩ := par_Pc2 ihc
      have E' : app Y (app Z (Pc C D) (cd a)) (cd b) = app Y (app Z (Pc C D) a') b' := E
      injection E' with _ _ e2
      show Par _ (cd b)
      rw [e2]; exact .P2 _ _ _ _ _ _ _ _ _ _ hb
    · rw [hcd]; exact .app _ _ _ _ _ ihF ihc

/-- Rocq: `SystemTCL.par_cd`. -/
theorem par_cd {M N : Term} (h : Par M N) : Par N (cd M) := by
  induction h with
  | refl M => exact par_self_cd M
  | app W F F' c c' hF hc ihF ihc =>
    rcases app_view W F c with ⟨X, A, B, a, rfl⟩ | ⟨Y, X, A, B, C, a, b, rfl⟩ |
        ⟨Y, X, C, t, a, n, rfl, hn⟩ | ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ |
        ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ | ⟨hcd, -⟩
    · obtain ⟨a', rfl, _⟩ := par_K1 hF
      obtain ⟨a'', E, ha'⟩ := par_K1 ihF
      have E' : app X (Kc A B) (cd a) = app X (Kc A B) a'' := E
      injection E' with _ _ e
      show Par _ (cd a)
      rw [e]; exact .K _ _ _ _ _ _ _ ha'
    · obtain ⟨a', b', rfl, _, _⟩ := par_S2 hF
      obtain ⟨a'', b'', E, ha', hb'⟩ := par_S2 ihF
      have E' : app Y (app X (Sc A B C) (cd a)) (cd b) = app Y (app X (Sc A B C) a'') b'' := E
      injection E' with _ e1 e2
      injection e1 with _ _ e1
      show Par _ (app B (app A (cd a) (cd c)) (app A (cd b) (cd c)))
      rw [e1, e2]; exact .S _ _ _ _ _ _ _ _ _ _ _ _ ha' hb' ihc
    · obtain ⟨t', a', rfl, ht, _⟩ := par_R2 hF
      have Et := isNum_spec t n hn
      subst Et
      have Et' := par_num n ht
      subst Et'
      obtain ⟨t'', a'', E, _, ha'⟩ := par_R2 ihF
      have E' : app Y (app X (Rc C) (cd (num n))) (cd a) = app Y (app X (Rc C) t'') a'' := E
      injection E' with _ _ e
      dsimp only [cd]
      rw [isNum_num]
      cases n with
      | zero => rw [e]; exact .R0 _ _ _ _ _ _ _ _ (isNum_num 0) ha'
      | succ n => rw [e]; exact .RS _ _ _ _ _ _ _ _ _ _ (isNum_num (n + 1)) ha' ihc
    · rw [par_atom hF (fun _ _ _ e => by cases e)]
      obtain ⟨a', b', rfl, _, _⟩ := par_Pc2 hc
      obtain ⟨a'', b'', E, ha', _⟩ := par_Pc2 ihc
      have E' : app Y (app Z (Pc C D) (cd a)) (cd b) = app Y (app Z (Pc C D) a'') b'' := E
      injection E' with _ e1 _
      injection e1 with _ _ e1
      show Par _ (cd a)
      rw [e1]; exact .P1 _ _ _ _ _ _ _ _ _ _ ha'
    · rw [par_atom hF (fun _ _ _ e => by cases e)]
      obtain ⟨a', b', rfl, _, _⟩ := par_Pc2 hc
      obtain ⟨a'', b'', E, _, hb'⟩ := par_Pc2 ihc
      have E' : app Y (app Z (Pc C D) (cd a)) (cd b) = app Y (app Z (Pc C D) a'') b'' := E
      injection E' with _ _ e2
      show Par _ (cd b)
      rw [e2]; exact .P2 _ _ _ _ _ _ _ _ _ _ hb'
    · rw [hcd]; exact .app _ _ _ _ _ ihF ihc
  | K _ _ _ _ _ _ _ _ iha => exact iha
  | S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iha ihb ihc =>
    exact .app _ _ _ _ _ (.app _ _ _ _ _ iha ihc) (.app _ _ _ _ _ ihb ihc)
  | R0 _ _ _ _ _ _ _ _ ht _ iha => dsimp only [cd]; rw [ht]; exact iha
  | RS _ _ _ _ _ _ _ _ _ _ ht _ _ iha ihb =>
    dsimp only [cd]; rw [ht]
    exact .app _ _ _ _ _ (.app _ _ _ _ _ ihb (.refl _)) (.app _ _ _ _ _ (.app _ _ _ _ _ (.refl _) iha) ihb)
  | P1 _ _ _ _ _ _ _ _ _ _ _ iha => exact iha
  | P2 _ _ _ _ _ _ _ _ _ _ _ ihb => exact ihb

/-- Rocq: `SystemTCL.strip`. -/
theorem strip {M N1 N2 : Term} (h1 : Par M N1) (h2 : Star M N2) : ∃ P, Star N1 P ∧ Par N2 P := by
  induction h2 generalizing N1 with
  | refl => exact ⟨N1, .refl _, h1⟩
  | step M M1 N2 hs _ ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (par_cd (step_par hs))
    exact ⟨P, star_trans (par_star (par_cd h1)) hP1, hP2⟩

/-- Rocq: `SystemTCL.confluence`. -/
theorem confluence {M N1 N2 : Term} (h1 : Star M N1) (h2 : Star M N2) :
    ∃ P, Star N1 P ∧ Star N2 P := by
  induction h1 generalizing N2 with
  | refl => exact ⟨N2, h2, .refl _⟩
  | step M M1 N1 hs _ ih =>
    obtain ⟨Q, hQ1, hQ2⟩ := strip (step_par hs) h2
    obtain ⟨P, hP1, hP2⟩ := ih hQ1
    exact ⟨P, hP1, star_trans (par_star hQ2) hP2⟩

/-! ## Closed terms of type `N` evaluate to numerals -/

/-- Rocq: `SystemTCL.normal`. -/
def Normal (M : Term) : Prop := ∀ N, ¬ Step M N

/-- Rocq: `SystemTCL.step_or_normal`. -/
theorem step_or_normal : ∀ M : Term, (∃ N, Step M N) ∨ Normal M
  | var _ => .inr fun _ h => nomatch h
  | Kc _ _ => .inr fun _ h => nomatch h
  | Sc _ _ _ => .inr fun _ h => nomatch h
  | Zc => .inr fun _ h => nomatch h
  | Suc => .inr fun _ h => nomatch h
  | Rc _ => .inr fun _ h => nomatch h
  | Pc _ _ => .inr fun _ h => nomatch h
  | P1c _ _ => .inr fun _ h => nomatch h
  | P2c _ _ => .inr fun _ h => nomatch h
  | app W F c => by
    rcases step_or_normal F with ⟨F', hF⟩ | hF
    · exact .inl ⟨_, .l _ _ _ _ hF⟩
    rcases step_or_normal c with ⟨c', hc⟩ | hc
    · exact .inl ⟨_, .r _ _ _ _ hc⟩
    rcases app_view W F c with ⟨X, A, B, a, rfl⟩ | ⟨Y, X, A, B, C, a, b, rfl⟩ |
        ⟨Y, X, C, t, a, n, rfl, hn⟩ | ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ |
        ⟨A, B, Y, Z, C, D, a, b, rfl, rfl⟩ | ⟨_, HK, HS, HR, HP⟩
    · exact .inl ⟨_, .K _ _ _ _ _ _⟩
    · exact .inl ⟨_, .S _ _ _ _ _ _ _ _ _⟩
    · cases n with
      | zero => exact .inl ⟨_, .R0 _ _ _ _ _ _ _ hn⟩
      | succ n => exact .inl ⟨_, .RS _ _ _ _ _ _ _ _ hn⟩
    · exact .inl ⟨_, .P1 _ _ _ _ _ _ _ _ _⟩
    · exact .inl ⟨_, .P2 _ _ _ _ _ _ _ _ _⟩
    · refine .inr fun N h => ?_
      cases h with
      | K => exact HK _ _ _ _ rfl
      | S => exact HS _ _ _ _ _ _ _ rfl
      | R0 _ _ _ _ _ _ _ ht => rw [HR _ _ _ _ _ rfl] at ht; cases ht
      | RS _ _ _ _ _ _ _ _ ht => rw [HR _ _ _ _ _ rfl] at ht; cases ht
      | P1 => exact HP ⟨_, _, .inl rfl⟩ ⟨_, _, _, _, _, _, rfl⟩
      | P2 => exact HP ⟨_, _, .inr rfl⟩ ⟨_, _, _, _, _, _, rfl⟩
      | l _ _ _ _ h => exact hF _ h
      | r _ _ _ _ h => exact hc _ h

/-- Rocq: `SystemTCL.SN_normal_form`. -/
theorem SN_normal_form {M : Term} (h : SN M) : ∃ N, Star M N ∧ Normal N := by
  induction h with
  | intro M _ ih =>
    rcases step_or_normal M with ⟨M', hs⟩ | hn
    · obtain ⟨N, hN1, hN2⟩ := ih M' hs
      exact ⟨N, .step _ _ _ hs hN1, hN2⟩
    · exact ⟨M, .refl _, hn⟩

/-- Rocq: `SystemTCL.star_typing`. -/
theorem star_typing {Γ : List Ty} {M N : Term} {A : Ty} (h : Star M N) (ht : Typing Γ M A) :
    Typing Γ N A := by
  induction h with
  | refl => exact ht
  | step _ _ _ hs _ ih => exact ih (subject_reduction hs ht)

/-- Rocq: `SystemTCL.star_normal`. -/
theorem star_normal {M N : Term} (hn : Normal M) (h : Star M N) : N = M := by
  cases h with
  | refl => rfl
  | step _ _ _ hs _ => exact (hn _ hs).elim

/-- Closed normal terms are numerals, pairs, or partial applications of
constants. Rocq: `SystemTCL.value`. -/
inductive Value : Term → Prop where
  | numeral (n : Nat) : Value (num n)
  | Suc : Value Suc
  | K (A B : Ty) : Value (Kc A B)
  | K1 (X A B : Ty) (a : Term) : Value (app X (Kc A B) a)
  | S (A B C : Ty) : Value (Sc A B C)
  | S1 (X A B C : Ty) (a : Term) : Value (app X (Sc A B C) a)
  | S2 (Y X A B C : Ty) (a b : Term) : Value (app Y (app X (Sc A B C) a) b)
  | R (C : Ty) : Value (Rc C)
  | R1 (X C : Ty) (n : Nat) : Value (app X (Rc C) (num n))
  | R2 (Y X C : Ty) (n : Nat) (a : Term) : Value (app Y (app X (Rc C) (num n)) a)
  | P (A B : Ty) : Value (Pc A B)
  | P1 (X A B : Ty) (a : Term) : Value (app X (Pc A B) a)
  | P2 (Y X A B : Ty) (a b : Term) : Value (app Y (app X (Pc A B) a) b)
  | Fst (A B : Ty) : Value (P1c A B)
  | Snd (A B : Ty) : Value (P2c A B)

/-- Rocq: `SystemTCL.value_nat`. -/
theorem value_nat {Γ : List Ty} {M : Term} (hv : Value M) (ht : Typing Γ M TN) : ∃ n, M = num n := by
  cases hv with
  | numeral n => exact ⟨n, rfl⟩
  | Suc => cases ht
  | K => cases ht
  | K1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | S => cases ht
  | S1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | S2 => obtain ⟨h, _⟩ := typing_app ht; obtain ⟨h, _⟩ := typing_app h; cases h
  | R => cases ht
  | R1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | R2 => obtain ⟨h, _⟩ := typing_app ht; obtain ⟨h, _⟩ := typing_app h; cases h
  | P => cases ht
  | P1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | P2 => obtain ⟨h, _⟩ := typing_app ht; obtain ⟨h, _⟩ := typing_app h; cases h
  | Fst => cases ht
  | Snd => cases ht

/-- Rocq: `SystemTCL.value_pair`. -/
theorem value_pair {Γ : List Ty} {M : Term} {A B : Ty} (hv : Value M) (ht : Typing Γ M (TPr A B)) :
    ∃ Y X C D a b, M = app Y (app X (Pc C D) a) b := by
  cases hv with
  | numeral n => cases typing_unique ht (typing_num Γ n)
  | Suc => cases ht
  | K => cases ht
  | K1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | S => cases ht
  | S1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | S2 => obtain ⟨h, _⟩ := typing_app ht; obtain ⟨h, _⟩ := typing_app h; cases h
  | R => cases ht
  | R1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | R2 => obtain ⟨h, _⟩ := typing_app ht; obtain ⟨h, _⟩ := typing_app h; cases h
  | P => cases ht
  | P1 => obtain ⟨h, _⟩ := typing_app ht; cases h
  | P2 Y X C D a b => exact ⟨Y, X, C, D, a, b, rfl⟩
  | Fst => cases ht
  | Snd => cases ht

/-- Rocq: `SystemTCL.normal_app_l`. -/
theorem normal_app_l {A : Ty} {M N : Term} (h : Normal (app A M N)) : Normal M :=
  fun _ hs => h _ (.l _ _ _ _ hs)

/-- Rocq: `SystemTCL.normal_app_r`. -/
theorem normal_app_r {A : Ty} {M N : Term} (h : Normal (app A M N)) : Normal N :=
  fun _ hs => h _ (.r _ _ _ _ hs)

/-- Rocq: `SystemTCL.closed_normal_value`. -/
theorem closed_normal_value {M : Term} {A : Ty} (h : Typing [] M A) (hn : Normal M) : Value M := by
  induction h with
  | var x A hx => cases x <;> cases hx
  | K => exact .K _ _
  | S => exact .S _ _ _
  | Z => exact .numeral 0
  | Suc => exact .Suc
  | R => exact .R _
  | P => exact .P _ _
  | P1 => exact .Fst _ _
  | P2 => exact .Snd _ _
  | app A B F N hF hN ihF ihN =>
    have vF := ihF (normal_app_l hn)
    have vN := ihN (normal_app_r hn)
    cases vF with
    | numeral n => cases typing_unique hF (typing_num [] n)
    | Suc =>
      cases hF
      obtain ⟨m, rfl⟩ := value_nat vN hN
      exact .numeral (m + 1)
    | K => exact .K1 _ _ _ _
    | K1 => exact (hn _ (.K _ _ _ _ _ _)).elim
    | S => exact .S1 _ _ _ _ _
    | S1 => exact .S2 _ _ _ _ _ _ _
    | S2 => exact (hn _ (.S _ _ _ _ _ _ _ _ _)).elim
    | R =>
      cases hF
      obtain ⟨m, rfl⟩ := value_nat vN hN
      exact .R1 _ _ _
    | R1 => exact .R2 _ _ _ _ _
    | R2 _ _ _ n =>
      cases n with
      | zero => exact (hn _ (.R0 _ _ _ _ _ _ _ (isNum_num 0))).elim
      | succ n => exact (hn _ (.RS _ _ _ _ _ _ _ _ (isNum_num (n + 1)))).elim
    | P => exact .P1 _ _ _ _
    | P1 => exact .P2 _ _ _ _ _ _
    | P2 => obtain ⟨h, _⟩ := typing_app hF; obtain ⟨h, _⟩ := typing_app h; cases h
    | Fst =>
      cases hF
      obtain ⟨Y, X, C, D, a, b, rfl⟩ := value_pair vN hN
      exact (hn _ (.P1 _ _ _ _ _ _ _ _ _)).elim
    | Snd =>
      cases hF
      obtain ⟨Y, X, C, D, a, b, rfl⟩ := value_pair vN hN
      exact (hn _ (.P2 _ _ _ _ _ _ _ _ _)).elim

theorem num_inj' {n m : Nat} (h : num n = num m) : n = m := by
  have h' := congrArg isNum h
  rw [isNum_num, isNum_num] at h'
  exact Option.some.inj h'

/-- Every closed term of type `N` reduces to a unique numeral. Rocq: `SystemTCL.T_value`. -/
theorem T_value {M : Term} (h : Typing [] M TN) : ∃ n, Star M (num n) ∧ ∀ m, Star M (num m) → m = n := by
  obtain ⟨N, hMN, hN⟩ := SN_normal_form (typed_SN h)
  have hNt := star_typing hMN h
  obtain ⟨n, rfl⟩ := value_nat (closed_normal_value hNt hN) hNt
  refine ⟨n, hMN, fun m hm => ?_⟩
  obtain ⟨P, hP1, hP2⟩ := confluence hMN hm
  have e1 := star_normal (fun _ hs => num_normal n _ hs) hP1
  have e2 := star_normal (fun _ hs => num_normal m _ hs) hP2
  exact num_inj' (e2.symm.trans e1)

end ConstructiveOrdinals.SystemTCL
