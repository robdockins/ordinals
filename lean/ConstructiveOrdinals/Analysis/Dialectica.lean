import ConstructiveOrdinals.Analysis.SystemTCL
import ConstructiveOrdinals.Analysis.PeanoArith

/-!
# Consistency of Peano arithmetic by Gödel's Dialectica interpretation

Port of `Ordinal/Analysis/Dialectica.v`.

Gödel's functional interpretation carries Heyting arithmetic into the
quantifier-free theory of the functionals of System T: from a proof of `A` it
extracts a term `t` such that the quantifier-free matrix `A_D(t, y)` holds for
every `y`. With the negative translation (`PeanoArith`), a proof of `⊥` in
Peano arithmetic would give a closed term making `⊥_D` true, which is
impossible.

The interpretation targets combinatory T with pairs (`SystemTCL`). The
quantifier-free matrices are terms of type `N`, read as true when they reduce
to `0`, and their variables range over closed terms of the right types. What
makes this work is `T_value`: every closed term of type `N` has a unique
numeral value, which decides the matrices (needed for contraction) and drives
the recursor in the induction rule. `T_value` rests on strong normalization,
which `SystemTCL` proves by an ordinal assignment below ε₀.

The predicate variable `X` of `PeanoArith` is read as the empty set: its
atoms are interpreted like `⊥`.

Lean notes:

- Rocq's `nth` with a default is `nthD`, and `Forall2` is `Forall2`, both
  defined here: the core list lemmas use `propext`.
- Matches spell out every constructor instead of using a wildcard, which
  would make the definitions depend on `propext`.
-/

namespace ConstructiveOrdinals.Dialectica

open SystemTCL PeanoArith Ty Term

/-! ## Arithmetic and list helpers -/

theorem add_eq_zero {a : Nat} : ∀ {b : Nat}, a + b = 0 → a = 0 ∧ b = 0
  | 0, h => ⟨h, rfl⟩
  | _ + 1, h => Nat.noConfusion h

theorem sub_self' : ∀ n : Nat, n - n = 0
  | 0 => rfl
  | n + 1 => (Nat.succ_sub_succ n n).trans (sub_self' n)

/-- The `i`th element of a list, or `d`. Rocq: `List.nth`. -/
def nthD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: l, i + 1, d => nthD l i d

/-- Rocq: `List.Forall2`. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → Forall2 R l l' → Forall2 R (a :: l) (b :: l')

theorem Forall2.length_eq {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : Forall2 R l l') : l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg (· + 1) ih

/-! ## Terms with free variables

Terms of T have no binders, so substitution is a plain map over the
variables. -/

/-- Rocq: `Analysis.Dialectica.tsub`. -/
def tsub (ρ : Nat → Term) : Term → Term
  | var i => ρ i
  | app A M N => app A (tsub ρ M) (tsub ρ N)
  | Kc A B => Kc A B
  | Sc A B C => Sc A B C
  | Zc => Zc
  | Suc => Suc
  | Rc C => Rc C
  | Pc A B => Pc A B
  | P1c A B => P1c A B
  | P2c A B => P2c A B

/-- Rocq: `Analysis.Dialectica.tsub_ext`. -/
theorem tsub_ext {ρ ρ' : Nat → Term} (h : ∀ i, ρ i = ρ' i) : ∀ M, tsub ρ M = tsub ρ' M
  | var i => h i
  | app A M N => congrArg₂ (app A) (tsub_ext h M) (tsub_ext h N)
  | Kc _ _ => rfl
  | Sc _ _ _ => rfl
  | Zc => rfl
  | Suc => rfl
  | Rc _ => rfl
  | Pc _ _ => rfl
  | P1c _ _ => rfl
  | P2c _ _ => rfl

/-- Rocq: `Analysis.Dialectica.tsub_comp`. -/
theorem tsub_comp (σ ρ : Nat → Term) : ∀ M, tsub σ (tsub ρ M) = tsub (fun i => tsub σ (ρ i)) M
  | var _ => rfl
  | app A M N => congrArg₂ (app A) (tsub_comp σ ρ M) (tsub_comp σ ρ N)
  | Kc _ _ => rfl
  | Sc _ _ _ => rfl
  | Zc => rfl
  | Suc => rfl
  | Rc _ => rfl
  | Pc _ _ => rfl
  | P1c _ _ => rfl
  | P2c _ _ => rfl

/-- Rocq: `Analysis.Dialectica.tsub_num`. -/
theorem tsub_num (ρ : Nat → Term) : ∀ n, tsub ρ (num n) = num n
  | 0 => rfl
  | n + 1 => congrArg (app TN Suc) (tsub_num ρ n)

/-- Rocq: `Analysis.Dialectica.tsub_id`. -/
theorem tsub_id : ∀ M, tsub var M = M
  | var _ => rfl
  | app A M N => congrArg₂ (app A) (tsub_id M) (tsub_id N)
  | Kc _ _ => rfl
  | Sc _ _ _ => rfl
  | Zc => rfl
  | Suc => rfl
  | Rc _ => rfl
  | Pc _ _ => rfl
  | P1c _ _ => rfl
  | P2c _ _ => rfl

/-- Rocq: `Analysis.Dialectica.prepend`. -/
def prepend {X : Type} : List X → (Nat → X) → Nat → X
  | [], f, i => f i
  | a :: _, _, 0 => a
  | _ :: l, f, i + 1 => prepend l f i

/-- Rocq: `Analysis.Dialectica.prepend_lt`. -/
theorem prepend_lt {X : Type} : ∀ (l : List X) (f : Nat → X) (i : Nat) (d : X),
    i < l.length → prepend l f i = nthD l i d
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: l, f, i + 1, d, h => prepend_lt l f i d (Nat.lt_of_succ_lt_succ h)

/-- Rocq: `Analysis.Dialectica.prepend_ge`. -/
theorem prepend_ge {X : Type} : ∀ (l : List X) (f : Nat → X) (j : Nat), prepend l f (l.length + j) = f j
  | [], _, j => congrArg _ (Nat.zero_add j)
  | _ :: l, f, j => by
    show prepend (_ :: l) f (l.length + 1 + j) = f j
    rw [Nat.add_right_comm]
    exact prepend_ge l f j

/-- Rocq: `Analysis.Dialectica.prepend_ge'`. -/
theorem prepend_ge' {X : Type} (l : List X) (f : Nat → X) (i : Nat) (h : l.length ≤ i) :
    prepend l f i = f (i - l.length) := by
  have e : l.length + (i - l.length) = i := by
    rw [Nat.add_comm]; exact Nat.sub_add_cancel h
  have := prepend_ge l f (i - l.length)
  rw [e] at this
  exact this

/-- Rocq: `Analysis.Dialectica.prepend_app`. -/
theorem prepend_app {X : Type} : ∀ (l1 l2 : List X) (f : Nat → X) (i : Nat),
    prepend (l1 ++ l2) f i = prepend l1 (prepend l2 f) i
  | [], _, _, _ => rfl
  | _ :: _, _, _, 0 => rfl
  | _ :: l1, l2, f, i + 1 => prepend_app l1 l2 f i

/-- Typing with a context that assigns a type to every variable.
Rocq: `Analysis.Dialectica.wt`. -/
inductive Wt (Γ : Nat → Ty) : Term → Ty → Prop where
  | var (i : Nat) : Wt Γ (var i) (Γ i)
  | K (A B : Ty) : Wt Γ (Kc A B) (TAr A (TAr B A))
  | S (A B C : Ty) : Wt Γ (Sc A B C) (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
  | Z : Wt Γ Zc TN
  | Suc : Wt Γ Suc (TAr TN TN)
  | R (C : Ty) : Wt Γ (Rc C) (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
  | P (A B : Ty) : Wt Γ (Pc A B) (TAr A (TAr B (TPr A B)))
  | P1 (A B : Ty) : Wt Γ (P1c A B) (TAr (TPr A B) A)
  | P2 (A B : Ty) : Wt Γ (P2c A B) (TAr (TPr A B) B)
  | app (A B : Ty) (M N : Term) : Wt Γ M (TAr A B) → Wt Γ N A → Wt Γ (app A M N) B

/-- Rocq: `Analysis.Dialectica.wt_var'`. -/
theorem wt_var' {Γ : Nat → Ty} {i : Nat} {A : Ty} (h : Γ i = A) : Wt Γ (var i) A := h ▸ .var i

/-- Rocq: `Analysis.Dialectica.wt_tsub`. -/
theorem wt_tsub {Γ Δ : Nat → Ty} {ρ : Nat → Term} {M : Term} {A : Ty} (h : Wt Γ M A)
    (hρ : ∀ i, Wt Δ (ρ i) (Γ i)) : Wt Δ (tsub ρ M) A := by
  induction h with
  | var i => exact hρ i
  | K => exact .K _ _
  | S => exact .S _ _ _
  | Z => exact .Z
  | Suc => exact .Suc
  | R => exact .R _
  | P => exact .P _ _
  | P1 => exact .P1 _ _
  | P2 => exact .P2 _ _
  | app _ _ _ _ _ _ ih1 ih2 => exact .app _ _ _ _ ih1 ih2

/-- Rocq: `Analysis.Dialectica.wt_typing`. -/
theorem wt_typing {Γ : Nat → Ty} {ρ : Nat → Term} {M : Term} {A : Ty} (h : Wt Γ M A)
    (hρ : ∀ i, Typing [] (ρ i) (Γ i)) : Typing [] (tsub ρ M) A := by
  induction h with
  | var i => exact hρ i
  | K => exact .K _ _
  | S => exact .S _ _ _
  | Z => exact .Z
  | Suc => exact .Suc
  | R => exact .R _
  | P => exact .P _ _
  | P1 => exact .P1 _ _
  | P2 => exact .P2 _ _
  | app _ _ _ _ _ _ ih1 ih2 => exact .app _ _ _ _ ih1 ih2

/-- Rocq: `Analysis.Dialectica.typing_wt`. -/
theorem typing_wt {M : Term} {A : Ty} (h : Typing [] M A) (Γ : Nat → Ty) : Wt Γ M A := by
  induction h with
  | var x _ hx => cases x <;> cases hx
  | K => exact .K _ _
  | S => exact .S _ _ _
  | Z => exact .Z
  | Suc => exact .Suc
  | R => exact .R _
  | P => exact .P _ _
  | P1 => exact .P1 _ _
  | P2 => exact .P2 _ _
  | app _ _ _ _ _ _ ih1 ih2 => exact .app _ _ _ _ ih1 ih2

/-- Rocq: `Analysis.Dialectica.typing_closed`. -/
theorem typing_closed {M : Term} {A : Ty} (h : Typing [] M A) (ρ : Nat → Term) : tsub ρ M = M := by
  induction h with
  | var x _ hx => cases x <;> cases hx
  | app _ _ _ _ _ _ ih1 ih2 => exact congrArg₂ (app _) ih1 ih2
  | _ => rfl

/-- Rocq: `Analysis.Dialectica.prepend_typing`. -/
theorem prepend_typing {xs : List Term} {Ts : List Ty} {ns : Nat → Term} {f : Nat → Ty}
    (h : Forall2 (fun x T => Typing [] x T) xs Ts) (hn : ∀ j, Typing [] (ns j) (f j)) :
    ∀ i, Typing [] (prepend xs ns i) (prepend Ts f i) := by
  induction h with
  | nil => exact hn
  | cons hx _ ih =>
    intro i
    cases i with
    | zero => exact hx
    | succ i => exact ih i

/-! ## Bracket abstraction -/

/-- Rocq: `Analysis.Dialectica.infer`. -/
def infer (Γ : Nat → Ty) : Term → Option Ty
  | var i => some (Γ i)
  | Kc A B => some (TAr A (TAr B A))
  | Sc A B C => some (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
  | Zc => some TN
  | Suc => some (TAr TN TN)
  | Rc C => some (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
  | Pc A B => some (TAr A (TAr B (TPr A B)))
  | P1c A B => some (TAr (TPr A B) A)
  | P2c A B => some (TAr (TPr A B) B)
  | app _ M _ =>
    match infer Γ M with
    | some (TAr _ B) => some B
    | some TN => none
    | some (TPr _ _) => none
    | none => none

/-- Rocq: `Analysis.Dialectica.infer_wt`. -/
theorem infer_wt {Γ : Nat → Ty} {M : Term} {A : Ty} (h : Wt Γ M A) : infer Γ M = some A := by
  induction h with
  | app _ _ M _ _ _ ih _ =>
    show (match infer Γ M with
      | some (TAr _ B) => some B
      | some TN => none
      | some (TPr _ _) => none
      | none => none) = _
    rw [ih]
  | _ => rfl

/-- Rocq: `Analysis.Dialectica.tyof`. -/
def tyof (Γ : Nat → Ty) (M : Term) : Ty :=
  match infer Γ M with
  | some A => A
  | none => TN

/-- `Kt T A M = λ_:A. M`. Rocq: `Analysis.Dialectica.Kt`. -/
def Kt (T A : Ty) (M : Term) : Term := app T (Kc T A) M

/-- The identity. Rocq: `Analysis.Dialectica.It`. -/
def It (A : Ty) : Term :=
  app (TAr A (TAr A A)) (app (TAr A (TAr (TAr A A) A)) (Sc A (TAr A A) A) (Kc A (TAr A A))) (Kc A A)

/-- Rocq: `Analysis.Dialectica.rem`. -/
def rem (j : Nat) (Γ : Nat → Ty) : Nat → Ty := fun i => if i < j then Γ i else Γ (i + 1)

/-- Rocq: `Analysis.Dialectica.ins`. -/
def ins {X : Type} (j : Nat) (a : X) (f : Nat → X) : Nat → X :=
  fun i => if i < j then f i else if i = j then a else f (Nat.pred i)

/-- `lamAt Γ j M` abstracts the variable `j` of `M`. Rocq: `Analysis.Dialectica.lam_at`. -/
def lamAt (Γ : Nat → Ty) (j : Nat) : Term → Term
  | var i => if i = j then It (Γ j) else Kt (Γ i) (Γ j) (var (if i < j then i else Nat.pred i))
  | app B P Q =>
    app (TAr (Γ j) B) (app (TAr (Γ j) (TAr B (tyof Γ (app B P Q)))) (Sc (Γ j) B (tyof Γ (app B P Q)))
      (lamAt Γ j P)) (lamAt Γ j Q)
  | Kc A B => Kt (tyof Γ (Kc A B)) (Γ j) (Kc A B)
  | Sc A B C => Kt (tyof Γ (Sc A B C)) (Γ j) (Sc A B C)
  | Zc => Kt (tyof Γ Zc) (Γ j) Zc
  | Suc => Kt (tyof Γ Suc) (Γ j) Suc
  | Rc C => Kt (tyof Γ (Rc C)) (Γ j) (Rc C)
  | Pc A B => Kt (tyof Γ (Pc A B)) (Γ j) (Pc A B)
  | P1c A B => Kt (tyof Γ (P1c A B)) (Γ j) (P1c A B)
  | P2c A B => Kt (tyof Γ (P2c A B)) (Γ j) (P2c A B)

/-- Rocq: `Analysis.Dialectica.wt_It`. -/
theorem wt_It (Γ : Nat → Ty) (A : Ty) : Wt Γ (It A) (TAr A A) :=
  .app _ _ _ _ (.app _ _ _ _ (.S _ _ _) (.K _ _)) (.K _ _)

/-- Rocq: `Analysis.Dialectica.wt_Kt`. -/
theorem wt_Kt {Γ : Nat → Ty} {T : Ty} (A : Ty) {M : Term} (h : Wt Γ M T) : Wt Γ (Kt T A M) (TAr A T) :=
  .app _ _ _ _ (.K _ _) h

/-- Rocq: `Analysis.Dialectica.wt_lam_at`. -/
theorem wt_lam_at {Γ : Nat → Ty} (j : Nat) {M : Term} {T : Ty} (h : Wt Γ M T) :
    Wt (rem j Γ) (lamAt Γ j M) (TAr (Γ j) T) := by
  induction h with
  | var i =>
    show Wt _ (if i = j then It (Γ j) else Kt (Γ i) (Γ j) (var (if i < j then i else Nat.pred i))) _
    by_cases hij : i = j
    · rw [ite_eq_left hij]; subst hij; exact wt_It _ _
    · rw [ite_eq_right hij]
      refine wt_Kt _ (wt_var' ?_)
      by_cases hlt : i < j
      · rw [ite_eq_left hlt]; exact ite_eq_left hlt
      · rw [ite_eq_right hlt]
        cases i with
        | zero => exact absurd (Nat.lt_of_le_of_ne (Nat.zero_le j) hij) hlt
        | succ i =>
          exact ite_eq_right (fun h => hlt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h) hij))
  | K A B => exact wt_Kt _ (.K _ _)
  | S A B C => exact wt_Kt _ (.S _ _ _)
  | Z => exact wt_Kt _ .Z
  | Suc => exact wt_Kt _ .Suc
  | R C => exact wt_Kt _ (.R _)
  | P A B => exact wt_Kt _ (.P _ _)
  | P1 A B => exact wt_Kt _ (.P1 _ _)
  | P2 A B => exact wt_Kt _ (.P2 _ _)
  | app A B M N hM hN ihM ihN =>
    have e : tyof Γ (app A M N) = B := by
      unfold tyof; rw [infer_wt (.app _ _ _ _ hM hN)]
    show Wt _ (app (TAr (Γ j) A) (app (TAr (Γ j) (TAr A (tyof Γ (app A M N))))
      (Sc (Γ j) A (tyof Γ (app A M N))) (lamAt Γ j M)) (lamAt Γ j N)) _
    rw [e]
    exact .app _ _ _ _ (.app _ _ _ _ (.S _ _ _) ihM) ihN

/-- Rocq: `Analysis.Dialectica.star_It`. -/
theorem star_It (X A : Ty) (N : Term) : Star (app X (It A) N) N :=
  .step _ _ _ (.S _ _ _ _ _ _ _ _ _) (.step _ _ _ (.K _ _ _ _ _ _) (.refl _))

/-- Rocq: `Analysis.Dialectica.star_lam_at`. -/
theorem star_lam_at (Γ : Nat → Ty) (j : Nat) : ∀ (M : Term) (ρ : Nat → Term) (X : Ty) (N : Term),
    Star (app X (tsub ρ (lamAt Γ j M)) N) (tsub (ins j N ρ) M)
  | var i, ρ, X, N => by
    by_cases hij : i = j
    · subst hij
      show Star (app X (tsub ρ (if i = i then It (Γ i) else _)) N) (if i < i then ρ i else if i = i then N else _)
      rw [ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl i), ite_eq_left rfl]
      exact star_It _ _ _
    · show Star (app X (tsub ρ (if i = j then It (Γ j) else Kt (Γ i) (Γ j)
          (var (if i < j then i else Nat.pred i)))) N)
        (if i < j then ρ i else if i = j then N else ρ (Nat.pred i))
      rw [ite_eq_right hij, ite_eq_right hij]
      refine .step _ _ _ (.K _ _ _ _ _ _) ?_
      by_cases hlt : i < j
      · rw [ite_eq_left hlt, ite_eq_left hlt]; exact .refl _
      · rw [ite_eq_right hlt, ite_eq_right hlt]; exact .refl _
  | app B P Q, ρ, X, N =>
    .step _ _ _ (.S _ _ _ _ _ _ _ _ _) (star_app _ (star_lam_at Γ j P ρ _ N) (star_lam_at Γ j Q ρ _ N))
  | Kc _ _, _, _, _ => star_one (.K _ _ _ _ _ _)
  | Sc _ _ _, _, _, _ => star_one (.K _ _ _ _ _ _)
  | Zc, _, _, _ => star_one (.K _ _ _ _ _ _)
  | Suc, _, _, _ => star_one (.K _ _ _ _ _ _)
  | Rc _, _, _, _ => star_one (.K _ _ _ _ _ _)
  | Pc _ _, _, _, _ => star_one (.K _ _ _ _ _ _)
  | P1c _ _, _, _, _ => star_one (.K _ _ _ _ _ _)
  | P2c _ _, _, _, _ => star_one (.K _ _ _ _ _ _)

/-- Rocq: `Analysis.Dialectica.star_tsub`. -/
theorem star_tsub {ρ ρ' : Nat → Term} (h : ∀ i, Star (ρ i) (ρ' i)) : ∀ M, Star (tsub ρ M) (tsub ρ' M)
  | var i => h i
  | app _ M N => star_app _ (star_tsub h M) (star_tsub h N)
  | Kc _ _ => .refl _
  | Sc _ _ _ => .refl _
  | Zc => .refl _
  | Suc => .refl _
  | Rc _ => .refl _
  | Pc _ _ => .refl _
  | P1c _ _ => .refl _
  | P2c _ _ => .refl _

/-! ## Evaluation

A closed term of type `N` is read as true when it reduces to `0`. -/

/-- Rocq: `Analysis.Dialectica.holds`. -/
def Holds (M : Term) : Prop := Star M (num 0)

/-- Rocq: `Analysis.Dialectica.num_inj`. -/
theorem num_inj {n m : Nat} (h : num n = num m) : n = m := num_inj' h

/-- Rocq: `Analysis.Dialectica.star_from_num`. -/
theorem star_from_num {n : Nat} {N : Term} (h : Star (num n) N) : N = num n :=
  star_normal (fun _ hs => num_normal n _ hs) h

/-- Rocq: `Analysis.Dialectica.star_num_unique`. -/
theorem star_num_unique {M : Term} {n m : Nat} (h1 : Star M (num n)) (h2 : Star M (num m)) : n = m := by
  obtain ⟨P, hP1, hP2⟩ := confluence h1 h2
  exact num_inj ((star_from_num hP1).symm.trans (star_from_num hP2))

/-- Rocq: `Analysis.Dialectica.evals_star`. -/
theorem evals_star {M M' : Term} {n : Nat} (h : Star M M') : Star M (num n) ↔ Star M' (num n) :=
  ⟨fun hn => by
    obtain ⟨P, hP1, hP2⟩ := confluence h hn
    rw [star_from_num hP2] at hP1
    exact hP1,
   fun hn => star_trans h hn⟩

/-- Rocq: `Analysis.Dialectica.holds_star`. -/
theorem holds_star {M M' : Term} (h : Star M M') : Holds M ↔ Holds M' := evals_star h

/-- Rocq: `Analysis.Dialectica.T_eval`. -/
theorem T_eval {M : Term} (h : Typing [] M TN) : ∃ n, Star M (num n) :=
  let ⟨n, hn, _⟩ := T_value h
  ⟨n, hn⟩

/-- Rocq: `Analysis.Dialectica.holds_dec`. -/
theorem holds_dec {M : Term} (h : Typing [] M TN) : Holds M ∨ ∃ m, Star M (num (m + 1)) :=
  match T_eval h with
  | ⟨0, h0⟩ => .inl h0
  | ⟨m + 1, hm⟩ => .inr ⟨m, hm⟩

/-- Rocq: `Analysis.Dialectica.not_holds`. -/
theorem not_holds {M : Term} {m : Nat} (h : Star M (num (m + 1))) : ¬ Holds M := fun h' =>
  Nat.noConfusion (star_num_unique h h')

/-! ## Pairs, definition by cases and arithmetic -/

/-- Rocq: `Analysis.Dialectica.tpair`. -/
def tpair (A B : Ty) (a b : Term) : Term := app B (app A (Pc A B) a) b
/-- Rocq: `Analysis.Dialectica.pi1`. -/
def pi1 (A B : Ty) (M : Term) : Term := app (TPr A B) (P1c A B) M
/-- Rocq: `Analysis.Dialectica.pi2`. -/
def pi2 (A B : Ty) (M : Term) : Term := app (TPr A B) (P2c A B) M

/-- Rocq: `Analysis.Dialectica.star_pi1`. -/
theorem star_pi1 (A B C D : Ty) (a b : Term) : Star (pi1 A B (tpair C D a b)) a :=
  star_one (.P1 _ _ _ _ _ _ _ _ _)

/-- Rocq: `Analysis.Dialectica.star_pi2`. -/
theorem star_pi2 (A B C D : Ty) (a b : Term) : Star (pi2 A B (tpair C D a b)) b :=
  star_one (.P2 _ _ _ _ _ _ _ _ _)

/-- Rocq: `Analysis.Dialectica.star_pi1'`. -/
theorem star_pi1' (A B : Ty) {M a b : Term} {C D : Ty} (h : Star M (tpair C D a b)) :
    Star (pi1 A B M) a :=
  star_trans (star_app_r _ _ h) (star_pi1 _ _ _ _ _ _)

/-- Rocq: `Analysis.Dialectica.star_pi2'`. -/
theorem star_pi2' (A B : Ty) {M a b : Term} {C D : Ty} (h : Star M (tpair C D a b)) :
    Star (pi2 A B M) b :=
  star_trans (star_app_r _ _ h) (star_pi2 _ _ _ _ _ _)

/-- Rocq: `Analysis.Dialectica.wt_tpair`. -/
theorem wt_tpair {Γ : Nat → Ty} {A B : Ty} {a b : Term} (ha : Wt Γ a A) (hb : Wt Γ b B) :
    Wt Γ (tpair A B a b) (TPr A B) :=
  .app _ _ _ _ (.app _ _ _ _ (.P _ _) ha) hb

/-- Rocq: `Analysis.Dialectica.wt_pi1`. -/
theorem wt_pi1 {Γ : Nat → Ty} {A B : Ty} {M : Term} (h : Wt Γ M (TPr A B)) : Wt Γ (pi1 A B M) A :=
  .app _ _ _ _ (.P1 _ _) h

/-- Rocq: `Analysis.Dialectica.wt_pi2`. -/
theorem wt_pi2 {Γ : Nat → Ty} {A B : Ty} {M : Term} (h : Wt Γ M (TPr A B)) : Wt Γ (pi2 A B M) B :=
  .app _ _ _ _ (.P2 _ _) h

/-- `cond σ z a b` is `a` if `z = 0`, and `b` otherwise. Rocq: `Analysis.Dialectica.cond`. -/
def cond (σ : Ty) (z a b : Term) : Term :=
  app (TAr TN (TAr σ σ)) (app σ (app TN (Rc σ) z) a) (Kt (TAr σ σ) TN (Kt σ σ b))

/-- Rocq: `Analysis.Dialectica.wt_cond`. -/
theorem wt_cond {Γ : Nat → Ty} {σ : Ty} {z a b : Term} (hz : Wt Γ z TN) (ha : Wt Γ a σ) (hb : Wt Γ b σ) :
    Wt Γ (cond σ z a b) σ :=
  .app _ _ _ _ (.app _ _ _ _ (.app _ _ _ _ (.R _) hz) ha) (wt_Kt _ (wt_Kt _ hb))

/-- Rocq: `Analysis.Dialectica.cond_0`. -/
theorem cond_0 (σ : Ty) {z : Term} (a b : Term) (h : Star z (num 0)) : Star (cond σ z a b) a :=
  star_trans (star_app_l _ _ (star_app_l _ _ (star_app_r _ _ h))) (star_one (.R0 _ _ _ _ _ _ _ rfl))

/-- Rocq: `Analysis.Dialectica.cond_S`. -/
theorem cond_S (σ : Ty) {z : Term} (a b : Term) {m : Nat} (h : Star z (num (m + 1))) :
    Star (cond σ z a b) b :=
  star_trans (star_app_l _ _ (star_app_l _ _ (star_app_r _ _ h)))
    (.step _ _ _ (.RS _ _ _ _ _ _ _ _ (isNum_num (m + 1)))
      (.step _ _ _ (.l _ _ _ _ (.K _ _ _ _ _ _)) (.step _ _ _ (.K _ _ _ _ _ _) (.refl _))))

/-- Rocq: `Analysis.Dialectica.recN`. -/
def recN (y x g : Term) : Term := app (TAr TN (TAr TN TN)) (app TN (app TN (Rc TN) y) x) g

/-- Rocq: `Analysis.Dialectica.wt_recN`. -/
theorem wt_recN {Γ : Nat → Ty} {y x g : Term} (hy : Wt Γ y TN) (hx : Wt Γ x TN)
    (hg : Wt Γ g (TAr TN (TAr TN TN))) : Wt Γ (recN y x g) TN :=
  .app _ _ _ _ (.app _ _ _ _ (.app _ _ _ _ (.R _) hy) hx) hg

/-- Rocq: `Analysis.Dialectica.recN_star`. -/
theorem recN_star {y y' x x' : Term} (g : Term) (hy : Star y y') (hx : Star x x') :
    Star (recN y x g) (recN y' x' g) :=
  star_app_l _ _ (star_app _ (star_app_r _ _ hy) hx)

/-- Rocq: `Analysis.Dialectica.recN_0`. -/
theorem recN_0 (x g : Term) : Star (recN (num 0) x g) x := star_one (.R0 _ _ _ _ _ _ _ rfl)

/-- Rocq: `Analysis.Dialectica.recN_S`. -/
theorem recN_S (n : Nat) (x f : Term) :
    Star (recN (num (n + 1)) x (Kt (TAr TN TN) TN f)) (app TN f (recN (num n) x (Kt (TAr TN TN) TN f))) :=
  .step _ _ _ (.RS _ _ _ _ _ _ _ _ (isNum_num (n + 1))) (.step _ _ _ (.l _ _ _ _ (.K _ _ _ _ _ _)) (.refl _))

/-- Rocq: `Analysis.Dialectica.addT`. -/
def addT (x y : Term) : Term := recN y x (Kt (TAr TN TN) TN Suc)

/-- Rocq: `Analysis.Dialectica.TN0`. -/
def TN0 : Nat → Ty := fun _ => TN

/-- `ADDR x w = w + x`. Rocq: `Analysis.Dialectica.ADDR`. -/
def ADDR : Term := lamAt TN0 0 (lamAt TN0 0 (addT (var 0) (var 1)))
/-- Rocq: `Analysis.Dialectica.predT`. -/
def predT (n : Term) : Term := recN n Zc (Kc TN TN)
/-- `PREDF n = n - 1`. Rocq: `Analysis.Dialectica.PREDF`. -/
def PREDF : Term := lamAt TN0 0 (predT (var 0))

/-- Rocq: `Analysis.Dialectica.mulT`. -/
def mulT (x y : Term) : Term := recN y Zc (Kt (TAr TN TN) TN (app TN ADDR x))
/-- Rocq: `Analysis.Dialectica.subT`. -/
def subT (x y : Term) : Term := recN y x (Kt (TAr TN TN) TN PREDF)
/-- Rocq: `Analysis.Dialectica.eqT`. -/
def eqT (x y : Term) : Term := addT (subT x y) (subT y x)

/-- Rocq: `Analysis.Dialectica.wt_addT`. -/
theorem wt_addT {Γ : Nat → Ty} {x y : Term} (hx : Wt Γ x TN) (hy : Wt Γ y TN) : Wt Γ (addT x y) TN :=
  wt_recN hy hx (wt_Kt _ .Suc)

/-- Rocq: `Analysis.Dialectica.wt_ext`. -/
theorem wt_ext {Γ Δ : Nat → Ty} (E : ∀ i, Γ i = Δ i) {M : Term} {A : Ty} (h : Wt Γ M A) : Wt Δ M A := by
  induction h with
  | var i => exact wt_var' (E i).symm
  | K => exact .K _ _
  | S => exact .S _ _ _
  | Z => exact .Z
  | Suc => exact .Suc
  | R => exact .R _
  | P => exact .P _ _
  | P1 => exact .P1 _ _
  | P2 => exact .P2 _ _
  | app _ _ _ _ _ _ ih1 ih2 => exact .app _ _ _ _ ih1 ih2

/-- Closed terms typed in `TN0` are typed everywhere. Rocq: `Analysis.Dialectica.wt_TN0_closed`. -/
theorem wt_TN0_closed (Γ : Nat → Ty) {M : Term} {A : Ty} (h : Wt TN0 M A)
    (hc : ∀ ρ, tsub ρ M = M) : Wt Γ M A := by
  rw [← hc (fun _ => Zc)]
  exact typing_wt (wt_typing h (fun _ => .Z)) Γ

/-- Rocq: `Analysis.Dialectica.wt_ADDR`. -/
theorem wt_ADDR (Γ : Nat → Ty) : Wt Γ ADDR (TAr TN (TAr TN TN)) :=
  have h1 : Wt TN0 (addT (var 0) (var 1)) TN := wt_addT (wt_var' rfl) (wt_var' rfl)
  have h2 : Wt TN0 (lamAt TN0 0 (addT (var 0) (var 1))) (TAr TN TN) :=
    wt_ext (Γ := rem 0 TN0) (fun _ => rfl) (wt_lam_at 0 h1)
  wt_TN0_closed Γ (wt_ext (Γ := rem 0 TN0) (fun _ => rfl) (wt_lam_at 0 h2)) (fun _ => rfl)

/-- Rocq: `Analysis.Dialectica.wt_predT`. -/
theorem wt_predT {Γ : Nat → Ty} {n : Term} (h : Wt Γ n TN) : Wt Γ (predT n) TN :=
  wt_recN h .Z (.K _ _)

/-- Rocq: `Analysis.Dialectica.wt_PREDF`. -/
theorem wt_PREDF (Γ : Nat → Ty) : Wt Γ PREDF (TAr TN TN) :=
  have h1 : Wt TN0 (predT (var 0)) TN := wt_predT (wt_var' rfl)
  wt_TN0_closed Γ (wt_ext (Γ := rem 0 TN0) (fun _ => rfl) (wt_lam_at 0 h1)) (fun _ => rfl)

/-- Rocq: `Analysis.Dialectica.wt_mulT`. -/
theorem wt_mulT {Γ : Nat → Ty} {x y : Term} (hx : Wt Γ x TN) (hy : Wt Γ y TN) : Wt Γ (mulT x y) TN :=
  wt_recN hy .Z (wt_Kt _ (.app _ _ _ _ (wt_ADDR Γ) hx))

/-- Rocq: `Analysis.Dialectica.wt_subT`. -/
theorem wt_subT {Γ : Nat → Ty} {x y : Term} (hx : Wt Γ x TN) (hy : Wt Γ y TN) : Wt Γ (subT x y) TN :=
  wt_recN hy hx (wt_Kt _ (wt_PREDF Γ))

/-- Rocq: `Analysis.Dialectica.wt_eqT`. -/
theorem wt_eqT {Γ : Nat → Ty} {x y : Term} (hx : Wt Γ x TN) (hy : Wt Γ y TN) : Wt Γ (eqT x y) TN :=
  wt_addT (wt_subT hx hy) (wt_subT hy hx)

/-! Their values. -/

/-- Rocq: `Analysis.Dialectica.addT_num`. -/
theorem addT_num (m : Nat) : ∀ k, Star (addT (num m) (num k)) (num (m + k))
  | 0 => recN_0 _ _
  | k + 1 => star_trans (recN_S _ _ _) (star_app_r _ _ (addT_num m k))

/-- Rocq: `Analysis.Dialectica.addT_eval`. -/
theorem addT_eval {x y : Term} {m k : Nat} (hx : Star x (num m)) (hy : Star y (num k)) :
    Star (addT x y) (num (m + k)) :=
  star_trans (recN_star _ hy hx) (addT_num m k)

/-- Rocq: `Analysis.Dialectica.ADDR_eval`. -/
theorem ADDR_eval (X Y : Ty) (x w : Term) : Star (app X (app Y ADDR x) w) (addT w x) := by
  rw [← tsub_id ADDR]
  exact star_trans (star_app_l _ _ (star_lam_at TN0 0 _ var Y x))
    (star_lam_at TN0 0 (addT (var 0) (var 1)) (ins 0 x var) X w)

/-- Rocq: `Analysis.Dialectica.mulT_num`. -/
theorem mulT_num (m : Nat) : ∀ k, Star (mulT (num m) (num k)) (num (m * k))
  | 0 => recN_0 _ _
  | k + 1 => star_trans (recN_S _ _ _) (star_trans (ADDR_eval _ _ _ _)
      (addT_eval (mulT_num m k) (.refl _)))

/-- Rocq: `Analysis.Dialectica.mulT_eval`. -/
theorem mulT_eval {x y : Term} {m k : Nat} (hx : Star x (num m)) (hy : Star y (num k)) :
    Star (mulT x y) (num (m * k)) :=
  star_trans (recN_star _ hy (.refl _))
    (star_trans (star_app_r _ _ (star_app_r _ _ (star_app_r _ _ hx))) (mulT_num m k))

/-- Rocq: `Analysis.Dialectica.predT_num`. -/
theorem predT_num : ∀ n, Star (predT (num n)) (num (Nat.pred n))
  | 0 => recN_0 _ _
  | n + 1 => .step _ _ _ (.RS _ _ _ _ _ _ _ _ (isNum_num (n + 1))) (.step _ _ _ (.K _ _ _ _ _ _) (.refl _))

/-- Rocq: `Analysis.Dialectica.PREDF_eval`. -/
theorem PREDF_eval (X : Ty) {x : Term} {n : Nat} (h : Star x (num n)) :
    Star (app X PREDF x) (num (Nat.pred n)) := by
  rw [← tsub_id PREDF]
  exact star_trans (star_lam_at TN0 0 (predT (var 0)) var X x)
    (star_trans (recN_star _ h (.refl _)) (predT_num n))

/-- Rocq: `Analysis.Dialectica.subT_num`. -/
theorem subT_num (m : Nat) : ∀ k, Star (subT (num m) (num k)) (num (m - k))
  | 0 => recN_0 _ _
  | k + 1 => by
    rw [Nat.sub_succ]
    exact star_trans (recN_S _ _ _) (PREDF_eval _ (subT_num m k))

/-- Rocq: `Analysis.Dialectica.subT_eval`. -/
theorem subT_eval {x y : Term} {m k : Nat} (hx : Star x (num m)) (hy : Star y (num k)) :
    Star (subT x y) (num (m - k)) :=
  star_trans (recN_star _ hy hx) (subT_num m k)

/-- Rocq: `Analysis.Dialectica.eqT_eval`. -/
theorem eqT_eval {x y : Term} {m k : Nat} (hx : Star x (num m)) (hy : Star y (num k)) :
    ∃ d, Star (eqT x y) (num d) ∧ (d = 0 ↔ m = k) :=
  ⟨(m - k) + (k - m), addT_eval (subT_eval hx hy) (subT_eval hy hx),
    fun h =>
      let ⟨h1, h2⟩ := add_eq_zero h
      Nat.le_antisymm (le_of_sub_eq_zero' h1) (le_of_sub_eq_zero' h2),
    fun h => by subst h; rw [sub_self']⟩

/-- Arithmetic terms as terms of T. Rocq: `Analysis.Dialectica.tr`. -/
def tr : ATerm → Term
  | .tv i => var i
  | .tz => Zc
  | .ts t => app TN Suc (tr t)
  | .tplus a b => addT (tr a) (tr b)
  | .tmult a b => mulT (tr a) (tr b)

/-- Rocq: `Analysis.Dialectica.tsub_addT`. -/
theorem tsub_addT (ρ : Nat → Term) (x y : Term) : tsub ρ (addT x y) = addT (tsub ρ x) (tsub ρ y) := rfl

/-- Rocq: `Analysis.Dialectica.tsub_mulT`. -/
theorem tsub_mulT (ρ : Nat → Term) (x y : Term) : tsub ρ (mulT x y) = mulT (tsub ρ x) (tsub ρ y) := rfl

/-- Rocq: `Analysis.Dialectica.tsub_eqT`. -/
theorem tsub_eqT (ρ : Nat → Term) (x y : Term) : tsub ρ (eqT x y) = eqT (tsub ρ x) (tsub ρ y) := rfl

/-- Rocq: `Analysis.Dialectica.tsub_cond`. -/
theorem tsub_cond (ρ : Nat → Term) (σ : Ty) (z a b : Term) :
    tsub ρ (cond σ z a b) = cond σ (tsub ρ z) (tsub ρ a) (tsub ρ b) := rfl

/-- Rocq: `Analysis.Dialectica.tr_asubst`. -/
theorem tr_asubst (σ : Nat → ATerm) : ∀ t, tr (asubst σ t) = tsub (fun i => tr (σ i)) (tr t)
  | .tv _ => rfl
  | .tz => rfl
  | .ts t => congrArg (app TN Suc) (tr_asubst σ t)
  | .tplus a b => congrArg₂ addT (tr_asubst σ a) (tr_asubst σ b)
  | .tmult a b => congrArg₂ mulT (tr_asubst σ a) (tr_asubst σ b)

/-- Rocq: `Analysis.Dialectica.wt_tr`. -/
theorem wt_tr {Γ : Nat → Ty} (h : ∀ i, Γ i = TN) : ∀ t, Wt Γ (tr t) TN
  | .tv i => wt_var' (h i)
  | .tz => .Z
  | .ts t => .app _ _ _ _ .Suc (wt_tr h t)
  | .tplus a b => wt_addT (wt_tr h a) (wt_tr h b)
  | .tmult a b => wt_mulT (wt_tr h a) (wt_tr h b)

/-- Rocq: `Analysis.Dialectica.Ns`. -/
def Ns (ns : Nat → Term) : Prop := ∀ j, Typing [] (ns j) TN

/-- Rocq: `Analysis.Dialectica.typing_tr`. -/
theorem typing_tr {ns : Nat → Term} (t : ATerm) (h : Ns ns) : Typing [] (tsub ns (tr t)) TN :=
  wt_typing (Γ := TN0) (wt_tr (fun _ => rfl) t) h

/-! ## The Dialectica interpretation

`wty A` is the type of witnesses of `A`, `cty A` the type of its
counterexamples, and `dia A` the quantifier-free matrix `A_D`: a term of type
`N` whose variable `0` is the counterexample, variable `1` the witness, and
variables `2 + j` the free number variables of `A`. -/

mutual
/-- Rocq: `Analysis.Dialectica.wty`. -/
def wty : Form → Ty
  | .eq _ _ => TN
  | .bot => TN
  | .conj A B => TPr (wty A) (wty B)
  | .disj A B => TPr TN (TPr (wty A) (wty B))
  | .imp A B => TPr (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A)))
  | .all A => TAr TN (wty A)
  | .ex A => TPr TN (wty A)
  | .px _ => TN
/-- Rocq: `Analysis.Dialectica.cty`. -/
def cty : Form → Ty
  | .eq _ _ => TN
  | .bot => TN
  | .conj A B => TPr (cty A) (cty B)
  | .disj A B => TPr (cty A) (cty B)
  | .imp A B => TPr (wty A) (cty B)
  | .all A => TPr TN (cty A)
  | .ex A => cty A
  | .px _ => TN
end

/-- Rocq: `Analysis.Dialectica.wty_cty_subst`. -/
theorem wty_cty_subst : ∀ (A : Form) (σ : Nat → ATerm), wty (fsubst σ A) = wty A ∧ cty (fsubst σ A) = cty A
  | .eq _ _, _ => ⟨rfl, rfl⟩
  | .bot, _ => ⟨rfl, rfl⟩
  | .conj A B, σ => by
    show TPr _ _ = _ ∧ TPr _ _ = _
    rw [(wty_cty_subst A σ).1, (wty_cty_subst A σ).2, (wty_cty_subst B σ).1, (wty_cty_subst B σ).2]
    exact ⟨rfl, rfl⟩
  | .disj A B, σ => by
    show TPr _ _ = _ ∧ TPr _ _ = _
    rw [(wty_cty_subst A σ).1, (wty_cty_subst A σ).2, (wty_cty_subst B σ).1, (wty_cty_subst B σ).2]
    exact ⟨rfl, rfl⟩
  | .imp A B, σ => by
    show TPr _ _ = _ ∧ TPr _ _ = _
    rw [(wty_cty_subst A σ).1, (wty_cty_subst A σ).2, (wty_cty_subst B σ).1, (wty_cty_subst B σ).2]
    exact ⟨rfl, rfl⟩
  | .all A, σ => by
    show TAr _ _ = _ ∧ TPr _ _ = _
    rw [(wty_cty_subst A (up σ)).1, (wty_cty_subst A (up σ)).2]
    exact ⟨rfl, rfl⟩
  | .ex A, σ => by
    show TPr _ _ = _ ∧ _ = _
    rw [(wty_cty_subst A (up σ)).1]
    exact ⟨rfl, (wty_cty_subst A (up σ)).2⟩
  | .px _, _ => ⟨rfl, rfl⟩

/-- Rocq: `Analysis.Dialectica.wty_subst`. -/
theorem wty_subst (A : Form) (σ : Nat → ATerm) : wty (fsubst σ A) = wty A := (wty_cty_subst A σ).1

/-- Rocq: `Analysis.Dialectica.cty_subst`. -/
theorem cty_subst (A : Form) (σ : Nat → ATerm) : cty (fsubst σ A) = cty A := (wty_cty_subst A σ).2

/-- Rocq: `Analysis.Dialectica.dsub`. -/
def dsub {X : Type} (y x : X) (f : Nat → X) : Nat → X
  | 0 => y
  | 1 => x
  | j + 2 => f j

/-- Rocq: `Analysis.Dialectica.nvars`. -/
def nvars : Nat → Term := fun j => var (j + 2)

/-- Rocq: `Analysis.Dialectica.dia`. -/
def dia : Form → Term
  | .eq s t => eqT (tsub nvars (tr s)) (tsub nvars (tr t))
  | .bot => num 1
  | .conj A B =>
    addT (tsub (dsub (pi1 (cty A) (cty B) (var 0)) (pi1 (wty A) (wty B) (var 1)) nvars) (dia A))
      (tsub (dsub (pi2 (cty A) (cty B) (var 0)) (pi2 (wty A) (wty B) (var 1)) nvars) (dia B))
  | .disj A B =>
    cond TN (pi1 TN (TPr (wty A) (wty B)) (var 1))
      (tsub (dsub (pi1 (cty A) (cty B) (var 0))
        (pi1 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) (var 1))) nvars) (dia A))
      (tsub (dsub (pi2 (cty A) (cty B) (var 0))
        (pi2 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) (var 1))) nvars) (dia B))
  | .imp A B =>
    cond TN
      (tsub (dsub (app (cty B) (app (wty A)
          (pi2 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) (var 1))
          (pi1 (wty A) (cty B) (var 0))) (pi2 (wty A) (cty B) (var 0)))
        (pi1 (wty A) (cty B) (var 0)) nvars) (dia A))
      (tsub (dsub (pi2 (wty A) (cty B) (var 0))
        (app (wty A) (pi1 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) (var 1))
          (pi1 (wty A) (cty B) (var 0))) nvars) (dia B)) Zc
  | .all A =>
    tsub (dsub (pi2 TN (cty A) (var 0)) (app TN (var 1) (pi1 TN (cty A) (var 0)))
      (prepend [pi1 TN (cty A) (var 0)] nvars)) (dia A)
  | .ex A =>
    tsub (dsub (var 0) (pi2 TN (wty A) (var 1)) (prepend [pi1 TN (wty A) (var 1)] nvars)) (dia A)
  | .px _ => num 1

/-- Rocq: `Analysis.Dialectica.dctx`. -/
def dctx (A : Form) : Nat → Ty := dsub (cty A) (wty A) TN0

theorem wt_dsub {Γ Δ : Nat → Ty} {Y X : Term} {F : Nat → Term} (hy : Wt Δ Y (Γ 0)) (hx : Wt Δ X (Γ 1))
    (hf : ∀ j, Wt Δ (F j) (Γ (j + 2))) : ∀ i, Wt Δ (dsub Y X F i) (Γ i)
  | 0 => hy
  | 1 => hx
  | j + 2 => hf j

/-- Rocq: `Analysis.Dialectica.wt_dia`. -/
theorem wt_dia : ∀ A : Form, Wt (dctx A) (dia A) TN
  | .eq s t => wt_eqT (wt_tsub (wt_tr (Γ := TN0) (fun _ => rfl) s) (fun _ => wt_var' rfl))
      (wt_tsub (wt_tr (Γ := TN0) (fun _ => rfl) t) (fun _ => wt_var' rfl))
  | .bot => .app _ _ _ _ .Suc .Z
  | .conj A B => wt_addT
      (wt_tsub (wt_dia A) (wt_dsub (wt_pi1 (wt_var' rfl)) (wt_pi1 (wt_var' rfl)) (fun _ => wt_var' rfl)))
      (wt_tsub (wt_dia B) (wt_dsub (wt_pi2 (wt_var' rfl)) (wt_pi2 (wt_var' rfl)) (fun _ => wt_var' rfl)))
  | .disj A B => wt_cond (wt_pi1 (wt_var' rfl))
      (wt_tsub (wt_dia A) (wt_dsub (wt_pi1 (wt_var' rfl)) (wt_pi1 (wt_pi2 (wt_var' rfl)))
        (fun _ => wt_var' rfl)))
      (wt_tsub (wt_dia B) (wt_dsub (wt_pi2 (wt_var' rfl)) (wt_pi2 (wt_pi2 (wt_var' rfl)))
        (fun _ => wt_var' rfl)))
  | .imp A B => wt_cond
      (wt_tsub (wt_dia A) (wt_dsub
        (.app _ _ _ _ (.app _ _ _ _ (wt_pi2 (wt_var' rfl)) (wt_pi1 (wt_var' rfl))) (wt_pi2 (wt_var' rfl)))
        (wt_pi1 (wt_var' rfl)) (fun _ => wt_var' rfl)))
      (wt_tsub (wt_dia B) (wt_dsub (wt_pi2 (wt_var' rfl))
        (.app _ _ _ _ (wt_pi1 (wt_var' rfl)) (wt_pi1 (wt_var' rfl))) (fun _ => wt_var' rfl)))
      .Z
  | .all A => wt_tsub (wt_dia A) (wt_dsub (wt_pi2 (wt_var' rfl))
      (.app _ _ _ _ (wt_var' rfl) (wt_pi1 (wt_var' rfl)))
      (fun | 0 => wt_pi1 (wt_var' rfl) | _ + 1 => wt_var' rfl))
  | .ex A => wt_tsub (wt_dia A) (wt_dsub (wt_var' rfl) (wt_pi2 (wt_var' rfl))
      (fun | 0 => wt_pi1 (wt_var' rfl) | _ + 1 => wt_var' rfl))
  | .px _ => .app _ _ _ _ .Suc .Z

/-! ## Truth of the matrix on closed instances -/

/-- Rocq: `Analysis.Dialectica.Dsem`. -/
def Dsem (A : Form) (x y : Term) (ns : Nat → Term) : Prop := Holds (tsub (dsub y x ns) (dia A))

/-- Rocq: `Analysis.Dialectica.DT`. -/
def DT (A : Form) (x y : Term) (ns : Nat → Term) : Prop :=
  Typing [] x (wty A) ∧ Typing [] y (cty A) ∧ Ns ns

/-- Rocq: `Analysis.Dialectica.dia_typing`. -/
theorem dia_typing {A : Form} {x y : Term} {ns : Nat → Term} (h : DT A x y ns) :
    Typing [] (tsub (dsub y x ns) (dia A)) TN :=
  wt_typing (wt_dia A) (fun | 0 => h.2.1 | 1 => h.1 | j + 2 => h.2.2 j)

/-- Rocq: `Analysis.Dialectica.tsub_dsub`. -/
theorem tsub_dsub (σ : Nat → Term) (Y X : Term) (NF : Nat → Term) (M : Term) :
    tsub σ (tsub (dsub Y X NF) M) = tsub (dsub (tsub σ Y) (tsub σ X) (fun j => tsub σ (NF j))) M :=
  (tsub_comp _ _ _).trans (tsub_ext (ρ := fun i => tsub σ (dsub Y X NF i))
    (ρ' := dsub (tsub σ Y) (tsub σ X) (fun j => tsub σ (NF j))) (fun | 0 => rfl | 1 => rfl | _ + 2 => rfl) M)

/-- Rocq: `Analysis.Dialectica.Dsem_star`. -/
theorem Dsem_star (A : Form) {x x' y y' : Term} {ns ns' : Nat → Term} (hx : Star x x') (hy : Star y y')
    (hn : ∀ j, Star (ns j) (ns' j)) : Dsem A x y ns ↔ Dsem A x' y' ns' :=
  holds_star (star_tsub (fun | 0 => hy | 1 => hx | j + 2 => hn j) _)

/-- Rocq: `Analysis.Dialectica.Dsem_ext`. -/
theorem Dsem_ext (A : Form) (x y : Term) {ns ns' : Nat → Term} (E : ∀ j, ns j = ns' j) :
    Dsem A x y ns ↔ Dsem A x y ns' := by
  unfold Dsem
  rw [tsub_ext (ρ := dsub y x ns) (ρ' := dsub y x ns') (fun | 0 => rfl | 1 => rfl | j + 2 => E j)]

/-- Rocq: `Analysis.Dialectica.holds_addT`. -/
theorem holds_addT {p q : Term} (hp : Typing [] p TN) (hq : Typing [] q TN) :
    Holds (addT p q) ↔ Holds p ∧ Holds q := by
  obtain ⟨m, hm⟩ := T_eval hp
  obtain ⟨k, hk⟩ := T_eval hq
  have ha := addT_eval hm hk
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨e1, e2⟩ := add_eq_zero (star_num_unique ha h)
    subst e1; subst e2
    exact ⟨hm, hk⟩
  · rw [star_num_unique hm h1, star_num_unique hk h2] at ha
    exact ha

/-- Rocq: `Analysis.Dialectica.holds_cond`. -/
theorem holds_cond {z : Term} (p q : Term) (hz : Typing [] z TN) :
    Holds (cond TN z p q) ↔ (Holds z ∧ Holds p) ∨ ((∃ m, Star z (num (m + 1))) ∧ Holds q) :=
  match holds_dec hz with
  | .inl h0 =>
    let hs := holds_star (cond_0 TN p q h0)
    ⟨fun h => .inl ⟨h0, hs.1 h⟩, fun
      | .inl ⟨_, h⟩ => hs.2 h
      | .inr ⟨⟨_, hm⟩, _⟩ => absurd h0 (not_holds hm)⟩
  | .inr ⟨m, hm⟩ =>
    let hs := holds_star (cond_S TN p q hm)
    ⟨fun h => .inr ⟨⟨m, hm⟩, hs.1 h⟩, fun
      | .inl ⟨h, _⟩ => absurd h (not_holds hm)
      | .inr ⟨_, h⟩ => hs.2 h⟩

/-- Rocq: `Analysis.Dialectica.holds_imp`. -/
theorem holds_imp {p : Term} (q : Term) (hp : Typing [] p TN) :
    Holds (cond TN p q Zc) ↔ (Holds p → Holds q) :=
  let hc := holds_cond q Zc hp
  ⟨fun h h' => match hc.1 h with
    | .inl ⟨_, h⟩ => h
    | .inr ⟨⟨_, hm⟩, _⟩ => absurd h' (not_holds hm),
   fun h => hc.2 (match holds_dec hp with
    | .inl h0 => .inl ⟨h0, h h0⟩
    | .inr hm => .inr ⟨hm, .refl _⟩)⟩

/-- Rocq: `Analysis.Dialectica.typing_pi1`. -/
theorem typing_pi1 {A B : Ty} {M : Term} (h : Typing [] M (TPr A B)) : Typing [] (pi1 A B M) A :=
  .app _ _ _ _ (.P1 _ _) h

/-- Rocq: `Analysis.Dialectica.typing_pi2`. -/
theorem typing_pi2 {A B : Ty} {M : Term} (h : Typing [] M (TPr A B)) : Typing [] (pi2 A B M) B :=
  .app _ _ _ _ (.P2 _ _) h

/-- Rocq: `Analysis.Dialectica.Ns_cons`. -/
theorem Ns_cons {z : Term} {ns : Nat → Term} (hz : Typing [] z TN) (hn : Ns ns) : Ns (prepend [z] ns)
  | 0 => hz
  | j + 1 => hn j

/-! The clauses of the interpretation. -/

/-- Rocq: `Analysis.Dialectica.D_bot`. -/
theorem D_bot (x y : Term) (ns : Nat → Term) : ¬ Dsem .bot x y ns := fun h =>
  not_holds (m := 0) (.refl _) h

/-- Rocq: `Analysis.Dialectica.D_eq`. -/
theorem D_eq (s t : ATerm) (x y : Term) {ns : Nat → Term} (hn : Ns ns) :
    Dsem (.eq s t) x y ns ↔ ∃ m, Star (tsub ns (tr s)) (num m) ∧ Star (tsub ns (tr t)) (num m) := by
  unfold Dsem
  show Holds (eqT (tsub _ (tsub nvars (tr s))) (tsub _ (tsub nvars (tr t)))) ↔ _
  rw [tsub_comp, tsub_comp]
  obtain ⟨m, hm⟩ := T_eval (typing_tr s hn)
  obtain ⟨k, hk⟩ := T_eval (typing_tr t hn)
  obtain ⟨d, hd, Ed⟩ := eqT_eval hm hk
  refine ⟨fun h => ?_, fun ⟨m', h1, h2⟩ => ?_⟩
  · have e := Ed.1 (star_num_unique hd h)
    subst e
    exact ⟨m, hm, hk⟩
  · have e1 := star_num_unique hm h1
    have e2 := star_num_unique hk h2
    subst e1; subst e2
    rw [Ed.2 rfl] at hd
    exact hd

/-- Rocq: `Analysis.Dialectica.D_and`. -/
theorem D_and (A B : Form) {x y : Term} {ns : Nat → Term} (h : DT (.conj A B) x y ns) :
    Dsem (.conj A B) x y ns ↔
      Dsem A (pi1 (wty A) (wty B) x) (pi1 (cty A) (cty B) y) ns ∧
      Dsem B (pi2 (wty A) (wty B) x) (pi2 (cty A) (cty B) y) ns := by
  obtain ⟨hx, hy, hn⟩ := h
  unfold Dsem
  show Holds (addT (tsub _ (tsub _ (dia A))) (tsub _ (tsub _ (dia B)))) ↔ _
  rw [tsub_dsub, tsub_dsub]
  exact holds_addT (dia_typing ⟨typing_pi1 hx, typing_pi1 hy, hn⟩)
    (dia_typing ⟨typing_pi2 hx, typing_pi2 hy, hn⟩)

/-- Rocq: `Analysis.Dialectica.D_or`. -/
theorem D_or (A B : Form) {x y : Term} {ns : Nat → Term} (h : DT (.disj A B) x y ns) :
    Dsem (.disj A B) x y ns ↔
      (Holds (pi1 TN (TPr (wty A) (wty B)) x) ∧
        Dsem A (pi1 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) x)) (pi1 (cty A) (cty B) y) ns) ∨
      ((∃ m, Star (pi1 TN (TPr (wty A) (wty B)) x) (num (m + 1))) ∧
        Dsem B (pi2 (wty A) (wty B) (pi2 TN (TPr (wty A) (wty B)) x)) (pi2 (cty A) (cty B) y) ns) := by
  obtain ⟨hx, _, _⟩ := h
  unfold Dsem
  show Holds (cond TN _ (tsub _ (tsub _ (dia A))) (tsub _ (tsub _ (dia B)))) ↔ _
  rw [tsub_dsub, tsub_dsub]
  exact holds_cond _ _ (typing_pi1 hx)

/-- Rocq: `Analysis.Dialectica.D_imp`. -/
theorem D_imp (A B : Form) {x y : Term} {ns : Nat → Term} (h : DT (.imp A B) x y ns) :
    Dsem (.imp A B) x y ns ↔
      (Dsem A (pi1 (wty A) (cty B) y)
          (app (cty B) (app (wty A) (pi2 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) x)
            (pi1 (wty A) (cty B) y)) (pi2 (wty A) (cty B) y)) ns →
        Dsem B (app (wty A) (pi1 (TAr (wty A) (wty B)) (TAr (wty A) (TAr (cty B) (cty A))) x)
          (pi1 (wty A) (cty B) y)) (pi2 (wty A) (cty B) y) ns) := by
  obtain ⟨hx, hy, hn⟩ := h
  unfold Dsem
  show Holds (cond TN (tsub _ (tsub _ (dia A))) (tsub _ (tsub _ (dia B))) Zc) ↔ _
  rw [tsub_dsub, tsub_dsub]
  exact holds_imp _ (dia_typing ⟨typing_pi1 hy,
    .app _ _ _ _ (.app _ _ _ _ (typing_pi2 hx) (typing_pi1 hy)) (typing_pi2 hy), hn⟩)

/-- Rocq: `Analysis.Dialectica.D_all`. -/
theorem D_all (A : Form) (x y : Term) (ns : Nat → Term) :
    Dsem (.all A) x y ns ↔
      Dsem A (app TN x (pi1 TN (cty A) y)) (pi2 TN (cty A) y) (prepend [pi1 TN (cty A) y] ns) := by
  have e : tsub (dsub y x ns) (tsub (dsub (pi2 TN (cty A) (var 0)) (app TN (var 1) (pi1 TN (cty A) (var 0)))
      (prepend [pi1 TN (cty A) (var 0)] nvars)) (dia A)) =
      tsub (dsub (pi2 TN (cty A) y) (app TN x (pi1 TN (cty A) y)) (prepend [pi1 TN (cty A) y] ns)) (dia A) :=
    by
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro i
      match i with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | _ + 3 => rfl
  unfold Dsem
  show Holds (tsub _ (tsub _ (dia A))) ↔ _
  rw [e]

/-- Rocq: `Analysis.Dialectica.D_ex`. -/
theorem D_ex (A : Form) (x y : Term) (ns : Nat → Term) :
    Dsem (.ex A) x y ns ↔ Dsem A (pi2 TN (wty A) x) y (prepend [pi1 TN (wty A) x] ns) := by
  have e : tsub (dsub y x ns) (tsub (dsub (var 0) (pi2 TN (wty A) (var 1))
      (prepend [pi1 TN (wty A) (var 1)] nvars)) (dia A)) =
      tsub (dsub y (pi2 TN (wty A) x) (prepend [pi1 TN (wty A) x] ns)) (dia A) :=
    by
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro i
      match i with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | _ + 3 => rfl
  unfold Dsem
  show Holds (tsub _ (tsub _ (dia A))) ↔ _
  rw [e]

theorem tsub_nvars_tr (y x : Term) (ns : Nat → Term) (σ : Nat → ATerm) (s : ATerm) :
    tsub (dsub y x ns) (tsub nvars (tr (asubst σ s))) =
      tsub (dsub y x (fun j => tsub ns (tr (σ j)))) (tsub nvars (tr s)) := by
  rw [tsub_comp, tsub_comp, tr_asubst, tsub_comp]
  rfl

/-- Substituting in the formula is substituting in the number variables.
Rocq: `Analysis.Dialectica.dia_subst`. -/
theorem dia_subst : ∀ (A : Form) (σ : Nat → ATerm) (y x : Term) (ns : Nat → Term),
    tsub (dsub y x ns) (dia (fsubst σ A)) = tsub (dsub y x (fun j => tsub ns (tr (σ j)))) (dia A)
  | .eq s t, σ, y, x, ns => congrArg₂ eqT (tsub_nvars_tr y x ns σ s) (tsub_nvars_tr y x ns σ t)
  | .bot, _, _, _, _ => rfl
  | .conj A B, σ, y, x, ns => by
    show tsub _ (addT (tsub (dsub (pi1 (cty (fsubst σ A)) (cty (fsubst σ B)) (var 0))
      (pi1 (wty (fsubst σ A)) (wty (fsubst σ B)) (var 1)) nvars) (dia (fsubst σ A)))
      (tsub (dsub (pi2 (cty (fsubst σ A)) (cty (fsubst σ B)) (var 0))
      (pi2 (wty (fsubst σ A)) (wty (fsubst σ B)) (var 1)) nvars) (dia (fsubst σ B)))) = _
    rw [cty_subst, cty_subst, wty_subst, wty_subst]
    show addT (tsub _ (tsub _ _)) (tsub _ (tsub _ _)) = addT (tsub _ (tsub _ _)) (tsub _ (tsub _ _))
    rw [tsub_dsub, tsub_dsub, tsub_dsub, tsub_dsub, dia_subst A σ, dia_subst B σ]
    rfl
  | .disj A B, σ, y, x, ns => by
    show tsub _ (cond TN (pi1 TN (TPr (wty (fsubst σ A)) (wty (fsubst σ B))) (var 1))
      (tsub (dsub (pi1 (cty (fsubst σ A)) (cty (fsubst σ B)) (var 0))
        (pi1 (wty (fsubst σ A)) (wty (fsubst σ B)) (pi2 TN (TPr (wty (fsubst σ A)) (wty (fsubst σ B)))
          (var 1))) nvars) (dia (fsubst σ A)))
      (tsub (dsub (pi2 (cty (fsubst σ A)) (cty (fsubst σ B)) (var 0))
        (pi2 (wty (fsubst σ A)) (wty (fsubst σ B)) (pi2 TN (TPr (wty (fsubst σ A)) (wty (fsubst σ B)))
          (var 1))) nvars) (dia (fsubst σ B)))) = _
    rw [cty_subst, cty_subst, wty_subst, wty_subst]
    show cond TN _ (tsub _ (tsub _ _)) (tsub _ (tsub _ _)) =
      cond TN _ (tsub _ (tsub _ _)) (tsub _ (tsub _ _))
    rw [tsub_dsub, tsub_dsub, tsub_dsub, tsub_dsub, dia_subst A σ, dia_subst B σ]
    rfl
  | .imp A B, σ, y, x, ns => by
    show tsub _ (cond TN
      (tsub (dsub (app (cty (fsubst σ B)) (app (wty (fsubst σ A))
          (pi2 (TAr (wty (fsubst σ A)) (wty (fsubst σ B)))
            (TAr (wty (fsubst σ A)) (TAr (cty (fsubst σ B)) (cty (fsubst σ A)))) (var 1))
          (pi1 (wty (fsubst σ A)) (cty (fsubst σ B)) (var 0))) (pi2 (wty (fsubst σ A)) (cty (fsubst σ B)) (var 0)))
        (pi1 (wty (fsubst σ A)) (cty (fsubst σ B)) (var 0)) nvars) (dia (fsubst σ A)))
      (tsub (dsub (pi2 (wty (fsubst σ A)) (cty (fsubst σ B)) (var 0))
        (app (wty (fsubst σ A)) (pi1 (TAr (wty (fsubst σ A)) (wty (fsubst σ B)))
            (TAr (wty (fsubst σ A)) (TAr (cty (fsubst σ B)) (cty (fsubst σ A)))) (var 1))
          (pi1 (wty (fsubst σ A)) (cty (fsubst σ B)) (var 0))) nvars) (dia (fsubst σ B))) Zc) = _
    rw [cty_subst, cty_subst, wty_subst, wty_subst]
    show cond TN (tsub _ (tsub _ _)) (tsub _ (tsub _ _)) Zc =
      cond TN (tsub _ (tsub _ _)) (tsub _ (tsub _ _)) Zc
    rw [tsub_dsub, tsub_dsub, tsub_dsub, tsub_dsub, dia_subst A σ, dia_subst B σ]
    rfl
  | .all A, σ, y, x, ns => by
    show tsub _ (tsub (dsub (pi2 TN (cty (fsubst (up σ) A)) (var 0))
      (app TN (var 1) (pi1 TN (cty (fsubst (up σ) A)) (var 0)))
      (prepend [pi1 TN (cty (fsubst (up σ) A)) (var 0)] nvars)) (dia (fsubst (up σ) A))) = _
    rw [cty_subst]
    show tsub _ (tsub _ _) = tsub _ (tsub _ _)
    rw [tsub_dsub, tsub_dsub, dia_subst A (up σ)]
    refine tsub_ext ?_ _
    intro i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 =>
      show tsub _ (tr (asubst shiftSub (σ k))) = _
      rw [tr_asubst, tsub_comp]
      rfl
  | .ex A, σ, y, x, ns => by
    show tsub _ (tsub (dsub (var 0) (pi2 TN (wty (fsubst (up σ) A)) (var 1))
      (prepend [pi1 TN (wty (fsubst (up σ) A)) (var 1)] nvars)) (dia (fsubst (up σ) A))) = _
    rw [wty_subst]
    show tsub _ (tsub _ _) = tsub _ (tsub _ _)
    rw [tsub_dsub, tsub_dsub, dia_subst A (up σ)]
    refine tsub_ext ?_ _
    intro i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | k + 3 =>
      show tsub _ (tr (asubst shiftSub (σ k))) = _
      rw [tr_asubst, tsub_comp]
      rfl
  | .px _, _, _, _, _ => rfl

/-- Rocq: `Analysis.Dialectica.D_subst`. -/
theorem D_subst (A : Form) (σ : Nat → ATerm) (x y : Term) (ns : Nat → Term) :
    Dsem (fsubst σ A) x y ns ↔ Dsem A x y (fun j => tsub ns (tr (σ j))) := by
  unfold Dsem
  rw [dia_subst]

/-- Rocq: `Analysis.Dialectica.D_shift`. -/
theorem D_shift (A : Form) (x y : Term) (ns : Nat → Term) :
    Dsem (fshift A) x y ns ↔ Dsem A x y (fun j => ns (j + 1)) := D_subst A _ x y ns

/-- Rocq: `Analysis.Dialectica.D_sub1`. -/
theorem D_sub1 (A : Form) (t : ATerm) (x y : Term) (ns : Nat → Term) :
    Dsem (sub1 A t) x y ns ↔ Dsem A x y (prepend [tsub ns (tr t)] ns) :=
  (D_subst A _ x y ns).trans (Dsem_ext A x y (fun | 0 => rfl | _ + 1 => rfl))

/-! ## Realizers of derivations

For a derivation of `Γ ⊢ A`, a witness term `t` for `A`, whose variables are
the witnesses `x_i` of the hypotheses followed by the number variables, and
for each hypothesis a counterexample term `s i`, which may also use the
counterexample `y` of `A` (variable `0`). If the counterexamples `s i` do not
refute the hypotheses, then `y` does not refute `t`. -/

theorem length_map' {α β : Type} (f : α → β) : ∀ l : List α, (l.map f).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (length_map' f l)

/-- Rocq: `Analysis.Dialectica.hctx`. -/
def hctx (Γ : List Form) : Nat → Ty := prepend (Γ.map wty) TN0
/-- Rocq: `Analysis.Dialectica.sctx`. -/
def sctx (A : Form) (Γ : List Form) : Nat → Ty := prepend (cty A :: Γ.map wty) TN0

/-- Rocq: `Analysis.Dialectica.XT`. -/
def XT (Γ : List Form) (xs : List Term) : Prop := Forall2 (fun x B => Typing [] x (wty B)) xs Γ

/-- Rocq: `Analysis.Dialectica.Hyps`. -/
def Hyps (Γ : List Form) (xs : List Term) (ys : Nat → Term) (ns : Nat → Term) : Prop :=
  ∀ i B, List.nthError Γ i = some B → Dsem B (nthD xs i Zc) (ys i) ns

/-- Rocq: `Analysis.Dialectica.Real`. -/
def Real (Γ : List Form) (A : Form) : Prop :=
  ∃ (t : Term) (s : Nat → Term),
    Wt (hctx Γ) t (wty A) ∧
    (∀ i B, List.nthError Γ i = some B → Wt (sctx A Γ) (s i) (cty B)) ∧
    ∀ xs y ns, XT Γ xs → Typing [] y (cty A) → Ns ns →
      Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (s i)) ns →
      Dsem A (tsub (prepend xs ns) t) y ns

/-- Rocq: `Analysis.Dialectica.XT_length`. -/
theorem XT_length {Γ : List Form} {xs : List Term} (h : XT Γ xs) : xs.length = Γ.length :=
  Forall2.length_eq h

/-- Rocq: `Analysis.Dialectica.XT_nth`. -/
theorem XT_nth {Γ : List Form} {xs : List Term} (h : XT Γ xs) :
    ∀ {i B}, List.nthError Γ i = some B → Typing [] (nthD xs i Zc) (wty B) := by
  induction h with
  | nil => intro i B hB; cases hB
  | cons hx _ ih =>
    intro i B hB
    cases i with
    | zero => cases hB; exact hx
    | succ i => exact ih hB

/-- Rocq: `Analysis.Dialectica.XT_map`. -/
theorem XT_map {Γ : List Form} {xs : List Term} (h : XT Γ xs) :
    Forall2 (fun x T => Typing [] x T) xs (Γ.map wty) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons hx ih

/-- Rocq: `Analysis.Dialectica.hctx_typed`. -/
theorem hctx_typed {Γ : List Form} {xs : List Term} {ns : Nat → Term} (h : XT Γ xs) (hn : Ns ns) :
    ∀ i, Typing [] (prepend xs ns i) (hctx Γ i) :=
  prepend_typing (XT_map h) hn

/-- Rocq: `Analysis.Dialectica.sctx_typed`. -/
theorem sctx_typed {A : Form} {Γ : List Form} {xs : List Term} {y : Term} {ns : Nat → Term}
    (h : XT Γ xs) (hy : Typing [] y (cty A)) (hn : Ns ns) :
    ∀ i, Typing [] (prepend (y :: xs) ns i) (sctx A Γ i)
  | 0 => hy
  | i + 1 => hctx_typed h hn i

/-- Rocq: `Analysis.Dialectica.hctx_nth`. -/
theorem hctx_nth : ∀ {Γ : List Form} {i : Nat} {B : Form}, List.nthError Γ i = some B → hctx Γ i = wty B
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: Γ, i + 1, _, h => hctx_nth (Γ := Γ) h

/-- Rocq: `Analysis.Dialectica.hctx_ge`. -/
theorem hctx_ge (Γ : List Form) {i : Nat} (h : Γ.length ≤ i) : hctx Γ i = TN := by
  unfold hctx
  rw [prepend_ge' _ _ _ (by rw [length_map']; exact h)]
  rfl

/-- Rocq: `Analysis.Dialectica.inst_t`. -/
theorem inst_t {Γ : List Form} {t : Term} {T : Ty} {xs : List Term} {ns : Nat → Term}
    (h : Wt (hctx Γ) t T) (hx : XT Γ xs) (hn : Ns ns) : Typing [] (tsub (prepend xs ns) t) T :=
  wt_typing h (hctx_typed hx hn)

/-- Rocq: `Analysis.Dialectica.inst_s`. -/
theorem inst_s {A : Form} {Γ : List Form} {s : Term} {T : Ty} {xs : List Term} {y : Term}
    {ns : Nat → Term} (h : Wt (sctx A Γ) s T) (hx : XT Γ xs) (hy : Typing [] y (cty A)) (hn : Ns ns) :
    Typing [] (tsub (prepend (y :: xs) ns) s) T :=
  wt_typing h (sctx_typed hx hy hn)

/-! Moving terms between the two kinds of context. -/

/-- Rocq: `Analysis.Dialectica.shs`. -/
def shs : Nat → Term := fun i => var (i + 1)
/-- Rocq: `Analysis.Dialectica.ysub`. -/
def ysub (Y : Term) : Nat → Term := prepend [Y] shs

/-- Rocq: `Analysis.Dialectica.inst_shs`. -/
theorem inst_shs (y : Term) (xs : List Term) (ns : Nat → Term) (M : Term) :
    tsub (prepend (y :: xs) ns) (tsub shs M) = tsub (prepend xs ns) M := by
  rw [tsub_comp]; rfl

/-- Rocq: `Analysis.Dialectica.inst_ysub`. -/
theorem inst_ysub (y : Term) (xs : List Term) (ns : Nat → Term) (Y M : Term) :
    tsub (prepend (y :: xs) ns) (tsub (ysub Y) M) = tsub (prepend (tsub (prepend (y :: xs) ns) Y :: xs) ns) M := by
  rw [tsub_comp]
  refine tsub_ext ?_ _
  intro i
  match i with
  | 0 => rfl
  | _ + 1 => rfl

/-- Rocq: `Analysis.Dialectica.wt_shs`. -/
theorem wt_shs (A : Form) {Γ : List Form} {M : Term} {T : Ty} (h : Wt (hctx Γ) M T) :
    Wt (sctx A Γ) (tsub shs M) T :=
  wt_tsub h (fun _ => wt_var' rfl)

/-- Rocq: `Analysis.Dialectica.wt_ysub`. -/
theorem wt_ysub {A A' : Form} {Γ : List Form} {Y M : Term} {T : Ty} (h : Wt (sctx A' Γ) M T)
    (hY : Wt (sctx A Γ) Y (cty A')) : Wt (sctx A Γ) (tsub (ysub Y) M) T :=
  wt_tsub h (fun | 0 => hY | _ + 1 => wt_var' rfl)

/-- Rocq: `Analysis.Dialectica.Hyps_star`. -/
theorem Hyps_star (Γ : List Form) (xs : List Term) {ys ys' : Nat → Term} (ns : Nat → Term)
    (h : ∀ i, Star (ys i) (ys' i)) : Hyps Γ xs ys ns ↔ Hyps Γ xs ys' ns :=
  ⟨fun hh i B hB => (Dsem_star B (.refl _) (h i) (fun _ => .refl _)).1 (hh i B hB),
   fun hh i B hB => (Dsem_star B (.refl _) (h i) (fun _ => .refl _)).2 (hh i B hB)⟩

/-- Rocq: `Analysis.Dialectica.Hyps_ext`. -/
theorem Hyps_ext (Γ : List Form) (xs : List Term) {ys ys' : Nat → Term} (ns : Nat → Term)
    (h : ∀ i, ys i = ys' i) : Hyps Γ xs ys ns ↔ Hyps Γ xs ys' ns :=
  Hyps_star Γ xs ns (fun i => h i ▸ .refl _)

/-- Default terms of every type. Rocq: `Analysis.Dialectica.zero`. -/
def zero : Ty → Term
  | TN => Zc
  | TAr A B => Kt B A (zero B)
  | TPr A B => tpair A B (zero A) (zero B)

/-- Rocq: `Analysis.Dialectica.wt_zero`. -/
theorem wt_zero (Γ : Nat → Ty) : ∀ T, Wt Γ (zero T) T
  | TN => .Z
  | TAr _ B => wt_Kt _ (wt_zero Γ B)
  | TPr A B => wt_tpair (wt_zero Γ A) (wt_zero Γ B)

/-- Rocq: `Analysis.Dialectica.tsub_zero`. -/
theorem tsub_zero (ρ : Nat → Term) : ∀ T, tsub ρ (zero T) = zero T
  | TN => rfl
  | TAr A B => congrArg (app B (Kc B A)) (tsub_zero ρ B)
  | TPr A B => congrArg₂ (fun a b => app B (app A (Pc A B) a) b) (tsub_zero ρ A) (tsub_zero ρ B)

/-- Rocq: `Analysis.Dialectica.typing_zero`. -/
theorem typing_zero (T : Ty) : Typing [] (zero T) T := by
  have := wt_typing (wt_zero TN0 T) (ρ := fun _ => Zc) (fun _ => .Z)
  rw [tsub_zero] at this
  exact this

/-- Rocq: `Analysis.Dialectica.zeros`. -/
def zeros (Γ : List Form) : Nat → Term := fun i => zero (cty (nthD Γ i .bot))

/-- Rocq: `Analysis.Dialectica.nth_error_nth'`. -/
theorem nthError_nthD : ∀ {Γ : List Form} {i : Nat} {B : Form}, List.nthError Γ i = some B → nthD Γ i .bot = B
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: Γ, i + 1, _, h => nthError_nthD (Γ := Γ) h

/-- Rocq: `Analysis.Dialectica.wt_zeros`. -/
theorem wt_zeros (A : Form) {Γ : List Form} {i : Nat} {B : Form} (h : List.nthError Γ i = some B) :
    Wt (sctx A Γ) (zeros Γ i) (cty B) := by
  unfold zeros; rw [nthError_nthD h]; exact wt_zero _ _

/-- Merging two lists of counterexamples: for each hypothesis, keep the first
candidate if it refutes the hypothesis, and the second otherwise. This is
where the matrices must be decidable. Rocq: `Analysis.Dialectica.merge1`. -/
def merge1 (n : Nat) (B : Form) (i : Nat) (a b : Term) : Term :=
  cond (cty B) (tsub (dsub a (var (i + 1)) (fun j => var (n + j + 1))) (dia B)) b a

/-- Rocq: `Analysis.Dialectica.mergeS`. -/
def mergeS (Γ : List Form) (a b : Nat → Term) : Nat → Term :=
  fun i => merge1 Γ.length (nthD Γ i .bot) i (a i) (b i)

/-- Rocq: `Analysis.Dialectica.nth_error_lt`. -/
theorem nthError_lt {X : Type} : ∀ {l : List X} {i : Nat} {a : X}, List.nthError l i = some a → i < l.length
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: l, _ + 1, _, h => Nat.succ_lt_succ (nthError_lt (l := l) h)

/-- Rocq: `Analysis.Dialectica.wt_mergeS`. -/
theorem wt_mergeS (A : Form) {Γ : List Form} {a b : Nat → Term} {i : Nat} {B : Form}
    (hB : List.nthError Γ i = some B) (ha : Wt (sctx A Γ) (a i) (cty B)) (hb : Wt (sctx A Γ) (b i) (cty B)) :
    Wt (sctx A Γ) (mergeS Γ a b i) (cty B) := by
  unfold mergeS merge1
  rw [nthError_nthD hB]
  refine wt_cond (wt_tsub (wt_dia B) (wt_dsub ha (wt_var' (hctx_nth hB)) (fun j => wt_var' ?_))) hb ha
  show hctx Γ (Γ.length + j) = TN
  exact hctx_ge Γ (Nat.le_add_right _ _)

/-- Rocq: `Analysis.Dialectica.merge_sem`. -/
theorem merge_sem {Γ : List Form} {a b : Nat → Term} {xs : List Term} {y : Term} {ns : Nat → Term}
    (hx : XT Γ xs) (hn : Ns ns)
    (ha : ∀ i B, List.nthError Γ i = some B → Typing [] (tsub (prepend (y :: xs) ns) (a i)) (cty B))
    (h : Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (mergeS Γ a b i)) ns) :
    Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (a i)) ns ∧
      Hyps Γ xs (fun i => tsub (prepend (y :: xs) ns) (b i)) ns := by
  have hlen := XT_length hx
  have hboth : ∀ i B, List.nthError Γ i = some B →
      Dsem B (nthD xs i Zc) (tsub (prepend (y :: xs) ns) (a i)) ns ∧
        Dsem B (nthD xs i Zc) (tsub (prepend (y :: xs) ns) (b i)) ns := by
    intro i B hB
    have hi := h i B hB
    have Ez : tsub (prepend (y :: xs) ns) (tsub (dsub (a i) (var (i + 1))
        (fun j => var (Γ.length + j + 1))) (dia B)) =
        tsub (dsub (tsub (prepend (y :: xs) ns) (a i)) (nthD xs i Zc) ns) (dia B) := by
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro k
      match k with
      | 0 => rfl
      | 1 =>
        show prepend xs ns i = nthD xs i Zc
        exact prepend_lt xs ns i Zc (hlen ▸ nthError_lt hB)
      | j + 2 =>
        show prepend xs ns (Γ.length + j) = ns j
        rw [← hlen]; exact prepend_ge xs ns j
    have hiz : Dsem B (nthD xs i Zc) (cond (cty B) (tsub (dsub (tsub (prepend (y :: xs) ns) (a i))
        (nthD xs i Zc) ns) (dia B)) (tsub (prepend (y :: xs) ns) (b i))
        (tsub (prepend (y :: xs) ns) (a i))) ns := by
      have hi' : Dsem B (nthD xs i Zc)
          (tsub (prepend (y :: xs) ns) (merge1 Γ.length (nthD Γ i .bot) i (a i) (b i))) ns := hi
      rw [nthError_nthD hB] at hi'
      unfold merge1 at hi'
      rw [tsub_cond, Ez] at hi'
      exact hi'
    have hz : Typing [] (tsub (dsub (tsub (prepend (y :: xs) ns) (a i)) (nthD xs i Zc) ns) (dia B)) TN :=
      dia_typing ⟨XT_nth hx hB, ha i B hB, hn⟩
    match holds_dec hz with
    | .inl h0 =>
      exact ⟨h0, (Dsem_star B (.refl _) (cond_0 _ _ _ h0) (fun _ => .refl _)).1 hiz⟩
    | .inr ⟨_, hm⟩ =>
      exact absurd ((Dsem_star B (.refl _) (cond_S _ _ _ hm) (fun _ => .refl _)).1 hiz) (not_holds hm)
  exact ⟨fun i B hB => (hboth i B hB).1, fun i B hB => (hboth i B hB).2⟩

/-- Rocq: `Analysis.Dialectica.Hyps_ext'`. -/
theorem Hyps_ext' {Γ : List Form} {xs : List Term} {ys ys' : Nat → Term} {ns : Nat → Term}
    (h : Hyps Γ xs ys ns) (E : ∀ i, ys i = ys' i) : Hyps Γ xs ys' ns :=
  (Hyps_ext Γ xs ns E).1 h

/-- Rocq: `Analysis.Dialectica.Hyps_red`. -/
theorem Hyps_red {Γ : List Form} {xs : List Term} {ys ys' : Nat → Term} {ns : Nat → Term}
    (h : Hyps Γ xs ys' ns) (E : ∀ i, Star (ys i) (ys' i)) : Hyps Γ xs ys ns :=
  (Hyps_star Γ xs ns E).2 h

/-- Rocq: `Analysis.Dialectica.Dsem_red`. -/
theorem Dsem_red {A : Form} {x x' y y' : Term} {ns : Nat → Term} (hx : Star x x') (hy : Star y y')
    (h : Dsem A x' y' ns) : Dsem A x y ns :=
  (Dsem_star A hx hy (fun _ => .refl _)).2 h

/-- Rocq: `Analysis.Dialectica.Dsem_fwd`. -/
theorem Dsem_fwd {A : Form} {x x' y y' : Term} {ns : Nat → Term} (hx : Star x x') (hy : Star y y')
    (h : Dsem A x y ns) : Dsem A x' y' ns :=
  (Dsem_star A hx hy (fun _ => .refl _)).1 h

/-- Rocq: `Analysis.Dialectica.XT_cons`. -/
theorem XT_cons {Γ : List Form} {xs : List Term} {A : Form} {x : Term} (hx : Typing [] x (wty A))
    (h : XT Γ xs) : XT (A :: Γ) (x :: xs) :=
  .cons hx h

/-! ## Soundness, rule by rule -/

theorem mem_nthError {A : Form} : ∀ {Γ : List Form}, A ∈ Γ → ∃ p, List.nthError Γ p = some A
  | _ :: _, .head _ => ⟨0, rfl⟩
  | _ :: _, .tail _ h => let ⟨p, hp⟩ := mem_nthError h; ⟨p + 1, hp⟩

/-- Rocq: `Analysis.Dialectica.R_hyp`. -/
theorem R_hyp {Γ : List Form} {A : Form} (h : A ∈ Γ) : Real Γ A := by
  obtain ⟨p, hp⟩ := mem_nthError h
  refine ⟨var p, fun i => if i = p then var 0 else zeros Γ i, wt_var' (hctx_nth hp), ?_, ?_⟩
  · intro i B hB
    by_cases hi : i = p
    · subst hi
      rw [hp] at hB; cases hB
      show Wt _ (if i = i then var 0 else _) _
      rw [ite_eq_left rfl]; exact wt_var' rfl
    · show Wt _ (if i = p then var 0 else _) _
      rw [ite_eq_right hi]; exact wt_zeros A hB
  · intro xs y ns hx _ _ hh
    have H := hh p A hp
    have e : (fun i => tsub (prepend (y :: xs) ns) (if i = p then var 0 else zeros Γ i)) p = y := by
      show tsub _ (if p = p then var 0 else _) = y
      rw [ite_eq_left rfl]; rfl
    rw [e] at H
    show Dsem A (prepend xs ns p) y ns
    rw [prepend_lt xs ns p Zc (XT_length hx ▸ nthError_lt hp)]
    exact H

/-- Rocq: `Analysis.Dialectica.R_botE`. -/
theorem R_botE {Γ : List Form} {A : Form} (h : Real Γ .bot) : Real Γ A := by
  obtain ⟨t, s, _, hs, H⟩ := h
  refine ⟨zero (wty A), fun i => tsub (ysub Zc) (s i), wt_zero _ _,
    fun i B hB => wt_ysub (A' := .bot) (hs i B hB) .Z, ?_⟩
  intro xs y ns hx _ hn hh
  refine absurd (H xs Zc ns hx .Z hn ?_) (D_bot _ _ _)
  exact Hyps_ext' hh (fun i => inst_ysub y xs ns Zc (s i))

/-- Rocq: `Analysis.Dialectica.R_andI`. -/
theorem R_andI {Γ : List Form} {A B : Form} (h1 : Real Γ A) (h2 : Real Γ B) : Real Γ (.conj A B) := by
  obtain ⟨t1, s1, ht1, hs1, H1⟩ := h1
  obtain ⟨t2, s2, ht2, hs2, H2⟩ := h2
  let a := fun i => tsub (ysub (pi1 (cty A) (cty B) (var 0))) (s1 i)
  let b := fun i => tsub (ysub (pi2 (cty A) (cty B) (var 0))) (s2 i)
  have ha : ∀ i C, List.nthError Γ i = some C → Wt (sctx (.conj A B) Γ) (a i) (cty C) :=
    fun i C hC => wt_ysub (hs1 i C hC) (wt_pi1 (wt_var' rfl))
  have hb : ∀ i C, List.nthError Γ i = some C → Wt (sctx (.conj A B) Γ) (b i) (cty C) :=
    fun i C hC => wt_ysub (hs2 i C hC) (wt_pi2 (wt_var' rfl))
  refine ⟨tpair (wty A) (wty B) t1 t2, mergeS Γ a b, wt_tpair ht1 ht2,
    fun i C hC => wt_mergeS _ hC (ha i C hC) (hb i C hC), ?_⟩
  intro xs y ns hx hy hn hh
  obtain ⟨hha, hhb⟩ := merge_sem hx hn (fun i C hC => inst_s (ha i C hC) hx hy hn) hh
  have hA := inst_t ht1 hx hn
  have hB := inst_t ht2 hx hn
  refine (D_and A B ⟨.app _ _ _ _ (.app _ _ _ _ (.P _ _) hA) hB, hy, hn⟩).2 ⟨?_, ?_⟩
  · refine Dsem_red (star_pi1 _ _ _ _ _ _) (.refl _) ?_
    exact H1 xs _ ns hx (typing_pi1 hy) hn (Hyps_ext' hha (fun i => inst_ysub y xs ns _ (s1 i)))
  · refine Dsem_red (star_pi2 _ _ _ _ _ _) (.refl _) ?_
    exact H2 xs _ ns hx (typing_pi2 hy) hn (Hyps_ext' hhb (fun i => inst_ysub y xs ns _ (s2 i)))

/-- Rocq: `Analysis.Dialectica.R_andE1`. -/
theorem R_andE1 {Γ : List Form} {A B : Form} (h : Real Γ (.conj A B)) : Real Γ A := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  refine ⟨pi1 (wty A) (wty B) t, fun i => tsub (ysub (tpair (cty A) (cty B) (var 0) (zero (cty B)))) (s i),
    wt_pi1 ht, fun i C hC => wt_ysub (hs i C hC) (wt_tpair (wt_var' rfl) (wt_zero _ _)), ?_⟩
  intro xs y ns hx hy hn hh
  have hy' : Typing [] (tpair (cty A) (cty B) y (zero (cty B))) (cty (.conj A B)) :=
    .app _ _ _ _ (.app _ _ _ _ (.P _ _) hy) (typing_zero _)
  have HD := H xs _ ns hx hy' hn (Hyps_ext' hh (fun i => by
    rw [inst_ysub]; show tsub (prepend (tpair _ _ y (tsub _ (zero (cty B))) :: xs) ns) (s i) = _
    rw [tsub_zero]))
  have HD' := ((D_and A B ⟨inst_t ht hx hn, hy', hn⟩).1 HD).1
  exact Dsem_fwd (.refl _) (star_pi1 _ _ _ _ _ _) HD'

/-- Rocq: `Analysis.Dialectica.R_andE2`. -/
theorem R_andE2 {Γ : List Form} {A B : Form} (h : Real Γ (.conj A B)) : Real Γ B := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  refine ⟨pi2 (wty A) (wty B) t, fun i => tsub (ysub (tpair (cty A) (cty B) (zero (cty A)) (var 0))) (s i),
    wt_pi2 ht, fun i C hC => wt_ysub (hs i C hC) (wt_tpair (wt_zero _ _) (wt_var' rfl)), ?_⟩
  intro xs y ns hx hy hn hh
  have hy' : Typing [] (tpair (cty A) (cty B) (zero (cty A)) y) (cty (.conj A B)) :=
    .app _ _ _ _ (.app _ _ _ _ (.P _ _) (typing_zero _)) hy
  have HD := H xs _ ns hx hy' hn (Hyps_ext' hh (fun i => by
    rw [inst_ysub]; show tsub (prepend (tpair _ _ (tsub _ (zero (cty A))) y :: xs) ns) (s i) = _
    rw [tsub_zero]))
  have HD' := ((D_and A B ⟨inst_t ht hx hn, hy', hn⟩).1 HD).2
  exact Dsem_fwd (.refl _) (star_pi2 _ _ _ _ _ _) HD'

/-- Rocq: `Analysis.Dialectica.ins0`. -/
theorem ins0 {X : Type} (a : X) (f : Nat → X) : ∀ i, ins 0 a f i = prepend [a] f i
  | 0 => rfl
  | _ + 1 => rfl

/-- Rocq: `Analysis.Dialectica.inst_ysub_eq`. -/
theorem inst_ysub_eq {y : Term} {xs : List Term} {ns : Nat → Term} {Y Y' : Term} (M : Term)
    (h : tsub (prepend (y :: xs) ns) Y = Y') :
    tsub (prepend (y :: xs) ns) (tsub (ysub Y) M) = tsub (prepend (Y' :: xs) ns) M := by
  rw [inst_ysub, h]

/-- Rocq: `Analysis.Dialectica.R_orI1`. -/
theorem R_orI1 {Γ : List Form} {A B : Form} (h : Real Γ A) : Real Γ (.disj A B) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  refine ⟨tpair TN (TPr (wty A) (wty B)) Zc (tpair (wty A) (wty B) t (zero (wty B))),
    fun i => tsub (ysub (pi1 (cty A) (cty B) (var 0))) (s i),
    wt_tpair .Z (wt_tpair ht (wt_zero _ _)), fun i C hC => wt_ysub (hs i C hC) (wt_pi1 (wt_var' rfl)), ?_⟩
  intro xs y ns hx hy hn hh
  have ht' := inst_t ht hx hn
  have hT : Typing [] (tsub (prepend xs ns) (tpair TN (TPr (wty A) (wty B)) Zc
      (tpair (wty A) (wty B) t (zero (wty B))))) (wty (.disj A B)) := by
    show Typing [] (tpair _ _ Zc (tpair _ _ _ (tsub _ (zero (wty B))))) _
    rw [tsub_zero]
    exact .app _ _ _ _ (.app _ _ _ _ (.P _ _) .Z) (.app _ _ _ _ (.app _ _ _ _ (.P _ _) ht') (typing_zero _))
  refine (D_or A B ⟨hT, hy, hn⟩).2 (.inl ⟨star_pi1 _ _ _ _ _ _, ?_⟩)
  refine Dsem_red (star_pi1' _ _ (star_pi2 _ _ _ _ _ _)) (.refl _) ?_
  exact H xs _ ns hx (typing_pi1 hy) hn (Hyps_ext' hh (fun i => inst_ysub_eq _ rfl))

/-- Rocq: `Analysis.Dialectica.R_orI2`. -/
theorem R_orI2 {Γ : List Form} {A B : Form} (h : Real Γ B) : Real Γ (.disj A B) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  refine ⟨tpair TN (TPr (wty A) (wty B)) (num 1) (tpair (wty A) (wty B) (zero (wty A)) t),
    fun i => tsub (ysub (pi2 (cty A) (cty B) (var 0))) (s i),
    wt_tpair (.app _ _ _ _ .Suc .Z) (wt_tpair (wt_zero _ _) ht),
    fun i C hC => wt_ysub (hs i C hC) (wt_pi2 (wt_var' rfl)), ?_⟩
  intro xs y ns hx hy hn hh
  have ht' := inst_t ht hx hn
  have hT : Typing [] (tsub (prepend xs ns) (tpair TN (TPr (wty A) (wty B)) (num 1)
      (tpair (wty A) (wty B) (zero (wty A)) t))) (wty (.disj A B)) := by
    show Typing [] (tpair _ _ (num 1) (tpair _ _ (tsub _ (zero (wty A))) _)) _
    rw [tsub_zero]
    exact .app _ _ _ _ (.app _ _ _ _ (.P _ _) (typing_num [] 1))
      (.app _ _ _ _ (.app _ _ _ _ (.P _ _) (typing_zero _)) ht')
  refine (D_or A B ⟨hT, hy, hn⟩).2 (.inr ⟨⟨0, star_pi1 _ _ _ _ _ _⟩, ?_⟩)
  refine Dsem_red (star_pi2' _ _ (star_pi2 _ _ _ _ _ _)) (.refl _) ?_
  exact H xs _ ns hx (typing_pi2 hy) hn (Hyps_ext' hh (fun i => inst_ysub_eq _ rfl))

/-- Rocq: `Analysis.Dialectica.Hyps_cons`. -/
theorem Hyps_cons {A : Form} {Γ : List Form} {x : Term} {xs : List Term} {ys : Nat → Term}
    {ns : Nat → Term} (h0 : Dsem A x (ys 0) ns) (h : Hyps Γ xs (fun i => ys (i + 1)) ns) :
    Hyps (A :: Γ) (x :: xs) ys ns
  | 0, _, hB => by cases hB; exact h0
  | i + 1, B, hB => h i B hB

/-- Rocq: `Analysis.Dialectica.R_impI`. -/
theorem R_impI {Γ : List Form} {A B : Form} (h : Real (A :: Γ) B) : Real Γ (.imp A B) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  let FA := TAr (wty A) (wty B)
  let GA := TAr (wty A) (TAr (cty B) (cty A))
  let f := lamAt (hctx (A :: Γ)) 0 t
  let g := lamAt (hctx (A :: Γ)) 0 (lamAt (sctx B (A :: Γ)) 0 (s 0))
  let ρ := dsub (pi2 (wty A) (cty B) (var 0)) (pi1 (wty A) (cty B) (var 0)) shs
  have hf : Wt (hctx Γ) f FA := wt_ext (Γ := rem 0 (hctx (A :: Γ))) (fun _ => rfl) (wt_lam_at 0 ht)
  have hg : Wt (hctx Γ) g GA :=
    wt_ext (Γ := rem 0 (hctx (A :: Γ))) (fun _ => rfl)
      (wt_lam_at 0 (wt_ext (Γ := rem 0 (sctx B (A :: Γ))) (fun _ => rfl) (wt_lam_at 0 (hs 0 A rfl))))
  refine ⟨tpair FA GA f g, fun i => tsub ρ (s (i + 1)), wt_tpair hf hg, ?_, ?_⟩
  · intro i C hC
    exact wt_tsub (hs (i + 1) C hC)
      (fun | 0 => wt_pi2 (wt_var' rfl) | 1 => wt_pi1 (wt_var' rfl) | _ + 2 => wt_var' rfl)
  · intro xs y ns hx hy hn hh
    have hT : Typing [] (tsub (prepend xs ns) (tpair FA GA f g)) (wty (.imp A B)) :=
      inst_t (wt_tpair hf hg) hx hn
    refine (D_imp A B ⟨hT, hy, hn⟩).2 (fun HA => ?_)
    have Ef : Star (app (wty A) (pi1 FA GA (tsub (prepend xs ns) (tpair FA GA f g))) (pi1 (wty A) (cty B) y))
        (tsub (prepend (pi1 (wty A) (cty B) y :: xs) ns) t) := by
      refine star_trans (star_app_l _ _ (star_pi1 _ _ _ _ _ _))
        (star_trans (star_lam_at _ 0 t (prepend xs ns) _ _) ?_)
      have e : tsub (ins 0 (pi1 (wty A) (cty B) y) (prepend xs ns)) t =
          tsub (prepend (pi1 (wty A) (cty B) y :: xs) ns) t := by
        refine tsub_ext ?_ t
        intro i
        match i with
        | 0 => rfl
        | _ + 1 => rfl
      rw [e]; exact .refl _
    have Eg : Star (app (cty B) (app (wty A) (pi2 FA GA (tsub (prepend xs ns) (tpair FA GA f g)))
          (pi1 (wty A) (cty B) y)) (pi2 (wty A) (cty B) y))
        (tsub (prepend (pi2 (wty A) (cty B) y :: pi1 (wty A) (cty B) y :: xs) ns) (s 0)) := by
      refine star_trans (star_app_l _ _ (star_app_l _ _ (star_pi2 _ _ _ _ _ _)))
        (star_trans (star_app_l _ _ (star_lam_at _ 0 _ (prepend xs ns) _ _))
          (star_trans (star_lam_at _ 0 (s 0) _ _ _) ?_))
      have e : tsub (ins 0 (pi2 (wty A) (cty B) y) (ins 0 (pi1 (wty A) (cty B) y) (prepend xs ns))) (s 0) =
          tsub (prepend (pi2 (wty A) (cty B) y :: pi1 (wty A) (cty B) y :: xs) ns) (s 0) := by
        refine tsub_ext ?_ (s 0)
        intro i
        match i with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 => rfl
      rw [e]; exact .refl _
    refine Dsem_red Ef (.refl _) (H _ _ ns (XT_cons (typing_pi1 hy) hx) (typing_pi2 hy) hn ?_)
    refine Hyps_cons (Dsem_fwd (.refl _) Eg HA) (Hyps_ext' hh (fun i => ?_))
    show tsub (prepend (y :: xs) ns) (tsub ρ (s (i + 1))) = _
    rw [tsub_comp]
    refine tsub_ext ?_ _
    intro k
    match k with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

/-- Rocq: `Analysis.Dialectica.R_impE`. -/
theorem R_impE {Γ : List Form} {A B : Form} (h1 : Real Γ (.imp A B)) (h2 : Real Γ A) : Real Γ B := by
  obtain ⟨t1, s1, ht1, hs1, H1⟩ := h1
  obtain ⟨t2, s2, ht2, hs2, H2⟩ := h2
  let FA := TAr (wty A) (wty B)
  let GA := TAr (wty A) (TAr (cty B) (cty A))
  let a := fun i => tsub (ysub (tpair (wty A) (cty B) (tsub shs t2) (var 0))) (s1 i)
  let b := fun i => tsub (ysub (app (cty B) (app (wty A) (pi2 FA GA (tsub shs t1)) (tsub shs t2)) (var 0))) (s2 i)
  have ha : ∀ i C, List.nthError Γ i = some C → Wt (sctx B Γ) (a i) (cty C) :=
    fun i C hC => wt_ysub (hs1 i C hC) (wt_tpair (wt_shs _ ht2) (wt_var' rfl))
  have hb : ∀ i C, List.nthError Γ i = some C → Wt (sctx B Γ) (b i) (cty C) :=
    fun i C hC => wt_ysub (hs2 i C hC)
      (.app _ _ _ _ (.app _ _ _ _ (wt_pi2 (wt_shs _ ht1)) (wt_shs _ ht2)) (wt_var' rfl))
  refine ⟨app (wty A) (pi1 FA GA t1) t2, mergeS Γ a b, .app _ _ _ _ (wt_pi1 ht1) ht2,
    fun i C hC => wt_mergeS _ hC (ha i C hC) (hb i C hC), ?_⟩
  intro xs y ns hx hy hn hh
  obtain ⟨hha, hhb⟩ := merge_sem hx hn (fun i C hC => inst_s (ha i C hC) hx hy hn) hh
  have ht1i : Typing [] (tsub (prepend xs ns) t1) (wty (.imp A B)) := inst_t ht1 hx hn
  have ht2i : Typing [] (tsub (prepend xs ns) t2) (wty A) := inst_t ht2 hx hn
  have HI : Dsem (.imp A B) (tsub (prepend xs ns) t1) (tpair (wty A) (cty B) (tsub (prepend xs ns) t2) y) ns :=
    H1 xs _ ns hx (.app _ _ _ _ (.app _ _ _ _ (.P _ _) ht2i) hy) hn
      (Hyps_ext' hha (fun i => inst_ysub_eq _ (by
        show tpair _ _ (tsub _ (tsub shs t2)) y = _
        rw [inst_shs])))
  have HA : Dsem A (tsub (prepend xs ns) t2)
      (app (cty B) (app (wty A) (pi2 FA GA (tsub (prepend xs ns) t1)) (tsub (prepend xs ns) t2)) y) ns :=
    H2 xs _ ns hx (.app _ _ _ _ (.app _ _ _ _ (typing_pi2 ht1i) ht2i) hy) hn
      (Hyps_ext' hhb (fun i => inst_ysub_eq _ (by
        show app _ (app _ (pi2 FA GA (tsub _ (tsub shs t1))) (tsub _ (tsub shs t2))) y = _
        rw [inst_shs, inst_shs])))
  have HI' := (D_imp A B ⟨ht1i, .app _ _ _ _ (.app _ _ _ _ (.P _ _) ht2i) hy, hn⟩).1 HI
  refine Dsem_fwd (star_app_r _ _ (star_pi1 _ _ _ _ _ _)) (star_pi2 _ _ _ _ _ _) (HI' ?_)
  exact Dsem_red (star_pi1 _ _ _ _ _ _)
    (star_app _ (star_app_r _ _ (star_pi1 _ _ _ _ _ _)) (star_pi2 _ _ _ _ _ _)) HA

/-! Context maps for a hypothesis added at the front. -/

/-- Rocq: `Analysis.Dialectica.xsub`. -/
def xsub (X : Term) : Nat → Term := prepend [var 0, tsub shs X] shs

/-- Rocq: `Analysis.Dialectica.inst_xsub`. -/
theorem inst_xsub (y : Term) (xs : List Term) (ns : Nat → Term) (X M : Term) :
    tsub (prepend (y :: xs) ns) (tsub (xsub X) M) = tsub (prepend (y :: tsub (prepend xs ns) X :: xs) ns) M := by
  rw [tsub_comp]
  refine tsub_ext ?_ _
  intro i
  match i with
  | 0 => rfl
  | 1 => exact inst_shs y xs ns X
  | _ + 2 => rfl

/-- Rocq: `Analysis.Dialectica.wt_xsub`. -/
theorem wt_xsub {C D : Form} {Γ : List Form} {X M : Term} {T : Ty} (h : Wt (sctx C (D :: Γ)) M T)
    (hX : Wt (hctx Γ) X (wty D)) : Wt (sctx C Γ) (tsub (xsub X) M) T :=
  wt_tsub h (fun | 0 => wt_var' rfl | 1 => wt_shs _ hX | _ + 2 => wt_var' rfl)

/-- Rocq: `Analysis.Dialectica.inst_hsub`. -/
theorem inst_hsub (xs : List Term) (ns : Nat → Term) (X M : Term) :
    tsub (prepend xs ns) (tsub (prepend [X] var) M) = tsub (prepend (tsub (prepend xs ns) X :: xs) ns) M := by
  rw [tsub_comp]
  refine tsub_ext ?_ _
  intro i
  match i with
  | 0 => rfl
  | _ + 1 => rfl

/-- Rocq: `Analysis.Dialectica.wt_hsub`. -/
theorem wt_hsub {D : Form} {Γ : List Form} {X M : Term} {T : Ty} (h : Wt (hctx (D :: Γ)) M T)
    (hX : Wt (hctx Γ) X (wty D)) : Wt (hctx Γ) (tsub (prepend [X] var) M) T :=
  wt_tsub h (fun | 0 => hX | _ + 1 => wt_var' rfl)

/-- Rocq: `Analysis.Dialectica.R_orE`. -/
theorem R_orE {Γ : List Form} {A B C : Form} (h0 : Real Γ (.disj A B)) (h1 : Real (A :: Γ) C)
    (h2 : Real (B :: Γ) C) : Real Γ C := by
  obtain ⟨t0, s0, ht0, hs0, H0⟩ := h0
  obtain ⟨t1, s1, ht1, hs1, H1⟩ := h1
  obtain ⟨t2, s2, ht2, hs2, H2⟩ := h2
  let WAB := TPr (wty A) (wty B)
  let xa := pi1 (wty A) (wty B) (pi2 TN WAB t0)
  let xb := pi2 (wty A) (wty B) (pi2 TN WAB t0)
  let zt := pi1 TN WAB t0
  have hxa : Wt (hctx Γ) xa (wty A) := wt_pi1 (wt_pi2 ht0)
  have hxb : Wt (hctx Γ) xb (wty B) := wt_pi2 (wt_pi2 ht0)
  have hzt : Wt (hctx Γ) zt TN := wt_pi1 ht0
  let ymain := tpair (cty A) (cty B) (tsub (xsub xa) (s1 0)) (tsub (xsub xb) (s2 0))
  let sm := fun i => tsub (ysub ymain) (s0 i)
  let sc := fun i => cond (cty (nthD Γ i .bot)) (tsub shs zt) (tsub (xsub xa) (s1 (i + 1)))
    (tsub (xsub xb) (s2 (i + 1)))
  have hym : Wt (sctx C Γ) ymain (cty (.disj A B)) :=
    wt_tpair (wt_xsub (hs1 0 A rfl) hxa) (wt_xsub (hs2 0 B rfl) hxb)
  have hsm : ∀ i D, List.nthError Γ i = some D → Wt (sctx C Γ) (sm i) (cty D) :=
    fun i D hD => wt_ysub (hs0 i D hD) hym
  have hsc : ∀ i D, List.nthError Γ i = some D → Wt (sctx C Γ) (sc i) (cty D) := by
    intro i D hD
    show Wt _ (cond (cty (nthD Γ i .bot)) _ _ _) _
    rw [nthError_nthD hD]
    exact wt_cond (wt_shs _ hzt) (wt_xsub (hs1 (i + 1) D hD) hxa) (wt_xsub (hs2 (i + 1) D hD) hxb)
  refine ⟨cond (wty C) zt (tsub (prepend [xa] var) t1) (tsub (prepend [xb] var) t2), mergeS Γ sm sc,
    wt_cond hzt (wt_hsub ht1 hxa) (wt_hsub ht2 hxb), fun i D hD => wt_mergeS _ hD (hsm i D hD) (hsc i D hD), ?_⟩
  intro xs y ns hx hy hn hh
  obtain ⟨hhm, hhc⟩ := merge_sem hx hn (fun i D hD => inst_s (hsm i D hD) hx hy hn) hh
  have ht0i : Typing [] (tsub (prepend xs ns) t0) (wty (.disj A B)) := inst_t ht0 hx hn
  have hymi : Typing [] (tsub (prepend (y :: xs) ns) ymain) (cty (.disj A B)) := inst_s hym hx hy hn
  have HO : Dsem (.disj A B) (tsub (prepend xs ns) t0) (tsub (prepend (y :: xs) ns) ymain) ns :=
    H0 xs _ ns hx hymi hn (Hyps_ext' hhm (fun i => inst_ysub y xs ns ymain (s0 i)))
  have hxai : Typing [] (tsub (prepend xs ns) xa) (wty A) := inst_t hxa hx hn
  have hxbi : Typing [] (tsub (prepend xs ns) xb) (wty B) := inst_t hxb hx hn
  rcases (D_or A B ⟨ht0i, hymi, hn⟩).1 HO with ⟨hz, HA⟩ | ⟨⟨m, hm⟩, HB⟩
  · refine Dsem_red (cond_0 _ _ _ hz) (.refl _) ?_
    rw [inst_hsub]
    refine H1 _ y ns (XT_cons hxai hx) hy hn (Hyps_cons ?_ ?_)
    · show Dsem A _ (tsub (prepend (y :: tsub (prepend xs ns) xa :: xs) ns) (s1 0)) ns
      rw [← inst_xsub]
      exact Dsem_fwd (.refl _) (star_pi1 _ _ _ _ _ _) HA
    · intro i D hD
      have hc := hhc i D hD
      have hc' : Dsem D (nthD xs i Zc) (tsub (prepend (y :: xs) ns)
          (cond (cty (nthD Γ i .bot)) (tsub shs zt) (tsub (xsub xa) (s1 (i + 1)))
            (tsub (xsub xb) (s2 (i + 1))))) ns := hc
      rw [tsub_cond, inst_shs, inst_xsub] at hc'
      exact Dsem_fwd (.refl _) (cond_0 _ _ _ hz) hc'
  · refine Dsem_red (cond_S _ _ _ hm) (.refl _) ?_
    rw [inst_hsub]
    refine H2 _ y ns (XT_cons hxbi hx) hy hn (Hyps_cons ?_ ?_)
    · show Dsem B _ (tsub (prepend (y :: tsub (prepend xs ns) xb :: xs) ns) (s2 0)) ns
      rw [← inst_xsub]
      exact Dsem_fwd (.refl _) (star_pi2 _ _ _ _ _ _) HB
    · intro i D hD
      have hc := hhc i D hD
      have hc' : Dsem D (nthD xs i Zc) (tsub (prepend (y :: xs) ns)
          (cond (cty (nthD Γ i .bot)) (tsub shs zt) (tsub (xsub xa) (s1 (i + 1)))
            (tsub (xsub xb) (s2 (i + 1))))) ns := hc
      rw [tsub_cond, inst_shs, inst_xsub, inst_xsub] at hc'
      exact Dsem_fwd (.refl _) (cond_S _ _ _ hm) hc'

/-! Inserting a number variable after the hypotheses. -/

/-- Rocq: `Analysis.Dialectica.prepend_lt_indep`. -/
theorem prepend_lt_indep {X : Type} : ∀ (xs : List X) (f g : Nat → X) (k : Nat), k < xs.length →
    prepend xs f k = prepend xs g k
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, _, 0, _ => rfl
  | _ :: xs, f, g, k + 1, h => prepend_lt_indep xs f g k (Nat.lt_of_succ_lt_succ h)

theorem exists_add_of_lt : ∀ {n k : Nat}, n < k → ∃ j, k = n + j + 1
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, k + 1, _ => ⟨k, by rw [Nat.zero_add]⟩
  | n + 1, k + 1, h =>
    let ⟨j, e⟩ := exists_add_of_lt (Nat.lt_of_succ_lt_succ h)
    ⟨j, by rw [e, Nat.add_right_comm n 1 j]⟩

theorem ins_spec {X : Type} (n : Nat) (a : X) (f : Nat → X) (k : Nat) :
    (k < n ∧ ins n a f k = f k) ∨ (k = n ∧ ins n a f k = a) ∨
      (∃ j, k = n + j + 1 ∧ ins n a f k = f (n + j)) := by
  by_cases h1 : k < n
  · exact .inl ⟨h1, ite_eq_left h1⟩
  · by_cases h2 : k = n
    · exact .inr (.inl ⟨h2, (ite_eq_right h1).trans (ite_eq_left h2)⟩)
    · obtain ⟨j, rfl⟩ := exists_add_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) (fun e => h2 e.symm))
      exact .inr (.inr ⟨j, rfl, (ite_eq_right h1).trans (ite_eq_right h2)⟩)

/-- Rocq: `Analysis.Dialectica.ins_prepend`. -/
theorem ins_prepend {X : Type} (xs : List X) (ns : Nat → X) (a : X) (k : Nat) :
    ins xs.length a (prepend xs ns) k = prepend xs (prepend [a] ns) k := by
  rcases ins_spec xs.length a (prepend xs ns) k with ⟨h, e⟩ | ⟨rfl, e⟩ | ⟨j, rfl, e⟩
  · rw [e]; exact prepend_lt_indep xs _ _ k h
  · rw [e]; exact (prepend_ge xs (prepend [a] ns) 0).symm
  · rw [e, prepend_ge]; exact (prepend_ge xs (prepend [a] ns) (j + 1)).symm

/-- Rocq: `Analysis.Dialectica.tsub_ins`. -/
theorem tsub_ins (ρ : Nat → Term) (n : Nat) (a : Term) (f : Nat → Term) (k : Nat) :
    tsub ρ (ins n a f k) = ins n (tsub ρ a) (fun k => tsub ρ (f k)) k := by
  show tsub ρ (if k < n then f k else if k = n then a else f (Nat.pred k)) =
    (if k < n then tsub ρ (f k) else if k = n then tsub ρ a else tsub ρ (f (Nat.pred k)))
  by_cases h1 : k < n
  · rw [ite_eq_left h1, ite_eq_left h1]
  · by_cases h2 : k = n
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h2]

/-- Rocq: `Analysis.Dialectica.ins_ext`. -/
theorem ins_ext {X : Type} (n : Nat) (a : X) {f g : Nat → X} (h : ∀ k, f k = g k) (k : Nat) :
    ins n a f k = ins n a g k := by
  show (if k < n then f k else if k = n then a else f (Nat.pred k)) =
    (if k < n then g k else if k = n then a else g (Nat.pred k))
  rw [h k, h (Nat.pred k)]

/-- Rocq: `Analysis.Dialectica.wt_ins`. -/
theorem wt_ins {Δ Γ : Nat → Ty} {n : Nat} {a : Term} {f : Nat → Term}
    (h1 : ∀ k, k < n → Wt Δ (f k) (Γ k)) (h2 : Wt Δ a (Γ n))
    (h3 : ∀ j, Wt Δ (f (n + j)) (Γ (n + j + 1))) : ∀ k, Wt Δ (ins n a f k) (Γ k) := by
  intro k
  rcases ins_spec n a f k with ⟨h, e⟩ | ⟨rfl, e⟩ | ⟨j, rfl, e⟩
  · rw [e]; exact h1 k h
  · rw [e]; exact h2
  · rw [e]; exact h3 j

/-- Rocq: `Analysis.Dialectica.hctx_shift`. -/
theorem hctx_shift (Γ : List Form) : hctx (Γ.map fshift) = hctx Γ := by
  unfold hctx
  rw [map_map, map_ext (f := fun x => wty (fshift x)) (g := wty) (fun A => wty_subst A shiftSub) Γ]

/-- Rocq: `Analysis.Dialectica.sctx_shift`. -/
theorem sctx_shift (A : Form) (Γ : List Form) : sctx A (Γ.map fshift) = sctx A Γ := by
  unfold sctx
  rw [map_map, map_ext (f := fun x => wty (fshift x)) (g := wty) (fun A => wty_subst A shiftSub) Γ]

/-- Rocq: `Analysis.Dialectica.XT_shift`. -/
theorem XT_shift {Γ : List Form} {xs : List Term} (h : XT Γ xs) : XT (Γ.map fshift) xs := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (by show Typing [] _ (wty (fshift _)); rw [fshift, wty_subst]; exact hx) ih

/-- Rocq: `Analysis.Dialectica.XT_unshift`. -/
theorem XT_unshift : ∀ {Γ : List Form} {xs : List Term}, XT (Γ.map fshift) xs → XT Γ xs
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    cases h with
    | cons hx h' =>
      refine .cons ?_ (XT_unshift h')
      have hx' : Typing [] _ (wty (fsubst shiftSub _)) := hx
      rw [wty_subst] at hx'
      exact hx'

/-- Rocq: `Analysis.Dialectica.nth_error_shift`. -/
theorem nthError_shift : ∀ {Γ : List Form} {i : Nat} {D : Form}, List.nthError (Γ.map fshift) i = some D →
    ∃ D', D = fshift D' ∧ List.nthError Γ i = some D'
  | _ :: _, 0, _, h => by cases h; exact ⟨_, rfl, rfl⟩
  | _ :: Γ, i + 1, _, h => nthError_shift (Γ := Γ) (i := i) h

/-- Rocq: `Analysis.Dialectica.nth_error_shift'`. -/
theorem nthError_shift' : ∀ {Γ : List Form} {i : Nat} {D : Form}, List.nthError Γ i = some D →
    List.nthError (Γ.map fshift) i = some (fshift D)
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: Γ, i + 1, _, h => nthError_shift' (Γ := Γ) (i := i) h

/-- Rocq: `Analysis.Dialectica.D_shift1`. -/
theorem D_shift1 (A : Form) (x y z : Term) (ns : Nat → Term) :
    Dsem (fshift A) x y (prepend [z] ns) ↔ Dsem A x y ns :=
  (D_shift A x y _).trans (Dsem_ext A x y (fun _ => rfl))

/-- Rocq: `Analysis.Dialectica.Ns_star`. -/
theorem Ns_star (ns : Nat → Term) {z z' : Term} (h : Star z z') :
    ∀ j, Star (prepend [z] ns j) (prepend [z'] ns j)
  | 0 => h
  | _ + 1 => .refl _

theorem rem_hctx (Γ : List Form) (k : Nat) : rem Γ.length (hctx Γ) k = hctx Γ k := by
  by_cases h : k < Γ.length
  · exact ite_eq_left h
  · refine (ite_eq_right h).trans ?_
    rw [hctx_ge Γ (Nat.le_succ_of_le (Nat.le_of_not_lt h)), hctx_ge Γ (Nat.le_of_not_lt h)]

/-- Rocq: `Analysis.Dialectica.R_allI`. -/
theorem R_allI {Γ : List Form} {A : Form} (h : Real (Γ.map fshift) A) : Real Γ (.all A) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  rw [hctx_shift] at ht
  let ρ := prepend [pi2 TN (cty A) (var 0)] (ins Γ.length (pi1 TN (cty A) (var 0)) shs)
  refine ⟨lamAt (hctx Γ) Γ.length t, fun i => tsub ρ (s i), ?_, ?_, ?_⟩
  · have := wt_lam_at Γ.length ht
    rw [hctx_ge Γ (Nat.le_refl _)] at this
    exact wt_ext (rem_hctx Γ) this
  · intro i D hD
    have hsi : Wt (sctx A Γ) (s i) (cty D) := by
      have := hs i (fshift D) (nthError_shift' hD)
      rw [sctx_shift] at this
      exact (cty_subst D shiftSub) ▸ this
    refine wt_tsub hsi ?_
    intro k
    match k with
    | 0 => exact wt_pi2 (wt_var' rfl)
    | k + 1 =>
      show Wt _ (ins Γ.length _ shs k) (hctx Γ k)
      refine wt_ins (Δ := sctx (.all A) Γ) (Γ := hctx Γ) (fun k _ => wt_var' rfl) ?_ (fun j => wt_var' ?_) k
      · rw [hctx_ge Γ (Nat.le_refl _)]; exact wt_pi1 (wt_var' rfl)
      · show hctx Γ (Γ.length + j) = hctx Γ (Γ.length + j + 1)
        rw [hctx_ge Γ (Nat.le_add_right _ _), hctx_ge Γ (Nat.le_succ_of_le (Nat.le_add_right _ _))]
  · intro xs y ns hx hy hn hh
    have hlen := XT_length hx
    have hz : Typing [] (pi1 TN (cty A) y) TN := typing_pi1 hy
    refine (D_all A _ y ns).2 (Dsem_red (star_lam_at _ Γ.length t (prepend xs ns) _ _) (.refl _) ?_)
    have e : tsub (ins Γ.length (pi1 TN (cty A) y) (prepend xs ns)) t =
        tsub (prepend xs (prepend [pi1 TN (cty A) y] ns)) t := by
      refine tsub_ext ?_ t
      intro k
      show ins Γ.length _ _ k = _
      rw [← hlen]; exact ins_prepend xs ns _ k
    rw [e]
    refine H xs _ _ (XT_shift hx) (typing_pi2 hy) (Ns_cons hz hn) ?_
    intro i D' hD'
    obtain ⟨D, rfl, hD⟩ := nthError_shift hD'
    refine (D_shift1 D _ _ _ ns).2 ?_
    have hhi := hh i D hD
    have e2 : tsub (prepend (y :: xs) ns) (tsub ρ (s i)) =
        tsub (prepend (pi2 TN (cty A) y :: xs) (prepend [pi1 TN (cty A) y] ns)) (s i) := by
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro k
      match k with
      | 0 => rfl
      | k + 1 =>
        show tsub (prepend (y :: xs) ns) (ins Γ.length (pi1 TN (cty A) (var 0)) shs k) = prepend xs _ k
        rw [tsub_ins]
        refine (ins_ext Γ.length _ (g := prepend xs ns) (fun _ => rfl) k).trans ?_
        rw [← hlen]; exact ins_prepend xs ns (pi1 TN (cty A) y) k
    have hhi' : Dsem D (nthD xs i Zc) (tsub (prepend (y :: xs) ns) (tsub ρ (s i))) ns := hhi
    rw [e2] at hhi'
    exact hhi'

/-- Rocq: `Analysis.Dialectica.wt_tr_at`. -/
theorem wt_tr_at {Γ : Nat → Ty} {k : Nat} (h : ∀ j, Γ (k + j) = TN) (t : ATerm) :
    Wt Γ (tsub (fun j => var (k + j)) (tr t)) TN :=
  wt_tsub (wt_tr (Γ := TN0) (fun _ => rfl) t) (fun j => wt_var' (h j))

/-- Rocq: `Analysis.Dialectica.inst_tr_at`. -/
theorem inst_tr_at (xs : List Term) (ns : Nat → Term) (t : ATerm) :
    tsub (prepend xs ns) (tsub (fun j => var (xs.length + j)) (tr t)) = tsub ns (tr t) := by
  rw [tsub_comp]
  refine tsub_ext ?_ _
  intro j
  exact prepend_ge xs ns j

theorem inst_tr_at' (y : Term) (xs : List Term) (ns : Nat → Term) (t : ATerm) :
    tsub (prepend (y :: xs) ns) (tsub (fun j => var (xs.length + j + 1)) (tr t)) = tsub ns (tr t) := by
  rw [tsub_comp]
  refine tsub_ext ?_ _
  intro j
  exact prepend_ge xs ns j

/-- Rocq: `Analysis.Dialectica.R_allE`. -/
theorem R_allE {Γ : List Form} {A : Form} (r : ATerm) (h : Real Γ (.all A)) : Real Γ (sub1 A r) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  have hrt : Wt (hctx Γ) (tsub (fun j => var (Γ.length + j)) (tr r)) TN :=
    wt_tr_at (fun _ => hctx_ge Γ (Nat.le_add_right _ _)) r
  have hrts : Wt (sctx (sub1 A r) Γ) (tsub (fun j => var (Γ.length + j + 1)) (tr r)) TN :=
    wt_tsub (wt_tr (Γ := TN0) (fun _ => rfl) r) (fun j => wt_var' (hctx_ge Γ (Nat.le_add_right _ j)))
  refine ⟨app TN t (tsub (fun j => var (Γ.length + j)) (tr r)),
    fun i => tsub (ysub (tpair TN (cty A) (tsub (fun j => var (Γ.length + j + 1)) (tr r)) (var 0))) (s i),
    ?_, ?_, ?_⟩
  · show Wt _ _ (wty (fsubst _ A)); rw [wty_subst]; exact .app _ _ _ _ ht hrt
  · intro i D hD
    exact wt_ysub (A' := .all A) (hs i D hD) (wt_tpair hrts (wt_var' (cty_subst A _)))
  · intro xs y ns hx hy hn hh
    have hlen := XT_length hx
    have hrr : Typing [] (tsub ns (tr r)) TN := typing_tr r hn
    have Erts : tsub (prepend (y :: xs) ns) (tsub (fun j => var (Γ.length + j + 1)) (tr r)) = tsub ns (tr r) := by
      rw [← hlen]; exact inst_tr_at' y xs ns r
    have Ert : tsub (prepend xs ns) (tsub (fun j => var (Γ.length + j)) (tr r)) = tsub ns (tr r) := by
      rw [← hlen]; exact inst_tr_at xs ns r
    have hy' : Typing [] y (cty A) := by
      have h' : Typing [] y (cty (fsubst (inst1 r) A)) := hy
      rw [cty_subst] at h'; exact h'
    have HA : Dsem (.all A) (tsub (prepend xs ns) t) (tpair TN (cty A) (tsub ns (tr r)) y) ns :=
      H xs _ ns hx (.app _ _ _ _ (.app _ _ _ _ (.P _ _) hrr) hy') hn
        (Hyps_ext' hh (fun i => inst_ysub_eq _ (by
          show tpair _ _ (tsub _ (tsub (fun j => var (Γ.length + j + 1)) (tr r))) y = _
          rw [Erts])))
    have HA' := (D_all A _ _ ns).1 HA
    refine (D_sub1 A r _ y ns).2 ?_
    show Dsem A (app TN (tsub (prepend xs ns) t) (tsub (prepend xs ns) (tsub _ (tr r)))) y _
    rw [Ert]
    exact (Dsem_star A (star_app_r _ _ (star_pi1 _ _ _ _ _ _)) (star_pi2 _ _ _ _ _ _)
      (Ns_star ns (star_pi1 _ _ _ _ _ _))).1 HA'

/-- Rocq: `Analysis.Dialectica.R_exI`. -/
theorem R_exI {Γ : List Form} {A : Form} (r : ATerm) (h : Real Γ (sub1 A r)) : Real Γ (.ex A) := by
  obtain ⟨t, s, ht, hs, H⟩ := h
  have hrt : Wt (hctx Γ) (tsub (fun j => var (Γ.length + j)) (tr r)) TN :=
    wt_tr_at (fun _ => hctx_ge Γ (Nat.le_add_right _ _)) r
  have ES : sctx (sub1 A r) Γ = sctx (.ex A) Γ := by
    unfold sctx; show prepend (cty (fsubst _ A) :: _) TN0 = _; rw [cty_subst]; rfl
  refine ⟨tpair TN (wty A) (tsub (fun j => var (Γ.length + j)) (tr r)) t, s, ?_, ?_, ?_⟩
  · have ht' : Wt (hctx Γ) t (wty (fsubst (inst1 r) A)) := ht
    rw [wty_subst] at ht'
    exact wt_tpair hrt ht'
  · intro i D hD; rw [← ES]; exact hs i D hD
  · intro xs y ns hx hy hn hh
    have hlen := XT_length hx
    have Ert : tsub (prepend xs ns) (tsub (fun j => var (Γ.length + j)) (tr r)) = tsub ns (tr r) := by
      rw [← hlen]; exact inst_tr_at xs ns r
    have hy' : Typing [] y (cty (sub1 A r)) := by
      show Typing [] y (cty (fsubst _ A)); rw [cty_subst]; exact hy
    have HA := (D_sub1 A r _ y ns).1 (H xs y ns hx hy' hn hh)
    refine (D_ex A _ y ns).2 ((Dsem_star A (star_pi2 _ _ _ _ _ _) (.refl _) ?_).2 HA)
    intro j
    match j with
    | 0 =>
      show Star (pi1 TN (wty A) (tpair TN (wty A) (tsub (prepend xs ns) (tsub _ (tr r))) _)) _
      rw [Ert]; exact star_pi1 _ _ _ _ _ _
    | _ + 1 => exact .refl _

/-- Rocq: `Analysis.Dialectica.R_exE`. -/
theorem R_exE {Γ : List Form} {A B : Form} (h0 : Real Γ (.ex A)) (h1 : Real (A :: Γ.map fshift) (fshift B)) :
    Real Γ B := by
  obtain ⟨t0, s0, ht0, hs0, H0⟩ := h0
  obtain ⟨t1, s1, ht1, hs1, H1⟩ := h1
  have hxa : Wt (hctx Γ) (pi2 TN (wty A) t0) (wty A) := wt_pi2 ht0
  have hzt : Wt (hctx Γ) (pi1 TN (wty A) t0) TN := wt_pi1 ht0
  let σ := prepend [pi2 TN (wty A) t0] (ins Γ.length (pi1 TN (wty A) t0) var)
  let τ := prepend [var 0, tsub shs (pi2 TN (wty A) t0)] (ins Γ.length (tsub shs (pi1 TN (wty A) t0)) shs)
  have hτ : ∀ M T, Wt (sctx (fshift B) (A :: Γ.map fshift)) M T → Wt (sctx B Γ) (tsub τ M) T := by
    intro M T hM
    refine wt_tsub hM ?_
    intro k
    match k with
    | 0 => exact wt_var' (cty_subst B shiftSub).symm
    | 1 => exact wt_shs _ hxa
    | k + 2 =>
      show Wt _ (ins Γ.length _ shs k) (hctx (Γ.map fshift) k)
      rw [hctx_shift]
      refine wt_ins (Δ := sctx B Γ) (Γ := hctx Γ) (fun k _ => wt_var' rfl) ?_ (fun j => wt_var' ?_) k
      · rw [hctx_ge Γ (Nat.le_refl _)]; exact wt_shs _ hzt
      · show hctx Γ (Γ.length + j) = hctx Γ (Γ.length + j + 1)
        rw [hctx_ge Γ (Nat.le_add_right _ _), hctx_ge Γ (Nat.le_succ_of_le (Nat.le_add_right _ _))]
  let sm := fun i => tsub (ysub (tsub τ (s1 0))) (s0 i)
  let ss := fun i => tsub τ (s1 (i + 1))
  have hsm : ∀ i D, List.nthError Γ i = some D → Wt (sctx B Γ) (sm i) (cty D) :=
    fun i D hD => wt_ysub (hs0 i D hD) (hτ _ _ (hs1 0 A rfl))
  have hss : ∀ i D, List.nthError Γ i = some D → Wt (sctx B Γ) (ss i) (cty D) := by
    intro i D hD
    have := hτ _ _ (hs1 (i + 1) (fshift D) (nthError_shift' hD))
    exact (cty_subst D shiftSub) ▸ this
  refine ⟨tsub σ t1, mergeS Γ sm ss, ?_, fun i D hD => wt_mergeS _ hD (hsm i D hD) (hss i D hD), ?_⟩
  · have ht1' : Wt (hctx (A :: Γ.map fshift)) t1 (wty B) := by
      have h' : Wt (hctx (A :: Γ.map fshift)) t1 (wty (fsubst shiftSub B)) := ht1
      rw [wty_subst] at h'; exact h'
    refine wt_tsub ht1' ?_
    intro k
    match k with
    | 0 => exact hxa
    | k + 1 =>
      show Wt _ (ins Γ.length _ var k) (hctx (Γ.map fshift) k)
      rw [hctx_shift]
      refine wt_ins (Δ := hctx Γ) (Γ := hctx Γ) (fun k _ => wt_var' rfl) ?_ (fun j => wt_var' ?_) k
      · rw [hctx_ge Γ (Nat.le_refl _)]; exact hzt
      · show hctx Γ (Γ.length + j) = hctx Γ (Γ.length + j + 1)
        rw [hctx_ge Γ (Nat.le_add_right _ _), hctx_ge Γ (Nat.le_succ_of_le (Nat.le_add_right _ _))]
  · intro xs y ns hx hy hn hh
    have hlen := XT_length hx
    obtain ⟨hhm, hhs⟩ := merge_sem hx hn (fun i D hD => inst_s (hsm i D hD) hx hy hn) hh
    have ht0i : Typing [] (tsub (prepend xs ns) t0) (wty (.ex A)) := inst_t ht0 hx hn
    have hxai : Typing [] (pi2 TN (wty A) (tsub (prepend xs ns) t0)) (wty A) := typing_pi2 ht0i
    have hzti : Typing [] (pi1 TN (wty A) (tsub (prepend xs ns) t0)) TN := typing_pi1 ht0i
    have Eτ : ∀ M, tsub (prepend (y :: xs) ns) (tsub τ M) =
        tsub (prepend (y :: pi2 TN (wty A) (tsub (prepend xs ns) t0) :: xs)
          (prepend [pi1 TN (wty A) (tsub (prepend xs ns) t0)] ns)) M := by
      intro M
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro k
      match k with
      | 0 => rfl
      | 1 => exact inst_shs _ _ _ _
      | k + 2 =>
        show tsub (prepend (y :: xs) ns) (ins Γ.length (tsub shs (pi1 TN (wty A) t0)) shs k) = prepend xs _ k
        rw [tsub_ins, inst_shs]
        refine (ins_ext Γ.length _ (g := prepend xs ns) (fun _ => rfl) k).trans ?_
        rw [← hlen]; exact ins_prepend xs ns _ k
    have Eσ : tsub (prepend xs ns) (tsub σ t1) =
        tsub (prepend (pi2 TN (wty A) (tsub (prepend xs ns) t0) :: xs)
          (prepend [pi1 TN (wty A) (tsub (prepend xs ns) t0)] ns)) t1 := by
      rw [tsub_comp]
      refine tsub_ext ?_ _
      intro k
      match k with
      | 0 => rfl
      | k + 1 =>
        show tsub (prepend xs ns) (ins Γ.length (pi1 TN (wty A) t0) var k) = prepend xs _ k
        rw [tsub_ins]
        refine (ins_ext Γ.length _ (g := prepend xs ns) (fun _ => rfl) k).trans ?_
        rw [← hlen]; exact ins_prepend xs ns _ k
    have hyi : Typing [] (tsub (prepend (y :: xs) ns) (tsub τ (s1 0))) (cty A) :=
      inst_s (hτ _ _ (hs1 0 A rfl)) hx hy hn
    have HE : Dsem (.ex A) (tsub (prepend xs ns) t0) (tsub (prepend (y :: xs) ns) (tsub τ (s1 0))) ns :=
      H0 xs _ ns hx hyi hn (Hyps_ext' hhm (fun i => inst_ysub y xs ns _ (s0 i)))
    have HE' := (D_ex A _ _ ns).1 HE
    rw [Eτ] at HE'
    rw [Eσ]
    refine (D_shift1 B _ y _ ns).1 (H1 _ y _ (XT_cons hxai (XT_shift hx))
      (by show Typing [] y (cty (fsubst _ B)); rw [cty_subst]; exact hy) (Ns_cons hzti hn) (Hyps_cons HE' ?_))
    intro i D' hD'
    obtain ⟨D, rfl, hD⟩ := nthError_shift hD'
    refine (D_shift1 D _ _ _ ns).2 ?_
    have hsi : Dsem D (nthD xs i Zc) (tsub (prepend (y :: xs) ns) (tsub τ (s1 (i + 1)))) ns := hhs i D hD
    rw [Eτ] at hsi
    exact hsi

/-- Axioms with trivial realizers. Rocq: `Analysis.Dialectica.R_axiom`. -/
theorem R_axiom (Γ : List Form) {A : Form} (h : ∀ x y ns, DT A x y ns → Dsem A x y ns) : Real Γ A :=
  ⟨zero (wty A), zeros Γ, wt_zero _ _, fun _ _ hB => wt_zeros A hB, fun _ y ns _ hy hn _ => by
    rw [tsub_zero]; exact h _ y ns ⟨typing_zero _, hy, hn⟩⟩

/-- Rocq: `Analysis.Dialectica.tr_value`. -/
theorem tr_value {ns : Nat → Term} (t : ATerm) (hn : Ns ns) : ∃ k, Star (tsub ns (tr t)) (num k) :=
  T_eval (typing_tr t hn)

/-- Rocq: `Analysis.Dialectica.R_refl`. -/
theorem R_refl (Γ : List Form) (t : ATerm) : Real Γ (.eq t t) :=
  R_axiom Γ fun x y _ ⟨_, _, hn⟩ =>
    (D_eq t t x y hn).2 (let ⟨k, hk⟩ := tr_value t hn; ⟨k, hk, hk⟩)

/-- Rocq: `Analysis.Dialectica.R_plus0`. -/
theorem R_plus0 (Γ : List Form) (t : ATerm) : Real Γ (.eq (.tplus t .tz) t) :=
  R_axiom Γ fun x y _ ⟨_, _, hn⟩ =>
    (D_eq _ t x y hn).2 (let ⟨k, hk⟩ := tr_value t hn; ⟨k, (addT_eval hk (.refl (num 0)) : Star _ (num (k + 0))), hk⟩)

/-- Rocq: `Analysis.Dialectica.R_plusS`. -/
theorem R_plusS (Γ : List Form) (s t : ATerm) : Real Γ (.eq (.tplus s (.ts t)) (.ts (.tplus s t))) :=
  R_axiom Γ fun x y _ ⟨_, _, hn⟩ =>
    (D_eq _ _ x y hn).2
      (let ⟨a, ha⟩ := tr_value s hn
       let ⟨b, hb⟩ := tr_value t hn
       ⟨a + b + 1, (addT_eval ha (star_app_r TN Suc hb : Star _ (num (b + 1))) : Star _ (num (a + (b + 1)))),
         (star_app_r TN Suc (addT_eval ha hb) : Star _ (num (a + b + 1)))⟩)

/-- Rocq: `Analysis.Dialectica.R_mult0`. -/
theorem R_mult0 (Γ : List Form) (t : ATerm) : Real Γ (.eq (.tmult t .tz) .tz) :=
  R_axiom Γ fun x y _ ⟨_, _, hn⟩ =>
    (D_eq _ _ x y hn).2 (let ⟨k, hk⟩ := tr_value t hn; ⟨0, (mulT_eval hk (.refl (num 0)) : Star _ (num (k * 0))), .refl _⟩)

/-- Rocq: `Analysis.Dialectica.R_multS`. -/
theorem R_multS (Γ : List Form) (s t : ATerm) :
    Real Γ (.eq (.tmult s (.ts t)) (.tplus (.tmult s t) s)) :=
  R_axiom Γ fun x y _ ⟨_, _, hn⟩ =>
    (D_eq _ _ x y hn).2
      (let ⟨a, ha⟩ := tr_value s hn
       let ⟨b, hb⟩ := tr_value t hn
       ⟨a * b + a, (mulT_eval ha (star_app_r TN Suc hb : Star _ (num (b + 1))) : Star _ (num (a * (b + 1)))),
         (addT_eval (mulT_eval ha hb) ha : Star _ (num (a * b + a)))⟩)

/-- Rocq: `Analysis.Dialectica.R_succ_ne`. -/
theorem R_succ_ne (Γ : List Form) (t : ATerm) : Real Γ (Form.eq (.ts t) .tz).neg :=
  R_axiom Γ fun _ _ ns hT => (D_imp _ _ hT).2 fun HE => by
    obtain ⟨_, _, hn⟩ := hT
    obtain ⟨m, h1, h2⟩ := (D_eq _ _ _ _ hn).1 HE
    have e : m = 0 := num_inj (star_from_num (n := 0) h2)
    subst e
    obtain ⟨k, hk⟩ := tr_value t hn
    have hk' : Star (tsub ns (tr (.ts t))) (num (k + 1)) := star_app_r TN Suc hk
    exact Nat.noConfusion (star_num_unique hk' h1)

/-- Rocq: `Analysis.Dialectica.R_succ_inj`. -/
theorem R_succ_inj {Γ : List Form} {s t : ATerm} (h : Real Γ (.eq (.ts s) (.ts t))) : Real Γ (.eq s t) := by
  obtain ⟨t0, s0, ht, hs, H⟩ := h
  refine ⟨t0, s0, ht, hs, fun xs y ns hx hy hn hh => ?_⟩
  obtain ⟨m, h1, h2⟩ := (D_eq _ _ _ _ hn).1 (H xs y ns hx hy hn hh)
  refine (D_eq _ _ _ _ hn).2 ?_
  obtain ⟨a, ha⟩ := tr_value s hn
  obtain ⟨b, hb⟩ := tr_value t hn
  have ha' : Star (tsub ns (tr (.ts s))) (num (a + 1)) := star_app_r TN Suc ha
  have hb' : Star (tsub ns (tr (.ts t))) (num (b + 1)) := star_app_r TN Suc hb
  have e1 := star_num_unique ha' h1
  have e2 := star_num_unique hb' h2
  have e : a = b := Nat.succ.inj (e1.trans e2.symm)
  subst e
  exact ⟨a, ha, hb⟩

/-- Rocq: `Analysis.Dialectica.sctx_cty`. -/
theorem sctx_cty {A A' : Form} (Γ : List Form) (E : cty A = cty A') : sctx A Γ = sctx A' Γ := by
  unfold sctx; rw [E]

/-- Rocq: `Analysis.Dialectica.R_leib`. -/
theorem R_leib {Γ : List Form} {A : Form} {a b : ATerm} (h1 : Real Γ (.eq a b)) (h2 : Real Γ (sub1 A a)) :
    Real Γ (sub1 A b) := by
  obtain ⟨t1, s1, _, hs1, H1⟩ := h1
  obtain ⟨t2, s2, ht2, hs2, H2⟩ := h2
  have EW : wty (sub1 A a) = wty (sub1 A b) := (wty_subst A _).trans (wty_subst A _).symm
  have EC : cty (sub1 A a) = cty (sub1 A b) := (cty_subst A _).trans (cty_subst A _).symm
  let sa := fun i => tsub (ysub Zc) (s1 i)
  have hsa : ∀ i D, List.nthError Γ i = some D → Wt (sctx (sub1 A b) Γ) (sa i) (cty D) :=
    fun i D hD => wt_ysub (A' := .eq a b) (hs1 i D hD) .Z
  have hs2' : ∀ i D, List.nthError Γ i = some D → Wt (sctx (sub1 A b) Γ) (s2 i) (cty D) := by
    intro i D hD; rw [← sctx_cty Γ EC]; exact hs2 i D hD
  refine ⟨t2, mergeS Γ sa s2, EW ▸ ht2, fun i D hD => wt_mergeS _ hD (hsa i D hD) (hs2' i D hD), ?_⟩
  intro xs y ns hx hy hn hh
  obtain ⟨hha, hhb⟩ := merge_sem hx hn (fun i C hC => inst_s (hsa i C hC) hx hy hn) hh
  have HE : Dsem (.eq a b) (tsub (prepend xs ns) t1) Zc ns :=
    H1 xs Zc ns hx .Z hn (Hyps_ext' hha (fun i => inst_ysub y xs ns Zc (s1 i)))
  obtain ⟨m, ham, hbm⟩ := (D_eq _ _ _ _ hn).1 HE
  have HA := (D_sub1 A a _ y ns).1 (H2 xs y ns hx (EC ▸ hy) hn hhb)
  refine (D_sub1 A b _ y ns).2 ((Dsem_star A (.refl _) (.refl _) (Ns_star ns hbm)).2 ?_)
  exact (Dsem_star A (.refl _) (.refl _) (Ns_star ns ham)).1 HA

/-- Induction: the witness of `∀x A` is defined by the recursor, at the type
of the witnesses of `A`. Rocq: `Analysis.Dialectica.R_ind`. -/
theorem R_ind (Γ : List Form) {A : Form} (h0 : Real [] (sub1 A .tz)) (h1 : Real [A] (fsubst sucSub A)) :
    Real Γ (.all A) := by
  obtain ⟨t0, _, ht0, _, H0⟩ := h0
  obtain ⟨t1, s1, ht1, hs1, H1⟩ := h1
  have ht0' : Wt (hctx []) t0 (wty A) := by
    have h' : Wt (hctx []) t0 (wty (fsubst (inst1 .tz) A)) := ht0
    rw [wty_subst] at h'; exact h'
  have ht1' : Wt (hctx [A]) t1 (wty A) := by
    have h' : Wt (hctx [A]) t1 (wty (fsubst sucSub A)) := ht1
    rw [wty_subst] at h'; exact h'
  let C2 := prepend [wty A, TN] (hctx Γ)
  let base := tsub (fun j => var (Γ.length + j + 1)) t0
  let M := tsub (dsub (var 0) (var 1) (fun j => var (Γ.length + j + 3))) t1
  let stepF := lamAt (prepend [TN] (hctx Γ)) 0 (lamAt C2 0 M)
  let recT := app (TAr TN (TAr (wty A) (wty A))) (app (wty A) (app TN (Rc (wty A)) (var Γ.length)) base) stepF
  have hbase : Wt (hctx Γ) base (wty A) :=
    wt_tsub ht0' (fun j => wt_var' (hctx_ge Γ (Nat.le_succ_of_le (Nat.le_add_right _ j))))
  have hM : Wt C2 M (wty A) :=
    wt_tsub ht1' (fun
      | 0 => wt_var' rfl
      | 1 => wt_var' rfl
      | j + 2 => wt_var' (hctx_ge Γ (Nat.le_succ_of_le (Nat.le_add_right _ j))))
  have hstep : Wt (hctx Γ) stepF (TAr TN (TAr (wty A) (wty A))) :=
    wt_ext (Γ := rem 0 (prepend [TN] (hctx Γ))) (fun _ => rfl)
      (wt_lam_at 0 (wt_ext (Γ := rem 0 C2) (fun | 0 => rfl | _ + 1 => rfl) (wt_lam_at 0 hM)))
  have hrec : Wt (hctx Γ) recT (wty A) :=
    .app _ _ _ _ (.app _ _ _ _ (.app _ _ _ _ (.R _) (wt_var' (hctx_ge Γ (Nat.le_refl _)))) hbase) hstep
  refine ⟨lamAt (hctx Γ) Γ.length recT, zeros Γ, ?_, fun _ _ hD => wt_zeros _ hD, ?_⟩
  · have := wt_lam_at Γ.length hrec
    rw [hctx_ge Γ (Nat.le_refl _)] at this
    exact wt_ext (rem_hctx Γ) this
  intro xs y ns hx hy hn _
  have hlen := XT_length hx
  have hz : Typing [] (pi1 TN (cty A) y) TN := typing_pi1 hy
  let ρ' := prepend xs (prepend [pi1 TN (cty A) y] ns)
  have hρ' : ∀ i, Typing [] (ρ' i) (hctx Γ i) := hctx_typed hx (Ns_cons hz hn)
  have Ebase : tsub ρ' base = tsub ns t0 := by
    rw [tsub_comp]
    refine tsub_ext ?_ _
    intro j
    show prepend xs _ (Γ.length + j + 1) = ns j
    rw [← hlen]; exact prepend_ge xs _ (j + 1)
  let Fm := fun m => app (TAr TN (TAr (wty A) (wty A)))
    (app (wty A) (app TN (Rc (wty A)) (num m)) (tsub ρ' base)) (tsub ρ' stepF)
  have hbaseT : Typing [] (tsub ρ' base) (wty A) := wt_typing hbase hρ'
  have hstepT : Typing [] (tsub ρ' stepF) (TAr TN (TAr (wty A) (wty A))) := wt_typing hstep hρ'
  have hF : ∀ m, Typing [] (Fm m) (wty A) := fun m =>
    .app _ _ _ _ (.app _ _ _ _ (.app _ _ _ _ (.R _) (typing_num [] m)) hbaseT) hstepT
  have hclaim : ∀ m y', Typing [] y' (cty A) → Dsem A (Fm m) y' (prepend [num m] ns) := by
    intro m
    induction m with
    | zero =>
      intro y' hy'
      refine Dsem_red (star_one (.R0 _ _ _ _ _ _ _ rfl)) (.refl _) ?_
      rw [Ebase]
      have hy'' : Typing [] y' (cty (sub1 A .tz)) := by
        show Typing [] y' (cty (fsubst _ A)); rw [cty_subst]; exact hy'
      have H := (D_sub1 A .tz _ y' ns).1 (H0 [] y' ns .nil hy'' hn (fun i _ hD => by cases i <;> cases hD))
      have e : tsub (prepend [] ns) t0 = tsub ns t0 := tsub_ext (fun _ => rfl) t0
      rw [e] at H
      exact H
    | succ m ih =>
      intro y' hy'
      refine Dsem_red (star_one (.RS _ _ _ _ _ _ _ _ (isNum_num (m + 1)))) (.refl _) ?_
      refine Dsem_red (star_trans (star_app_l _ _ (star_lam_at _ 0 _ ρ' _ _)) (star_lam_at C2 0 M _ _ (Fm m)))
        (.refl _) ?_
      have EM : tsub (ins 0 (Fm m) (ins 0 (num m) ρ')) M = tsub (prepend [Fm m] (prepend [num m] ns)) t1 := by
        rw [tsub_comp]
        refine tsub_ext ?_ _
        intro k
        match k with
        | 0 => rfl
        | 1 => rfl
        | j + 2 =>
          show ρ' (Γ.length + j + 1) = ns j
          show prepend xs _ (Γ.length + j + 1) = ns j
          rw [← hlen]; exact prepend_ge xs _ (j + 1)
      rw [EM]
      have HXT : XT [A] [Fm m] := .cons (hF m) .nil
      have hy'' : Typing [] y' (cty (fsubst sucSub A)) := by rw [cty_subst]; exact hy'
      have hn' : Ns (prepend [num m] ns) := Ns_cons (typing_num [] m) hn
      have HH : Hyps [A] [Fm m] (fun i => tsub (prepend [y', Fm m] (prepend [num m] ns)) (s1 i))
          (prepend [num m] ns) :=
        Hyps_cons (ih _ (inst_s (hs1 0 A rfl) HXT hy'' hn')) (fun i _ hD => by cases i <;> cases hD)
      have H := (D_subst A sucSub _ y' _).1 (H1 [Fm m] y' (prepend [num m] ns) HXT hy'' hn' HH)
      exact (Dsem_ext (ns := fun j => tsub (prepend [num m] ns) (tr (sucSub j)))
        (ns' := prepend [num (m + 1)] ns) A _ y' (fun | 0 => rfl | _ + 1 => rfl)).1 H
  refine (D_all A _ y ns).2 ?_
  obtain ⟨k, hk⟩ := T_eval hz
  refine Dsem_red (star_lam_at _ Γ.length recT (prepend xs ns) _ _) (.refl _) ?_
  have e : tsub (ins Γ.length (pi1 TN (cty A) y) (prepend xs ns)) recT = tsub ρ' recT := by
    refine tsub_ext ?_ recT
    intro i
    show ins Γ.length _ _ i = prepend xs _ i
    rw [← hlen]; exact ins_prepend xs ns _ i
  rw [e]
  have hzL : Star (ρ' Γ.length) (num k) := by
    show Star (prepend xs _ Γ.length) _
    rw [← hlen]
    exact (prepend_ge xs (prepend [pi1 TN (cty A) y] ns) 0) ▸ hk
  exact (Dsem_star A (star_app_l _ _ (star_app_l _ _ (star_app_r _ _ hzL))) (.refl _) (Ns_star ns hk)).2
    (hclaim k _ (typing_pi2 hy))

/-! ## Consistency -/

/-- Rocq: `Analysis.Dialectica.HA_sound`. -/
theorem HA_sound {Γ : List Form} {A : Form} (h : HA Γ A) : Real Γ A := by
  induction h with
  | hyp _ _ hA => exact R_hyp hA
  | botE _ _ _ ih => exact R_botE ih
  | dne _ _ hc _ _ => exact Bool.noConfusion hc
  | andI _ _ _ _ _ ih1 ih2 => exact R_andI ih1 ih2
  | andE1 _ _ _ _ ih => exact R_andE1 ih
  | andE2 _ _ _ _ ih => exact R_andE2 ih
  | orI1 _ _ _ _ ih => exact R_orI1 ih
  | orI2 _ _ _ _ ih => exact R_orI2 ih
  | orE _ _ _ _ _ _ _ ih1 ih2 ih3 => exact R_orE ih1 ih2 ih3
  | impI _ _ _ _ ih => exact R_impI ih
  | impE _ _ _ _ _ ih1 ih2 => exact R_impE ih1 ih2
  | allI _ _ _ ih => exact R_allI ih
  | allE _ _ t _ ih => exact R_allE t ih
  | exI _ _ t _ ih => exact R_exI t ih
  | exE _ _ _ _ _ ih1 ih2 => exact R_exE ih1 ih2
  | refl Γ t => exact R_refl Γ t
  | leib _ _ _ _ _ _ ih1 ih2 => exact R_leib ih1 ih2
  | succNe Γ t => exact R_succ_ne Γ t
  | succInj _ _ _ _ ih => exact R_succ_inj ih
  | plus0 Γ t => exact R_plus0 Γ t
  | plusS Γ s t => exact R_plusS Γ s t
  | mult0 Γ t => exact R_mult0 Γ t
  | multS Γ s t => exact R_multS Γ s t
  | ind Γ _ _ _ ih0 ih1 => exact R_ind Γ ih0 ih1

/-- A closed proof of `⊥` in Heyting arithmetic would give a closed term of T
whose matrix `⊥_D` holds; but `⊥_D` is the numeral `1`.
Rocq: `Analysis.Dialectica.HA_consistent`. -/
theorem HA_consistent : ¬ HA [] .bot := fun h =>
  let ⟨t, _, _, _, H⟩ := HA_sound h
  D_bot (tsub (prepend [] (fun _ => Zc)) t) Zc (fun _ => Zc)
    (H [] Zc (fun _ => Zc) .nil .Z (fun _ => .Z) (fun i _ hB => by cases i <;> cases hB))

/-- Peano arithmetic is consistent: by the negative translation, a proof of
`⊥` in PA gives one in HA. Rocq: `Analysis.Dialectica.PA_consistent`. -/
theorem PA_consistent : ¬ PA [] .bot := fun h => HA_consistent (PA_HA_consistency h)

end ConstructiveOrdinals.Dialectica
