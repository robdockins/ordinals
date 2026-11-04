import ConstructiveOrdinals.Prelude.List

/-!
# Relation operators and their well-foundedness

Axiom-free ports of the parts of Rocq's standard library that
`WellFounded.v` relies on: closure operators (`Relation_Operators`), the
standard well-foundedness constructions (`Inverse_Image`, `Inclusion`,
`Transitive_Closure`, `Disjoint_Union`, `Lexicographic_Product`), the
relations of `Lexicographic_Exponentiation` and `List_Extension`, and the
permutation relation (`Sorting.Permutation`).

The well-foundedness of lexicographic exponentiation and of list extension
is proved in `WellFounded.lean`, where it follows from ordinal
interpretations; Rocq's standard library proves them directly.
-/

namespace ConstructiveOrdinals

universe u v

variable {A : Type u}

/-! ## Closures -/

/-- Rocq: `Relation_Operators.clos_trans`. -/
inductive ClosTrans (R : A → A → Prop) : A → A → Prop
  | step {x y} : R x y → ClosTrans R x y
  | trans {x y z} : ClosTrans R x y → ClosTrans R y z → ClosTrans R x z

/-- Rocq: `Relation_Operators.clos_trans_n1`. -/
inductive ClosTransN1 (R : A → A → Prop) : A → A → Prop
  | step {x y} : R x y → ClosTransN1 R x y
  | trans {x y z} : R y z → ClosTransN1 R x y → ClosTransN1 R x z

/-- Rocq: `Relation_Operators.clos_refl_trans`. -/
inductive ClosReflTrans (R : A → A → Prop) : A → A → Prop
  | step {x y} : R x y → ClosReflTrans R x y
  | refl (x) : ClosReflTrans R x x
  | trans {x y z} : ClosReflTrans R x y → ClosReflTrans R y z → ClosReflTrans R x z

/-- Rocq: `Relation_Operators.clos_refl_trans_n1`. -/
inductive ClosReflTransN1 (R : A → A → Prop) : A → A → Prop
  | refl (x) : ClosReflTransN1 R x x
  | trans {x y z} : R y z → ClosReflTransN1 R x y → ClosReflTransN1 R x z

/-- Rocq: `Relation_Operators.clos_refl`. -/
inductive ClosRefl (R : A → A → Prop) : A → A → Prop
  | step {x y} : R x y → ClosRefl R x y
  | refl (x) : ClosRefl R x x

variable {R : A → A → Prop}

theorem ClosTransN1.append {x y z : A} (h₁ : ClosTransN1 R x y) (h₂ : ClosTransN1 R y z) :
    ClosTransN1 R x z := by
  induction h₂ with
  | step h => exact .trans h h₁
  | trans h _ ih => exact .trans h ih

/-- Rocq: `Operators_Properties.clos_trans_tn1`. -/
theorem clos_trans_tn1 {x y : A} (h : ClosTrans R x y) : ClosTransN1 R x y := by
  induction h with
  | step h => exact .step h
  | trans _ _ ih₁ ih₂ => exact ih₁.append ih₂

/-- Rocq: `Operators_Properties.clos_tn1_trans`. -/
theorem clos_tn1_trans {x y : A} (h : ClosTransN1 R x y) : ClosTrans R x y := by
  induction h with
  | step h => exact .step h
  | trans h _ ih => exact .trans ih (.step h)

theorem ClosReflTransN1.append {x y z : A} (h₁ : ClosReflTransN1 R x y) (h₂ : ClosReflTransN1 R y z) :
    ClosReflTransN1 R x z := by
  induction h₂ with
  | refl => exact h₁
  | trans h _ ih => exact .trans h ih

/-- Rocq: `Operators_Properties.clos_rt_rtn1`. -/
theorem clos_rt_rtn1 {x y : A} (h : ClosReflTrans R x y) : ClosReflTransN1 R x y := by
  induction h with
  | step h => exact .trans h (.refl _)
  | refl => exact .refl _
  | trans _ _ ih₁ ih₂ => exact ih₁.append ih₂

/-- Rocq: `Operators_Properties.clos_t_clos_rt`. -/
theorem clos_t_clos_rt {x y : A} (h : ClosTrans R x y) : ClosReflTrans R x y := by
  induction h with
  | step h => exact .step h
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Rocq: `Operators_Properties.clos_rt_t`. -/
theorem clos_rt_t {x y z : A} (h₁ : ClosReflTrans R x y) (h₂ : ClosTrans R y z) : ClosTrans R x z := by
  induction h₁ with
  | step h => exact .trans (.step h) h₂
  | refl => exact h₂
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ h₂)

/-! ## Well-foundedness constructions -/

theorem acc_closTrans {x : A} (h : Acc R x) : Acc (ClosTrans R) x := by
  induction h with
  | intro x _ ih =>
    refine Acc.intro x fun y hy => ?_
    match clos_trans_tn1 hy with
    | .step h => exact ih y h
    | .trans hzx hyz => exact (ih _ hzx).inv (clos_tn1_trans hyz)

/-- Rocq: `Transitive_Closure.wf_clos_trans`. -/
theorem wf_clos_trans (h : WellFounded R) : WellFounded (ClosTrans R) :=
  ⟨fun x => acc_closTrans (h.apply x)⟩

/-- Rocq: `Inverse_Image.wf_inverse_image`. -/
theorem wf_inverse_image {B : Type v} (R : B → B → Prop) (f : A → B) (h : WellFounded R) :
    WellFounded fun x y => R (f x) (f y) := by
  have key : ∀ b, Acc R b → ∀ a, f a = b → Acc (fun x y => R (f x) (f y)) a := by
    intro b hb
    induction hb with
    | intro b _ ih =>
      intro a ha
      exact Acc.intro a fun a' h' => ih (f a') (ha ▸ h') a' rfl
  exact ⟨fun a => key (f a) (h.apply (f a)) a rfl⟩

/-- Rocq: `Inclusion.wf_incl`. -/
theorem wf_incl (R₁ R₂ : A → A → Prop) (hincl : ∀ x y, R₁ x y → R₂ x y) (h : WellFounded R₂) :
    WellFounded R₁ := by
  have key : ∀ x, Acc R₂ x → Acc R₁ x := by
    intro x hx
    induction hx with
    | intro x _ ih => exact Acc.intro x fun y hy => ih y (hincl y x hy)
  exact ⟨fun x => key x (h.apply x)⟩

/-- The order on `A ⊕ B`: all of `A` before all of `B`.
Rocq: `Relation_Operators.le_AsB`. -/
inductive LeAsB {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop) : A ⊕ B → A ⊕ B → Prop
  | aa {x y : A} : leA x y → LeAsB leA leB (.inl x) (.inl y)
  | ab (x : A) (y : B) : LeAsB leA leB (.inl x) (.inr y)
  | bb {x y : B} : leB x y → LeAsB leA leB (.inr x) (.inr y)

/-- Rocq: `Disjoint_Union.wf_disjoint_sum`. -/
theorem wf_disjoint_sum {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop)
    (hA : WellFounded leA) (hB : WellFounded leB) : WellFounded (LeAsB leA leB) := by
  have hinl : ∀ a, Acc (LeAsB leA leB) (.inl a) := by
    intro a
    induction hA.apply a with
    | intro a _ ih =>
      refine Acc.intro _ fun y hy => ?_
      cases hy with
      | aa h => exact ih _ h
  have hinr : ∀ b, Acc (LeAsB leA leB) (.inr b) := by
    intro b
    induction hB.apply b with
    | intro b _ ih =>
      refine Acc.intro _ fun y hy => ?_
      cases hy with
      | ab x _ => exact hinl x
      | bb h => exact ih _ h
  exact ⟨fun | .inl a => hinl a | .inr b => hinr b⟩

/-- Rocq: `Relation_Operators.symprod`. -/
inductive Symprod {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop) : A × B → A × B → Prop
  | left {x x' : A} : leA x x' → ∀ y : B, Symprod leA leB (x, y) (x', y)
  | right {y y' : B} : leB y y' → ∀ x : A, Symprod leA leB (x, y) (x, y')

/-- Rocq: `Lexicographic_Product.wf_symprod`. -/
theorem wf_symprod {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop)
    (hA : WellFounded leA) (hB : WellFounded leB) : WellFounded (Symprod leA leB) := by
  have key : ∀ a b, Acc (Symprod leA leB) (a, b) := by
    intro a
    induction hA.apply a with
    | intro a _ iha =>
      intro b
      induction hB.apply b with
      | intro b _ ihb =>
        refine Acc.intro _ fun p hp => ?_
        cases hp with
        | left h => exact iha _ h b
        | right h => exact ihb _ h
  exact ⟨fun ⟨a, b⟩ => key a b⟩

/-- Rocq: `Relation_Operators.slexprod`. -/
inductive Slexprod {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop) : A × B → A × B → Prop
  | left {x x' : A} (y y' : B) : leA x x' → Slexprod leA leB (x, y) (x', y')
  | right (x : A) {y y' : B} : leB y y' → Slexprod leA leB (x, y) (x, y')

/-- Rocq: `Lexicographic_Product.wf_slexprod`. -/
theorem wf_slexprod {B : Type v} (leA : A → A → Prop) (leB : B → B → Prop)
    (hA : WellFounded leA) (hB : WellFounded leB) : WellFounded (Slexprod leA leB) := by
  have key : ∀ a b, Acc (Slexprod leA leB) (a, b) := by
    intro a
    induction hA.apply a with
    | intro a _ iha =>
      intro b
      induction hB.apply b with
      | intro b _ ihb =>
        refine Acc.intro _ fun p hp => ?_
        cases hp with
        | left _ _ h => exact iha _ h _
        | right _ h => exact ihb _ h
  exact ⟨fun ⟨a, b⟩ => key a b⟩

/-- Rocq: `Relation_Operators.lexprod`. -/
inductive Lexprod {B : A → Type v} (leA : A → A → Prop) (leB : ∀ x, B x → B x → Prop) :
    (Σ x, B x) → (Σ x, B x) → Prop
  | left {x x' : A} (y : B x) (y' : B x') : leA x x' → Lexprod leA leB ⟨x, y⟩ ⟨x', y'⟩
  | right (x : A) {y y' : B x} : leB x y y' → Lexprod leA leB ⟨x, y⟩ ⟨x, y'⟩

/-- Rocq: `Lexicographic_Product.wf_lexprod`. -/
theorem wf_lexprod {B : A → Type v} (leA : A → A → Prop) (leB : ∀ x, B x → B x → Prop)
    (hA : WellFounded leA) (hB : ∀ x, WellFounded (leB x)) : WellFounded (Lexprod leA leB) := by
  have key : ∀ a (b : B a), Acc (Lexprod leA leB) ⟨a, b⟩ := by
    intro a
    induction hA.apply a with
    | intro a _ iha =>
      intro b
      induction (hB a).apply b with
      | intro b _ ihb =>
        refine Acc.intro _ fun p hp => ?_
        cases hp with
        | left _ _ h => exact iha _ h _
        | right _ h => exact ihb _ h
  exact ⟨fun ⟨a, b⟩ => key a b⟩

/-- `<` on `Nat` is well-founded. Rocq: `Wf_nat.lt_wf`. -/
theorem nat_lt_wf : WellFounded fun a b : Nat => a < b := by
  have key : ∀ n m : Nat, m < n → Acc (fun a b : Nat => a < b) m := by
    intro n
    induction n with
    | zero => intro m h; exact absurd h (Nat.not_lt_zero m)
    | succ n ih =>
      intro m h
      refine Acc.intro m fun k hk => ih k (Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ h))
  exact ⟨fun n => key (n + 1) n (Nat.lt_succ_self n)⟩

/-! ## Lexicographic exponentiation -/

section lex_exp

variable (leA : A → A → Prop)

/-- Lexicographic order on lists. Rocq: `Relation_Operators.Ltl`. -/
inductive Ltl : List A → List A → Prop
  | nil (a : A) (x : List A) : Ltl [] (a :: x)
  | hd {a b : A} : leA a b → ∀ x y : List A, Ltl (a :: x) (b :: y)
  | tl (a : A) {x y : List A} : Ltl x y → Ltl (a :: x) (a :: y)

/-- Descending lists, built by adding elements at the end.
Rocq: `Relation_Operators.Desc`. -/
inductive Desc : List A → Prop
  | nil : Desc []
  | one (x : A) : Desc [x]
  | conc (x y : A) (l : List A) : ClosRefl leA x y → Desc (l ++ [y]) → Desc ((l ++ [y]) ++ [x])

/-- Rocq: `Relation_Operators.Pow`. -/
def Pow : Type u := { l : List A // Desc leA l }

/-- Rocq: `Relation_Operators.lex_exp`. -/
def lexExp (a b : Pow leA) : Prop := Ltl leA a.1 b.1

/-- Descending lists, characterized from the front. -/
def DescF : List A → Prop
  | [] => True
  | [_] => True
  | x :: x' :: xs => ClosRefl leA x' x ∧ DescF (x' :: xs)

variable {leA}

private theorem descF_snoc {y x : A} (hxy : ClosRefl leA x y) :
    ∀ l : List A, DescF leA (l ++ [y]) → DescF leA ((l ++ [y]) ++ [x])
  | [], _ => ⟨hxy, trivial⟩
  | [_], ⟨h, _⟩ => ⟨h, hxy, trivial⟩
  | _ :: z :: l, ⟨h, hd⟩ => ⟨h, descF_snoc hxy (z :: l) hd⟩

private theorem descF_snoc_inv {y x : A} :
    ∀ l : List A, DescF leA ((l ++ [y]) ++ [x]) → ClosRefl leA x y ∧ DescF leA (l ++ [y])
  | [], ⟨h, _⟩ => ⟨h, trivial⟩
  | [_], ⟨h, h', _⟩ => ⟨h', h, trivial⟩
  | _ :: z :: l, ⟨h, hd⟩ => let ⟨h₁, h₂⟩ := descF_snoc_inv (z :: l) hd; ⟨h₁, h, h₂⟩

theorem desc_descF {l : List A} (h : Desc leA l) : DescF leA l := by
  induction h with
  | nil => trivial
  | one => trivial
  | conc x y l hxy _ ih => exact descF_snoc hxy l ih

private theorem snoc_cases : ∀ l : List A, l = [] ∨ ∃ l' y, l = l' ++ [y] := by
  intro l
  induction l using List.rev_ind with
  | hnil => exact .inl rfl
  | hsnoc y l' _ => exact .inr ⟨l', y, rfl⟩

theorem descF_desc (l : List A) : DescF leA l → Desc leA l := by
  induction l using List.rev_ind with
  | hnil => intro; exact .nil
  | hsnoc x l ih =>
    intro h
    match snoc_cases l with
    | .inl hl => subst hl; exact .one x
    | .inr ⟨l', y, hl⟩ =>
      subst hl
      obtain ⟨hxy, hd⟩ := descF_snoc_inv l' h
      exact .conc x y l' hxy (ih hd)

theorem desc_iff (l : List A) : Desc leA l ↔ DescF leA l := ⟨desc_descF, descF_desc l⟩

private theorem descF_append_left : ∀ x y : List A, DescF leA (x ++ y) → DescF leA x
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: z :: x, y, ⟨h, hd⟩ => ⟨h, descF_append_left (z :: x) y hd⟩

private theorem descF_append_right : ∀ x y : List A, DescF leA (x ++ y) → DescF leA y
  | [], _, h => h
  | [_], [], _ => trivial
  | [_], _ :: _, ⟨_, h⟩ => h
  | _ :: z :: x, y, ⟨_, hd⟩ => descF_append_right (z :: x) y hd

/-- Rocq: `Lexicographic_Exponentiation.dist_Desc_concat`. -/
theorem dist_Desc_concat (x y : List A) (h : Desc leA (x ++ y)) : Desc leA x ∧ Desc leA y :=
  ⟨descF_desc x (descF_append_left x y (desc_descF h)),
   descF_desc y (descF_append_right x y (desc_descF h))⟩

/-- Every element of a descending list is below its head.
Rocq: `Lexicographic_Exponentiation.desc_hd`. -/
theorem desc_hd : ∀ (l : List A), Desc leA l → ∀ b, b ∈ l → ClosReflTrans leA b (l.headD b)
  | [], _, _, h => nomatch h
  | [_], _, _, .head _ => .refl _
  | [_], _, _, .tail _ h => nomatch h
  | x :: x' :: xs, h, b, hb => by
    obtain ⟨hx'x, hd⟩ := desc_descF h
    have ih := desc_hd (x' :: xs) (descF_desc _ hd)
    have hstep : ClosReflTrans leA x' x := match hx'x with
      | .step h => .step h
      | .refl _ => .refl _
    match hb with
    | .head _ => exact .refl _
    | .tail _ hb => exact .trans (ih b hb) hstep

end lex_exp

/-! ## List extension -/

/-- Replace one element of a list by zero or more smaller elements.
Rocq: `List_Extension.list_ext`. -/
inductive ListExt (ltA : A → A → Prop) : List A → List A → Prop
  | intro (a : A) (bs l₁ l₂ : List A) : (∀ b, b ∈ bs → ltA b a) →
      ListExt ltA (l₁ ++ (bs ++ l₂)) (l₁ ++ a :: l₂)

/-! ## Permutations -/

/-- Rocq: `Permutation.Permutation`. -/
inductive Permutation : List A → List A → Prop
  | nil : Permutation [] []
  | skip (x : A) {l l' : List A} : Permutation l l' → Permutation (x :: l) (x :: l')
  | swap (x y : A) (l : List A) : Permutation (y :: x :: l) (x :: y :: l)
  | trans {l l' l'' : List A} : Permutation l l' → Permutation l' l'' → Permutation l l''

namespace Permutation

theorem refl : ∀ l : List A, Permutation l l
  | [] => .nil
  | x :: l => .skip x (refl l)

theorem symm {l l' : List A} (h : Permutation l l') : Permutation l' l := by
  induction h with
  | nil => exact .nil
  | skip x _ ih => exact .skip x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

theorem mem {l l' : List A} (h : Permutation l l') {a : A} (ha : a ∈ l) : a ∈ l' := by
  induction h with
  | nil => exact ha
  | skip x _ ih =>
    match ha with
    | .head _ => exact .head _
    | .tail _ h => exact .tail _ (ih h)
  | swap x y l =>
    match ha with
    | .head _ => exact .tail _ (.head _)
    | .tail _ (.head _) => exact .head _
    | .tail _ (.tail _ h) => exact .tail _ (.tail _ h)
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ ha)

end Permutation

/-- `l'` is `l` with `a` inserted somewhere. Rocq: `List.Add`. -/
inductive ListAdd (a : A) : List A → List A → Prop
  | head (l : List A) : ListAdd a l (a :: l)
  | cons (x : A) {l l' : List A} : ListAdd a l l' → ListAdd a (x :: l) (x :: l')

theorem listAdd_app (a : A) : ∀ l₁ l₂ : List A, ListAdd a (l₁ ++ l₂) (l₁ ++ a :: l₂)
  | [], l₂ => .head l₂
  | x :: l₁, l₂ => .cons x (listAdd_app a l₁ l₂)

theorem perm_listAdd {a : A} {l l' : List A} (h : ListAdd a l l') : Permutation (a :: l) l' := by
  induction h with
  | head l => exact .refl _
  | cons x _ ih => exact .trans (.swap x a _) (.skip x ih)

theorem listAdd_mem {a : A} {l l' : List A} (h : ListAdd a l l') : a ∈ l' :=
  (perm_listAdd h).mem (.head _)

theorem listAdd_inv {a : A} : ∀ {l : List A}, a ∈ l → ∃ l', ListAdd a l' l
  | _ :: l, .head _ => ⟨l, .head l⟩
  | x :: _, .tail _ h => let ⟨l', h'⟩ := listAdd_inv h; ⟨x :: l', .cons x h'⟩

/-- Removing the same element from the same list gives permutations. -/
theorem listAdd_same_perm {a : A} {l₁ l₂ l : List A} (h₁ : ListAdd a l₁ l) (h₂ : ListAdd a l₂ l) :
    Permutation l₁ l₂ := by
  induction h₁ generalizing l₂ with
  | head l =>
    cases h₂ with
    | head => exact .refl _
    | cons _ h => exact (perm_listAdd h).symm
  | cons x h ih =>
    cases h₂ with
    | head => exact perm_listAdd h
    | cons _ h' => exact .skip x (ih h')

/-- Rocq: `Permutation.Permutation_Add_inv`. -/
theorem perm_listAdd_inv {a : A} {l₁ l₂ : List A} (hp : Permutation l₁ l₂) :
    ∀ {l₁' l₂' : List A}, ListAdd a l₁' l₁ → ListAdd a l₂' l₂ → Permutation l₁' l₂' := by
  induction hp with
  | nil => intro _ _ h; exact nomatch h
  | skip x hp ih =>
    intro l₁' l₂' h₁ h₂
    cases h₁ with
    | head =>
      cases h₂ with
      | head => exact hp
      | cons _ h => exact .trans hp (perm_listAdd h).symm
    | cons _ h =>
      cases h₂ with
      | head => exact .trans (perm_listAdd h) hp
      | cons _ h' => exact .skip x (ih h h')
  | swap =>
    intro l₁' l₂' h₁ h₂
    cases h₁ with
    | head =>
      cases h₂ with
      | head => exact .refl _
      | cons _ h =>
        cases h with
        | head => exact .refl _
        | cons _ h => exact .skip _ (perm_listAdd h).symm
    | cons _ h =>
      cases h with
      | head =>
        cases h₂ with
        | head => exact .refl _
        | cons _ h =>
          cases h with
          | head => exact .refl _
          | cons _ h => exact .trans (.skip _ (perm_listAdd h).symm) (.swap _ _ _)
      | cons _ h =>
        cases h₂ with
        | head => exact .skip _ (perm_listAdd h)
        | cons _ h' =>
          cases h' with
          | head => exact .trans (.swap _ _ _) (.skip _ (perm_listAdd h))
          | cons _ h' => exact .trans (.swap _ _ _) (.skip _ (.skip _ (listAdd_same_perm h h')))
  | trans _ _ ih₁ ih₂ =>
    intro l₁' l₂' h₁ h₂
    obtain ⟨l', h⟩ := listAdd_inv (Permutation.mem ‹_› (listAdd_mem h₁))
    exact .trans (ih₁ h₁ h) (ih₂ h h₂)

/-- Rocq: `Permutation.Permutation_app_inv`. -/
theorem Permutation_app_inv (l₁ l₂ l₃ l₄ : List A) (a : A)
    (h : Permutation (l₁ ++ a :: l₂) (l₃ ++ a :: l₄)) : Permutation (l₁ ++ l₂) (l₃ ++ l₄) :=
  perm_listAdd_inv h (listAdd_app a l₁ l₂) (listAdd_app a l₃ l₄)

/-- Rocq: `Permutation.Permutation_app_inv_m`. -/
theorem Permutation_app_inv_m : ∀ (l l₁ l₂ l₃ l₄ : List A),
    Permutation (l₁ ++ (l ++ l₂)) (l₃ ++ (l ++ l₄)) → Permutation (l₁ ++ l₂) (l₃ ++ l₄)
  | [], _, _, _, _, h => h
  | x :: l, l₁, l₂, l₃, l₄, h =>
    Permutation_app_inv_m l l₁ l₂ l₃ l₄ (Permutation_app_inv l₁ (l ++ l₂) l₃ (l ++ l₄) x h)

/-- Rocq: `Permutation.Permutation_app_middle`. -/
theorem Permutation_app_middle : ∀ (l l₁ l₂ l₃ l₄ : List A),
    Permutation (l₁ ++ l₂) (l₃ ++ l₄) → Permutation (l₁ ++ (l ++ l₂)) (l₃ ++ (l ++ l₄))
  | [], _, _, _, _, h => h
  | x :: l, l₁, l₂, l₃, l₄, h =>
    have ih := Permutation_app_middle l l₁ l₂ l₃ l₄ h
    .trans (perm_listAdd (listAdd_app x l₁ (l ++ l₂))).symm
      (.trans (.skip x ih) (perm_listAdd (listAdd_app x l₃ (l ++ l₄))))

private theorem mem_split {a : A} : ∀ {l : List A}, a ∈ l → ∃ l' l'', l = l' ++ a :: l''
  | _ :: l, .head _ => ⟨[], l, rfl⟩
  | x :: _, .tail _ h => let ⟨l', l'', e⟩ := mem_split h; ⟨x :: l', l'', e ▸ rfl⟩

/-- Rocq: `Permutation.Permutation_vs_elt_inv`. -/
theorem Permutation_vs_elt_inv (l l₁ l₂ : List A) (a : A) (h : Permutation l (l₁ ++ a :: l₂)) :
    ∃ l' l'', l = l' ++ a :: l'' :=
  mem_split (h.symm.mem (List.mem_append_right l₁ (.head _)))

end ConstructiveOrdinals
