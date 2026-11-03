import ConstructiveOrdinals.Operators

/-!
# Ordinal arithmetic

Port of `Ordinal/Arith.v`: transfinite primitive recursion (`fold`), and
ordinal addition, multiplication and exponentiation, together with the Knuth
up-arrow functions on ordinals.

Rocq's `Global Opaque addOrd mulOrd expOrd` is not replicated: Lean does not
unfold definitions eagerly the way Rocq's `simpl` does, so there is nothing to
protect against.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-! ## Transfinite primitive recursion -/

/-- Definition by transfinite primitive recursion, starting at `z` and
stepping with `s`. Rocq: `Arith.foldOrd`. -/
def fold (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk _ f => z ⊔ sup fun i => s (fold z s (f i))

variable {z : Ordinal.{u}} {s : Ordinal.{u} → Ordinal.{u}}

/-- Rocq: `Arith.foldOrd_unfold`. -/
theorem fold_unfold (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) :
    fold z s x = z ⊔ sup fun i : x => s (fold z s (x i)) := by
  cases x; rfl

/-- Rocq: `Arith.foldOrd_least`. -/
theorem fold_least (q : Ordinal.{u} → Ordinal.{u}) (hz : ∀ x, z ≤ q x)
    (hmono : ∀ x y, x ≤ y → s x ≤ s y) (hsq : ∀ (x : Ordinal.{u}) (i : x), s (q (x i)) ≤ q x) :
    ∀ x, fold z s x ≤ q x
  | mk A f => by
    rw [fold_unfold]
    exact lub_least (hz _) (sup_least fun a =>
      le_trans (hmono _ _ (fold_least q hz hmono hsq (f a))) (hsq (mk A f) a))

/-- Rocq: `Arith.foldOrd_unfold_le`. -/
theorem fold_unfold_le (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u})
    (i : x) : s (fold z s (x i)) ≤ fold z s x := by
  rw [fold_unfold z s x]
  exact le_trans (sup_le (fun i : x => s (fold z s (x i))) i) (lub_le2 _ _)

/-- Rocq: `Arith.foldOrd_above_z`. -/
theorem fold_above_z (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) :
    z ≤ fold z s x := by
  rw [fold_unfold]; exact lub_le1 _ _

/-- Rocq: `Arith.foldOrd_monotone`. -/
theorem fold_monotone (hs : ∀ a b, a ≤ b → s a ≤ s b) :
    ∀ x y : Ordinal.{u}, x ≤ y → fold z s x ≤ fold z s y
  | mk A f, y, h => by
    rw [fold_unfold z s (mk A f)]
    refine lub_least (fold_above_z z s y) (sup_least fun a => ?_)
    obtain ⟨b, hb⟩ := lt_elim (le_elim h a)
    exact le_trans (hs _ _ (fold_monotone hs (f a) (y b) hb)) (fold_unfold_le z s y b)

/-- Rocq: `Arith.foldOrd_zero`. -/
theorem fold_zero (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) : fold z s 0 ≈ z := by
  refine equiv_intro ?_ (fold_above_z z s 0)
  rw [fold_unfold]
  exact lub_least (le_refl z) (sup_least fun a => PEmpty.elim a)

/-- Rocq: `Arith.foldOrd_increasing`. -/
theorem fold_increasing (hinc : ∀ a, z ≤ a → a < s a) (hs : ∀ a b, a ≤ b → s a ≤ s b)
    {x y : Ordinal.{u}} (h : x < y) : fold z s x < fold z s y := by
  obtain ⟨b, hb⟩ := lt_elim h
  calc fold z s x ≤ fold z s (y b) := fold_monotone hs _ _ hb
    _ < s (fold z s (y b)) := hinc _ (fold_above_z z s _)
    _ ≤ fold z s y := fold_unfold_le z s y b

/-- Rocq: `Arith.foldOrd_succ`. -/
theorem fold_succ (x : Ordinal.{u}) (h : ∀ q, z ≤ q → z ≤ s q) :
    fold z s (succ x) ≈ s (fold z s x) := by
  refine equiv_intro ?_ (fold_unfold_le z s (succ x) PUnit.unit)
  rw [fold_unfold]
  exact lub_least (h _ (fold_above_z z s x)) (sup_least fun _ => le_refl _)

/-- Rocq: `Arith.foldOrd_limit`. -/
theorem fold_limit {x : Ordinal.{u}} (hx : IsLimit x) (hs : ∀ a b, a ≤ b → s a ≤ s b) :
    fold z s x ≈ boundedSup x (fold z s) := by
  obtain ⟨⟨a₀⟩, hasc⟩ := hx
  refine equiv_intro ?_ (boundedSup_least x _ _ fun a ha => fold_monotone hs _ _ (le_of_lt ha))
  rw [fold_unfold]
  refine lub_least (le_trans (fold_above_z z s (x a₀)) (sup_le (fun i : x => fold z s (x i)) a₀))
    (sup_least fun a => ?_)
  obtain ⟨a', ha'⟩ := hasc a
  calc s (fold z s (x a)) ≤ fold z s (succ (x a)) := fold_unfold_le z s (succ (x a)) PUnit.unit
    _ ≤ fold z s (x a') := fold_monotone hs _ _ (succ_least ha')
    _ ≤ boundedSup x (fold z s) := sup_le (fun i : x => fold z s (x i)) a'

/-- Rocq: `Arith.foldOrd_strongly_continuous`. -/
theorem fold_strongly_continuous (z : Ordinal.{u}) (s : Ordinal.{u} → Ordinal.{u}) :
    StronglyContinuous (fold z s) := fun A f a₀ => by
  rw [fold_unfold]
  refine lub_least (le_trans (fold_above_z z s (f a₀)) (sup_le (fun i => fold z s (f i)) a₀))
    (sup_least fun p => ?_)
  exact le_trans (fold_unfold_le z s (f p.1) p.2) (sup_le (fun i => fold z s (f i)) p.1)

/-- Rocq: `Arith.foldOrd_complete`. -/
theorem fold_complete (hz : Complete z) (hs₀ : ∀ x, z ≤ x → 0 < s x) (hs₁ : z ≤ s z)
    (hs₂ : ∀ x y, x ≤ y → s x ≤ s y) (hs₃ : ∀ o, Complete o → Complete (s o)) :
    ∀ x : Ordinal.{u}, Complete x → Complete (fold z s x)
  | mk X f, hx => by
    obtain ⟨hx₁, hx₂, hx₃⟩ := hx.elim
    have hsup : Complete (sup fun i : X => s (fold z s (f i))) := by
      refine sup_complete (fun i => hs₃ _ (fold_complete hz hs₀ hs₁ hs₂ hs₃ (f i) (hx₃ i)))
        (fun x₁ x₂ => ?_) ?_
      · obtain ⟨x', h₁, h₂⟩ := hx₁ x₁ x₂
        exact ⟨x', hs₂ _ _ (fold_monotone hs₂ _ _ h₁), hs₂ _ _ (fold_monotone hs₂ _ _ h₂)⟩
      · match hx₂ with
        | .inl ⟨x⟩ => exact .inl ⟨x, hs₀ _ (fold_above_z z s _)⟩
        | .inr hn => exact .inr fun x => (hn ⟨x⟩).elim
    rw [fold_unfold]
    match hx₂ with
    | .inl ⟨x⟩ =>
      exact lub_complete2 (le_trans hs₁ (le_trans (hs₂ _ _ (fold_above_z z s _))
        (sup_le (fun i : X => s (fold z s (f i))) x))) hz hsup
    | .inr hn => exact lub_complete1 (sup_least fun x => (hn ⟨x⟩).elim) hz hsup

/-! ## Addition -/

/-- Ordinal addition: iterate the successor `y` times, starting at `x`.
Rocq: `Arith.addOrd`. -/
protected def add (x y : Ordinal.{u}) : Ordinal.{u} := fold x succ y

instance : Add Ordinal.{u} := ⟨Ordinal.add⟩

theorem add_def (x y : Ordinal.{u}) : x + y = fold x succ y := rfl

/-- Rocq: `Arith.addOrd_unfold`. -/
theorem add_unfold (x y : Ordinal.{u}) : x + y = x ⊔ sup fun i : y => succ (x + y i) :=
  fold_unfold x succ y

/-- Rocq: `Arith.addOrd_succ`. -/
theorem add_succ (x y : Ordinal.{u}) : x + succ y ≈ succ (x + y) :=
  fold_succ y fun _ h => succ_trans' h

/-- Rocq: `Arith.addOrd_le1`. -/
@[ord_hint]
theorem le_add_right (x y : Ordinal.{u}) : x ≤ x + y := fold_above_z x succ y

/-- Rocq: `Arith.addOrd_le2`. -/
@[ord_hint]
theorem le_add_left (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, y ≤ x + y
  | mk B g => le_intro fun b => by
    rw [add_unfold]
    exact lt_of_lt_of_le (succ_trans (le_add_left x (g b)))
      (le_trans (sup_le (fun i : B => succ (x + g i)) b) (lub_le2 _ _))

/-- Rocq: `Arith.addOrd_zero_r`. -/
theorem add_zero (x : Ordinal.{u}) : x + 0 ≈ x := fold_zero x succ

/-- `x + 1` is above `succ x`. -/
theorem succ_le_add_one (x : Ordinal.{u}) : succ x ≤ x + 1 :=
  le_trans (succ_monotone (add_zero x).ge) (add_succ x 0).ge

/-- Rocq: `Arith.addOrd_zero_l`. -/
theorem zero_add : ∀ x : Ordinal.{u}, 0 + x ≈ x
  | mk X f => by
    refine equiv_intro ?_ (le_intro fun i => ?_) <;> rw [add_unfold]
    · exact lub_least (zero_least _) (sup_least fun i =>
        succ_least (lt_of_le_of_lt (zero_add (f i)).le (index_lt (mk X f) i)))
    · exact lt_of_lt_of_le (succ_trans (zero_add (f i)).ge)
        (le_trans (sup_le (fun i : X => succ (0 + f i)) i) (lub_le2 _ _))

/-- Rocq: `Arith.addOrd_monotone` and `Arith.addOrd_le_mor`. -/
@[ord_hint, ord_mono]
theorem add_le_add : ∀ {x y z₁ z₂ : Ordinal.{u}}, x ≤ y → z₁ ≤ z₂ → x + z₁ ≤ y + z₂
  | x, y, mk C h, z₂, hxy, hz => by
    rw [add_unfold x (mk C h)]
    refine lub_least (le_trans hxy (le_add_right y z₂)) (sup_least fun c => ?_)
    obtain ⟨d, hd⟩ := le_subord hz c
    rw [add_unfold y z₂]
    exact le_trans (succ_monotone (add_le_add hxy hd))
      (le_trans (sup_le (fun i : z₂ => succ (y + z₂ i)) d) (lub_le2 _ _))

/-- Rocq: `Arith.addOrd_increasing`. -/
theorem add_lt_add_left {x y : Ordinal.{u}} (z : Ordinal.{u}) (h : x < y) : z + x < z + y :=
  fold_increasing (fun a _ => succ_lt a) (fun _ _ => succ_monotone) h

/-- Rocq: `Arith.addOrd_lt_mor2`. -/
theorem add_lt_add_of_le_of_lt {x y z₁ z₂ : Ordinal.{u}} (h₁ : x ≤ y) (h₂ : z₁ < z₂) :
    x + z₁ < y + z₂ :=
  lt_of_lt_of_le (add_lt_add_left x h₂) (add_le_add h₁ (le_refl z₂))

/-- Rocq: `Arith.addOrd_eq_mor`. -/
theorem add_congr {x y z₁ z₂ : Ordinal.{u}} (h₁ : x ≈ y) (h₂ : z₁ ≈ z₂) : x + z₁ ≈ y + z₂ :=
  equiv_intro (add_le_add h₁.le h₂.le) (add_le_add h₁.ge h₂.ge)

/-- Rocq: `Arith.addOrd_continuous`. -/
theorem add_continuous (x : Ordinal.{u}) : StronglyContinuous (fun y => x + y) :=
  fold_strongly_continuous x succ

/-- Rocq: `Arith.addOrd_complete`. -/
@[ord_hint]
theorem add_complete {x y : Ordinal.{u}} (hx : Complete x) (hy : Complete y) :
    Complete (x + y) :=
  fold_complete (s := succ) hx (fun _ _ => lt_of_le_of_lt (zero_least _) (succ_lt _))
    (le_of_lt (succ_lt x)) (fun _ _ => succ_monotone) (fun _ => succ_complete) y hy

/-- Rocq: `Arith.add_lt`. -/
theorem add_lt {q x y : Ordinal.{u}} (h : q < x + y) : q < x ∨ ∃ i : y, q ≤ x + y i := by
  rw [add_unfold] at h
  match lub_lt h with
  | .inl h => exact .inl h
  | .inr h =>
    obtain ⟨i, hi⟩ := sup_lt h
    obtain ⟨_, hq⟩ := lt_elim hi
    exact .inr ⟨i, hq⟩

/-- Rocq: `Arith.addOrd_lub`. -/
theorem add_lub (a b c : Ordinal.{u}) : a + (b ⊔ c) ≈ (a + b) ⊔ (a + c) :=
  lub_continuous (f := fun y => a + y) b c (fun _ _ h => add_le_add (le_refl a) h)
    (add_continuous a)

/-- Rocq: `Arith.addOrd_assoc`. -/
theorem add_assoc (a b : Ordinal.{u}) : ∀ c : Ordinal.{u}, a + (b + c) ≈ a + b + c
  | mk C g => by
    rw [add_unfold b (mk C g)]
    refine equiv_trans (add_lub a b _) (equiv_intro ?_ ?_)
    · refine lub_least (le_add_right _ _) ?_
      rw [add_unfold a]
      refine lub_least (le_trans (le_add_right a b) (le_add_right _ _)) (sup_least fun p => ?_)
      refine succ_least (lt_of_le_of_lt (add_assoc a b (g p.1)).le ?_)
      exact lt_of_lt_of_le (succ_lt _) (fold_unfold_le (a + b) succ (mk C g) p.1)
    · rw [add_unfold (a + b)]
      refine lub_least (lub_le1 _ _) (sup_least fun c => succ_least ?_)
      refine lt_of_lt_of_le (lt_of_le_of_lt (add_assoc a b (g c)).ge (add_lt_add_left a ?_))
        (lub_le2 _ _)
      exact lt_of_lt_of_le (succ_lt _) (sup_le (fun i : C => succ (b + mk C g i)) c)

/-- Rocq: `Arith.addOrd_cancel_le`. -/
theorem add_cancel_le (a b : Ordinal.{u}) : ∀ x y : Ordinal.{u}, a + x ≤ b + y → b ≤ a → x ≤ y
  | mk X f, y, h₁, h₂ => le_intro fun x => by
    have h₃ : a + f x < b + y :=
      lt_of_lt_of_le (lt_of_lt_of_le (succ_lt _) (fold_unfold_le a succ (mk X f) x)) h₁
    rw [add_unfold b y] at h₃
    match lub_lt h₃ with
    | .inl h => exact (lt_irrefl b (lt_of_le_of_lt (le_trans h₂ (le_add_right a (f x))) h)).elim
    | .inr h =>
      obtain ⟨i, hi⟩ := sup_lt h
      obtain ⟨_, hi'⟩ := lt_elim hi
      exact lt_intro i (add_cancel_le a b (f x) (y i) hi' h₂)

/-- Rocq: `Arith.addOrd_cancel`. -/
theorem add_cancel {a b x y : Ordinal.{u}} (h : a + x ≈ b + y) (hab : a ≈ b) : x ≈ y :=
  equiv_intro (add_cancel_le a b x y h.le hab.ge) (add_cancel_le b a y x h.ge hab.le)

/-- Rocq: `Arith.onePlus_succ`. -/
theorem onePlus_succ : ∀ x : Ordinal.{u}, 1 + x ≤ succ x
  | mk X f => by
    rw [add_unfold]
    refine lub_least (succ_monotone (zero_least _)) (sup_least fun i => succ_monotone ?_)
    exact le_trans (onePlus_succ (f i)) (succ_least (index_lt (mk X f) i))

/-- Rocq: `Arith.limit_onePlus`. -/
theorem limit_onePlus {x : Ordinal.{u}} (hx : IsLimit x) : 1 + x ≤ x := by
  obtain ⟨⟨a⟩, hasc⟩ := hx
  rw [add_unfold]
  refine lub_least (succ_least (lt_intro a (zero_least _))) (sup_least fun i => succ_least ?_)
  obtain ⟨j, hj⟩ := hasc i
  exact lt_of_le_of_lt (le_trans (onePlus_succ (x i)) (succ_least hj)) (index_lt x j)

/-- Rocq: `Arith.natOrdSize_add`. -/
theorem ofNat_add : ∀ n m : Nat, ofNat.{u} (n + m) ≈ ofNat m + ofNat n
  | 0, m => by rw [Nat.zero_add]; exact equiv_symm (add_zero _)
  | n + 1, m => by
    rw [Nat.succ_add]
    exact equiv_trans (succ_congruence (ofNat_add n m)) (equiv_symm (add_succ _ _))

/-- Rocq: `Arith.limitOrdinal_intro`. -/
theorem limitOrdinal_intro {x : Ordinal.{u}} (h₀ : 0 < x)
    (h : ∀ i, i < x → ∃ j, i < j ∧ j < x) : IsLimit x :=
  (isLimit_iff x).2 ⟨h₀, h⟩

/-- Rocq: `Arith.successor_add`. -/
theorem successor_add (x : Ordinal.{u}) {y : Ordinal.{u}} (hy : IsSucc y) : IsSucc (x + y) :=
  let ⟨o, ho⟩ := (isSucc_iff y).1 hy
  (isSucc_iff _).2 ⟨x + o, equiv_trans (add_congr (equiv_refl x) ho) (add_succ x o)⟩

/-- Rocq: `Arith.limit_add`. -/
theorem limit_add (x : Ordinal.{u}) {y : Ordinal.{u}} (hy : IsLimit y) : IsLimit (x + y) := by
  obtain ⟨⟨a⟩, hasc⟩ := hy
  refine limitOrdinal_intro (lt_of_lt_of_le (lt_intro a (zero_least _)) (le_add_left x y))
    fun i hi => ?_
  rw [add_unfold] at hi
  match lub_lt hi with
  | .inl h =>
    exact ⟨x, h, lt_of_lt_of_le (succ_trans (le_add_right x (y a))) (fold_unfold_le x succ y a)⟩
  | .inr h =>
    obtain ⟨b, hb⟩ := sup_lt h
    obtain ⟨b', hb'⟩ := hasc b
    exact ⟨x + y b', lt_of_lt_of_le hb (succ_least (add_lt_add_left x hb')),
      lt_of_lt_of_le (succ_lt _) (fold_unfold_le x succ y b')⟩

/-- Rocq: `Arith.foldOrd_add`. -/
theorem fold_add (hs : ∀ x y, x ≤ y → s x ≤ s y) (a : Ordinal.{u}) :
    ∀ b : Ordinal.{u}, fold z s (a + b) ≈ fold (fold z s a) s b
  | mk B g => by
    refine equiv_intro ?_ ?_
    · rw [add_unfold]
      refine le_trans (lub_continuous (f := fold z s) _ _ (fold_monotone hs)
        (fold_strongly_continuous z s)).le (lub_least (by rw [fold_unfold]; exact lub_le1 _ _) ?_)
      refine le_trans (fold_monotone hs _ _ (sup_succ_lim (fun i : B => a + g i)).ge) ?_
      rw [fold_unfold z s (lim _), fold_unfold (fold z s a) s (mk B g)]
      refine lub_least (le_trans (fold_above_z z s a) (lub_le1 _ _)) (sup_least fun i => ?_)
      exact le_trans (hs _ _ (fold_add hs a (g i)).le)
        (le_trans (sup_le (fun i : B => s (fold (fold z s a) s (g i))) i) (lub_le2 _ _))
    · rw [fold_unfold (fold z s a) s (mk B g)]
      refine lub_least (fold_monotone hs _ _ (le_add_right a _)) (sup_least fun i => ?_)
      calc s (fold (fold z s a) s (g i)) ≤ s (fold z s (a + g i)) := hs _ _ (fold_add hs a (g i)).ge
        _ ≤ fold z s (succ (a + g i)) := fold_unfold_le z s (succ (a + g i)) PUnit.unit
        _ ≤ fold z s (a + mk B g) := fold_monotone hs _ _ (fold_unfold_le a succ (mk B g) i)

/-! ## Multiplication -/

/-- Ordinal multiplication: `x * y` adds `x` to itself `y` times.
Rocq: `Arith.mulOrd`. -/
protected def mul (x : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u}
  | mk _ g => sup fun b => Ordinal.mul x (g b) + x

instance : Mul Ordinal.{u} := ⟨Ordinal.mul⟩

/-- Rocq: `Arith.mulOrd_unfold`. -/
theorem mul_unfold (x y : Ordinal.{u}) : x * y = sup fun i : y => x * y i + x := by
  cases y; rfl

/-- Rocq: `Arith.mulOrd_monotone1`. -/
theorem mul_le_mul_right : ∀ (z : Ordinal.{u}) {x y : Ordinal.{u}}, x ≤ y → x * z ≤ y * z
  | mk C h, x, y, hxy => by
    rw [mul_unfold x, mul_unfold y]
    exact sup_monotone fun c => add_le_add (mul_le_mul_right (h c) hxy) hxy

/-- Rocq: `Arith.mulOrd_monotone2`. -/
theorem mul_le_mul_left (x : Ordinal.{u}) : ∀ {y z : Ordinal.{u}}, y ≤ z → x * y ≤ x * z
  | mk B g, z, h => by
    rw [mul_unfold x (mk B g)]
    refine sup_least fun b => ?_
    obtain ⟨q, hq⟩ := lt_elim (le_elim h b)
    rw [mul_unfold x z]
    exact le_trans (add_le_add (mul_le_mul_left x hq) (le_refl x))
      (sup_le (fun i : z => x * z i + x) q)

/-- Rocq: `Arith.mulOrd_increasing2`. -/
theorem mul_lt_mul_left {x y z : Ordinal.{u}} (hx : 0 < x) (h : y < z) : x * y < x * z := by
  obtain ⟨c, hc⟩ := lt_elim h
  rw [mul_unfold x z]
  exact lt_of_le_of_lt (mul_le_mul_left x hc) (lt_of_le_of_lt (add_zero _).ge
    (lt_of_lt_of_le (add_lt_add_left _ hx) (sup_le (fun i : z => x * z i + x) c)))

/-- Rocq: `Arith.mulOrd_le_mor`. -/
@[ord_mono]
theorem mul_le_mul {x x' y y' : Ordinal.{u}} (hx : x ≤ x') (hy : y ≤ y') : x * y ≤ x' * y' :=
  le_trans (mul_le_mul_left x hy) (mul_le_mul_right y' hx)

/-- Rocq: `Arith.mulOrd_eq_mor`. -/
theorem mul_congr {x x' y y' : Ordinal.{u}} (hx : x ≈ x') (hy : y ≈ y') : x * y ≈ x' * y' :=
  equiv_intro (mul_le_mul hx.le hy.le) (mul_le_mul hx.ge hy.ge)

/-- Rocq: `Arith.mulOrd_zero_r`. -/
theorem mul_zero (x : Ordinal.{u}) : x * 0 ≈ 0 := by
  refine equiv_intro ?_ (zero_least _)
  rw [mul_unfold]
  exact sup_least fun a => PEmpty.elim a

/-- Rocq: `Arith.mulOrd_zero_l`. -/
theorem zero_mul : ∀ x : Ordinal.{u}, 0 * x ≈ 0
  | mk X f => by
    refine equiv_intro ?_ (zero_least _)
    rw [mul_unfold]
    refine sup_least fun x => ?_
    rw [add_unfold]
    exact lub_least (zero_mul (f x)).le (sup_least fun i => PEmpty.elim i)

/-- Rocq: `Arith.mulOrd_succ`. -/
theorem mul_succ (x y : Ordinal.{u}) : x * succ y ≈ x * y + x := by
  rw [mul_unfold]
  exact equiv_intro (sup_least fun _ => le_refl _)
    (sup_le (fun i : (succ y).Carrier => x * succ y i + x) PUnit.unit)

/-- Rocq: `Arith.mulOrd_one_r`. -/
theorem mul_one (x : Ordinal.{u}) : x * 1 ≈ x :=
  equiv_trans (mul_succ x 0) (equiv_trans (add_congr (mul_zero x) (equiv_refl x)) (zero_add x))

/-- Rocq: `Arith.mulOrd_continuous`. -/
theorem mul_continuous (x : Ordinal.{u}) : StronglyContinuous (fun y => x * y) :=
  fun A f _ => by
    show x * sup f ≤ sup fun i => x * f i
    rw [mul_unfold]
    refine sup_least fun p => le_trans ?_ (sup_le (fun i => x * f i) p.1)
    rw [mul_unfold x (f p.1)]
    exact sup_le (fun i : f p.1 => x * f p.1 i + x) p.2

/-- Rocq: `Arith.mulOrd_lub`. -/
theorem mul_lub (a b c : Ordinal.{u}) : a * (b ⊔ c) ≈ (a * b) ⊔ (a * c) :=
  lub_continuous (f := fun y => a * y) b c (fun _ _ h => mul_le_mul_left a h) (mul_continuous a)

/-- Rocq: `Arith.mulOrd_one_l`. -/
theorem one_mul : ∀ x : Ordinal.{u}, 1 * x ≈ x
  | mk X f => by
    rw [mul_unfold]
    refine equiv_intro (sup_least fun i => ?_) (le_intro fun i => ?_)
    · rw [add_unfold]
      refine lub_least (le_trans (one_mul (f i)).le (index_le (mk X f) i))
        (sup_least fun _ => succ_least (lt_intro i ?_))
      exact le_trans (add_zero _).le (one_mul (f i)).le
    · refine lt_of_lt_of_le ?_ (sup_le (fun i : X => 1 * f i + 1) i)
      exact lt_of_lt_of_le (succ_trans (le_trans (one_mul (f i)).ge (le_add_right _ 0)))
        (add_succ _ 0).ge

/-- Rocq: `Arith.mulOrd_positive`. -/
theorem mul_pos {x y : Ordinal.{u}} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  obtain ⟨b, _⟩ := lt_elim hy
  rw [mul_unfold]
  exact lt_of_lt_of_le (lt_of_lt_of_le hx (le_add_left (x * y b) x))
    (sup_le (fun i : y => x * y i + x) b)

/-- Rocq: `Arith.mulOrd_limit`. -/
theorem mul_limit (x : Ordinal.{u}) {y : Ordinal.{u}} (hy : IsLimit y) :
    x * y ≈ sup fun b : y => x * y b := by
  rw [mul_unfold]
  refine equiv_intro (sup_least fun b => ?_) (sup_least fun b => ?_)
  · obtain ⟨b', hb'⟩ := hy.2 b
    exact le_trans (mul_succ x (y b)).ge
      (le_trans (mul_le_mul_left x (succ_least hb')) (sup_le (fun b : y => x * y b) b'))
  · exact le_trans (le_add_right _ x) (sup_le (fun i : y => x * y i + x) b)

/-- Rocq: `Arith.mulOrd_complete`. -/
theorem mul_complete {x : Ordinal.{u}} (hx : Complete x) :
    ∀ y : Ordinal.{u}, Complete y → Complete (x * y)
  | mk Y g, hy => by
    obtain ⟨hy₁, hy₂, hy₃⟩ := hy.elim
    rw [mul_unfold]
    refine sup_complete (fun i => add_complete (mul_complete hx (g i) (hy₃ i)) hx)
      (fun y₁ y₂ => ?_) ?_
    · obtain ⟨y', h₁, h₂⟩ := hy₁ y₁ y₂
      exact ⟨y', add_le_add (mul_le_mul_left x h₁) (le_refl x),
        add_le_add (mul_le_mul_left x h₂) (le_refl x)⟩
    · match complete_zeroDec hx with
      | .inl hx₀ =>
        exact .inr fun y => le_trans (add_le_add
          (le_trans (mul_le_mul_right _ hx₀) (zero_mul _).le) hx₀) (zero_add 0).le
      | .inr hx₀ =>
        match hy₂ with
        | .inl ⟨y⟩ => exact .inl ⟨y, lt_of_lt_of_le hx₀ (le_add_left _ _)⟩
        | .inr hn => exact .inr fun y => (hn ⟨y⟩).elim

/-- Left distributivity. Rocq: `Arith.ordDistrib_left`. -/
theorem mul_add (a b : Ordinal.{u}) : ∀ c : Ordinal.{u}, a * (b + c) ≈ a * b + a * c
  | mk C h => by
    refine equiv_intro ?_ ?_
    · rw [add_unfold b]
      refine le_trans (mul_lub a b _).le (lub_least (le_add_right _ _) ?_)
      rw [mul_unfold a (sup _)]
      refine sup_least fun p => ?_
      calc a * (b + h p.1) + a ≤ a * b + a * h p.1 + a := add_le_add (mul_add a b (h p.1)).le (le_refl a)
        _ ≤ a * b + (a * h p.1 + a) := (add_assoc _ _ _).ge
        _ ≤ a * b + a * mk C h := add_le_add (le_refl _) (by
            rw [mul_unfold a (mk C h)]
            exact sup_le (fun i : C => a * h i + a) p.1)
    · rw [add_unfold (a * b)]
      refine lub_least (mul_le_mul_left a (le_add_right b _)) (sup_least fun p => succ_least ?_)
      obtain ⟨i, k⟩ := p
      show a * b + (a * h i + a) k < a * (b + mk C h)
      calc a * b + (a * h i + a) k < a * b + (a * h i + a) := add_lt_add_left _ (index_lt _ _)
        _ ≈ a * b + a * h i + a := add_assoc _ _ _
        _ ≤ a * (b + h i) + a := add_le_add (mul_add a b (h i)).ge (le_refl a)
        _ ≤ a * succ (b + h i) := (mul_succ a _).ge
        _ ≤ a * (b + mk C h) := mul_le_mul_left a (fold_unfold_le b succ (mk C h) i)

/-- Rocq: `Arith.mulOrd_assoc`. -/
theorem mul_assoc (a b : Ordinal.{u}) : ∀ c : Ordinal.{u}, a * (b * c) ≈ a * b * c
  | mk C h => by
    refine equiv_intro ?_ ?_
    · rw [mul_unfold a (b * mk C h)]
      refine sup_least fun p => ?_
      obtain ⟨x, o⟩ := p
      show a * (b * h x + b) o + a ≤ a * b * mk C h
      calc a * (b * h x + b) o + a ≤ a * succ ((b * h x + b) o) := (mul_succ a _).ge
        _ ≤ a * (b * h x + b) := mul_le_mul_left a (succ_least (index_lt _ o))
        _ ≤ a * (b * h x) + a * b := (mul_add a _ b).le
        _ ≤ a * b * h x + a * b := add_le_add (mul_assoc a b (h x)).le (le_refl _)
        _ ≤ a * b * mk C h := by
            rw [mul_unfold (a * b) (mk C h)]
            exact sup_le (fun i : C => a * b * h i + a * b) x
    · rw [mul_unfold (a * b) (mk C h)]
      refine sup_least fun x => ?_
      calc a * b * h x + a * b ≤ a * (b * h x) + a * b := add_le_add (mul_assoc a b (h x)).ge (le_refl _)
        _ ≤ a * (b * h x + b) := (mul_add a _ b).ge
        _ ≤ a * (b * mk C h) := mul_le_mul_left a (by
            rw [mul_unfold b (mk C h)]
            exact sup_le (fun i : C => b * h i + b) x)

/-- Rocq: `Arith.natOrdSize_mul`. -/
theorem ofNat_mul : ∀ n m : Nat, ofNat.{u} (n * m) ≈ ofNat m * ofNat n
  | 0, m => by rw [Nat.zero_mul]; exact equiv_symm (mul_zero _)
  | n + 1, m => by
    rw [Nat.succ_mul, Nat.add_comm]
    exact equiv_trans (ofNat_add m (n * m))
      (equiv_trans (add_congr (ofNat_mul n m) (equiv_refl _)) (equiv_symm (mul_succ _ _)))

/-! ## Exponentiation -/

/-- Ordinal exponentiation: `x ^ y` multiplies by `x`, `y` times, starting
from `1`. Rocq: `Arith.expOrd`. -/
protected def pow (x y : Ordinal.{u}) : Ordinal.{u} := fold 1 (fun a => a * x) y

instance : Pow Ordinal.{u} Ordinal.{u} := ⟨Ordinal.pow⟩

theorem pow_def (x y : Ordinal.{u}) : x ^ y = fold 1 (fun a => a * x) y := rfl

/-- Rocq: `Arith.expOrd_unfold`. -/
theorem pow_unfold (x y : Ordinal.{u}) : x ^ y = 1 ⊔ sup fun i : y => x ^ y i * x :=
  fold_unfold 1 _ y

/-- Rocq: `Arith.expOrd_nonzero`. -/
theorem pow_pos (x y : Ordinal.{u}) : 0 < x ^ y :=
  lt_of_lt_of_le (succ_lt 0) (fold_above_z 1 _ y)

/-- Rocq: `Arith.expOrd_zero`. -/
theorem pow_zero (x : Ordinal.{u}) : x ^ (0 : Ordinal.{u}) ≈ 1 := fold_zero 1 (fun a => a * x)

private theorem pos_of_one_le {q : Ordinal.{u}} (h : 1 ≤ q) : 0 < q := le_elim h PUnit.unit

/-- Rocq: `Arith.expOrd_succ`. -/
theorem pow_succ {x : Ordinal.{u}} (y : Ordinal.{u}) (hx : 0 < x) : x ^ succ y ≈ x ^ y * x :=
  fold_succ y fun _ hq => succ_least (mul_pos (pos_of_one_le hq) hx)

/-- Rocq: `Arith.expOrd_monotone`. -/
theorem pow_le_pow_right (a : Ordinal.{u}) {x y : Ordinal.{u}} (h : x ≤ y) : a ^ x ≤ a ^ y :=
  fold_monotone (fun _ _ h => mul_le_mul_right a h) x y h

/-- Rocq: `Arith.expOrd_monotone_base`. -/
theorem pow_le_pow_left {x y : Ordinal.{u}} (h : x ≤ y) : ∀ a : Ordinal.{u}, x ^ a ≤ y ^ a
  | mk A f => by
    rw [pow_unfold x, pow_unfold y]
    refine lub_least (lub_le1 _ _) (le_trans (sup_least fun i => ?_) (lub_le2 _ _))
    exact le_trans (le_trans (mul_le_mul_left _ h) (mul_le_mul_right y (pow_le_pow_left h (f i))))
      (sup_le (fun i : A => y ^ f i * y) i)

/-- Rocq: `Arith.expOrd_le_mor`. -/
@[ord_mono]
theorem pow_le_pow {x x' y y' : Ordinal.{u}} (hx : x ≤ x') (hy : y ≤ y') : x ^ y ≤ x' ^ y' :=
  le_trans (pow_le_pow_right x hy) (pow_le_pow_left hx y')

/-- Rocq: `Arith.expOrd_eq_mor`. -/
theorem pow_congr {x x' y y' : Ordinal.{u}} (hx : x ≈ x') (hy : y ≈ y') : x ^ y ≈ x' ^ y' :=
  equiv_intro (pow_le_pow hx.le hy.le) (pow_le_pow hx.ge hy.ge)

/-- Rocq: `Arith.expOrd_increasing`. -/
theorem pow_lt_pow_right {a : Ordinal.{u}} (ha : 1 < a) {x y : Ordinal.{u}} (h : x < y) :
    a ^ x < a ^ y :=
  fold_increasing
    (fun b hb => lt_of_le_of_lt (mul_one b).ge (mul_lt_mul_left (pos_of_one_le hb) ha))
    (fun _ _ h => mul_le_mul_right a h) h

/-- Rocq: `Arith.expOrd_limit`. -/
theorem pow_limit {x y : Ordinal.{u}} (_hx : 1 < x) (hy : IsLimit y) :
    x ^ y ≈ boundedSup y (fun a => x ^ a) :=
  fold_limit hy fun _ _ h => mul_le_mul_right x h

/-- Rocq: `Arith.expOrd_continuous`. -/
theorem pow_continuous (x : Ordinal.{u}) : StronglyContinuous (fun y => x ^ y) :=
  fold_strongly_continuous 1 _

/-- Rocq: `Arith.expOrd_complete`. -/
theorem pow_complete {x y : Ordinal.{u}} (hx₀ : 0 < x) (hx : Complete x) (hy : Complete y) :
    Complete (x ^ y) :=
  fold_complete (s := fun a => a * x) (succ_complete zero_complete)
    (fun _ hq => mul_pos (pos_of_one_le hq) hx₀) (succ_least (mul_pos (succ_lt 0) hx₀))
    (fun _ _ h => mul_le_mul_right x h) (fun _ ho => mul_complete ho x hx) y hy

/-- Rocq: `Arith.expOrd_one_base`. -/
theorem one_pow : ∀ x : Ordinal.{u}, (1 : Ordinal.{u}) ^ x ≈ 1
  | mk A f => by
    rw [pow_unfold]
    exact equiv_intro (lub_least (le_refl 1) (sup_least fun i =>
      le_trans (mul_one _).le (one_pow (f i)).le)) (lub_le1 _ _)

/-- Rocq: `Arith.expOrd_one`. -/
theorem pow_one (x : Ordinal.{u}) : x ^ (1 : Ordinal.{u}) ≈ 1 ⊔ x := by
  rw [pow_unfold]
  refine equiv_intro (lub_least (lub_le1 _ _) (sup_least fun _ => ?_))
    (lub_least (lub_le1 _ _) ?_)
  · exact le_trans (le_trans (mul_le_mul_right x (pow_zero x).le) (one_mul x).le) (lub_le2 _ _)
  · refine le_trans ?_ (le_trans (sup_le (fun i : (1 : Ordinal.{u}).Carrier =>
      x ^ (1 : Ordinal.{u}) i * x) PUnit.unit) (lub_le2 _ _))
    exact le_trans (one_mul x).ge (mul_le_mul_right x (pow_zero x).ge)

/-- Rocq: `Arith.expOrd_one'`. -/
theorem pow_one' {x : Ordinal.{u}} (h : 0 < x) : x ^ (1 : Ordinal.{u}) ≈ x :=
  equiv_trans (pow_one x) (equiv_intro (lub_least (succ_least h) (le_refl x)) (lub_le2 _ _))

/-- Rocq: `Arith.expOrd_lub`. -/
theorem pow_lub (a b c : Ordinal.{u}) : a ^ (b ⊔ c) ≈ a ^ b ⊔ a ^ c :=
  lub_continuous (f := fun y => a ^ y) b c (fun _ _ h => pow_le_pow_right a h) (pow_continuous a)

/-- Rocq: `Arith.expOrd_add`. -/
theorem pow_add (a b : Ordinal.{u}) : ∀ c : Ordinal.{u}, a ^ (b + c) ≈ a ^ b * a ^ c
  | mk C h => by
    refine equiv_intro ?_ ?_
    · rw [add_unfold b]
      refine le_trans (pow_lub a b _).le (lub_least ?_ ?_)
      · exact le_trans (mul_one _).ge (mul_le_mul_left _ (fold_above_z 1 _ _))
      · rw [pow_unfold a (sup _)]
        refine lub_least (succ_least (mul_pos (pow_pos _ _) (pow_pos _ _))) (sup_least fun p => ?_)
        obtain ⟨x, q⟩ := p
        show a ^ (b + h x) * a ≤ a ^ b * a ^ mk C h
        calc a ^ (b + h x) * a ≤ a ^ b * a ^ h x * a := mul_le_mul_right a (pow_add a b (h x)).le
          _ ≤ a ^ b * (a ^ h x * a) := (mul_assoc _ _ _).ge
          _ ≤ a ^ b * a ^ mk C h := mul_le_mul_left _ (by
              rw [pow_unfold a (mk C h)]
              exact le_trans (sup_le (fun i : C => a ^ h i * a) x) (lub_le2 _ _))
    · rw [mul_unfold]
      refine sup_least fun j => ?_
      rcases j with _ | ⟨x, i⟩
      · show a ^ b * 0 + a ^ b ≤ a ^ (b + mk C h)
        exact le_trans (add_le_add (mul_zero _).le (le_refl _))
          (le_trans (zero_add _).le (pow_le_pow_right a (le_add_right b _)))
      · show a ^ b * (a ^ h x * a) i + a ^ b ≤ a ^ (b + mk C h)
        calc a ^ b * (a ^ h x * a) i + a ^ b ≤ a ^ b * succ ((a ^ h x * a) i) := (mul_succ _ _).ge
          _ ≤ a ^ b * (a ^ h x * a) := mul_le_mul_left _ (succ_least (index_lt _ i))
          _ ≤ a ^ b * a ^ h x * a := (mul_assoc _ _ _).le
          _ ≤ a ^ (b + h x) * a := mul_le_mul_right a (pow_add a b (h x)).ge
          _ ≤ a ^ (b + mk C h) :=
            fold_unfold_le 1 (fun c => c * a) (b + mk C h)
              (show (b + mk C h).Carrier from .inr ⟨x, PUnit.unit⟩)

/-- Rocq: `Arith.expOrd_mul`. -/
theorem pow_mul (a b : Ordinal.{u}) : ∀ c : Ordinal.{u}, a ^ (b * c) ≈ (a ^ b) ^ c
  | mk C h => by
    refine equiv_intro ?_ ?_
    · rw [pow_unfold a (b * mk C h), pow_unfold (a ^ b) (mk C h)]
      refine lub_least (lub_le1 _ _) (sup_least fun p => ?_)
      obtain ⟨i, q⟩ := p
      show a ^ (b * h i + b) q * a ≤ 1 ⊔ sup fun i : C => (a ^ b) ^ h i * a ^ b
      calc a ^ (b * h i + b) q * a ≤ a ^ (b * h i + b) := fold_unfold_le 1 (fun c => c * a) _ q
        _ ≤ a ^ (b * h i) * a ^ b := (pow_add a _ b).le
        _ ≤ (a ^ b) ^ h i * a ^ b := mul_le_mul_right _ (pow_mul a b (h i)).le
        _ ≤ 1 ⊔ sup fun i : C => (a ^ b) ^ h i * a ^ b :=
            le_trans (sup_le (fun i : C => (a ^ b) ^ h i * a ^ b) i) (lub_le2 _ _)
    · rw [pow_unfold (a ^ b) (mk C h)]
      refine lub_least (succ_least (pow_pos _ _)) (sup_least fun i => ?_)
      calc (a ^ b) ^ h i * a ^ b ≤ a ^ (b * h i) * a ^ b := mul_le_mul_right _ (pow_mul a b (h i)).ge
        _ ≤ a ^ (b * h i + b) := (pow_add a _ b).ge
        _ ≤ a ^ (b * mk C h) := pow_le_pow_right a (by
            rw [mul_unfold b (mk C h)]
            exact sup_le (fun i : C => b * h i + b) i)

/-- ω-exponentiation, `x ↦ ω ^ x`. Rocq: `Arith.powOmega`. -/
def powOmega (x : Ordinal.{u}) : Ordinal.{u} := ω ^ x

/-- Rocq: `Arith.powOmega_monotone`. -/
theorem powOmega_monotone {x y : Ordinal.{u}} (h : x ≤ y) : powOmega x ≤ powOmega y :=
  pow_le_pow_right ω h

/-- Rocq: `Arith.powOmega_increasing`. -/
theorem powOmega_increasing {x y : Ordinal.{u}} (h : x < y) : powOmega x < powOmega y :=
  pow_lt_pow_right omega_gt1 h

/-! ## The Knuth up-arrow functions

The up-arrow functions continue the pattern above: multiplication iterates
addition, exponentiation iterates multiplication, and so on.

The later functions in the sequence (`knuthUp 2` and above) are less
interesting: they saturate at `ω` and fail to be increasing. This limits their
use for building larger ordinals, even though on finite ordinals they form a
rapidly increasing sequence of functions.
-/

/-- Rocq: `Arith.KnuthUp`. -/
def knuthUp : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | 0 => fun a b => b * a
  | n + 1 => fun a => fold 1 (knuthUp n a)

/-- Rocq: `Arith.KnuthUp_zero`. -/
theorem knuthUp_zero : knuthUp.{u} 0 = fun a b => b * a := rfl

/-- Rocq: `Arith.KnuthUp_succ`. -/
theorem knuthUp_succ (n : Nat) : knuthUp.{u} (n + 1) = fun a => fold 1 (knuthUp n a) := rfl

/-- Rocq: `Arith.KnuthUp_one`. -/
theorem knuthUp_one : knuthUp.{u} 1 = fun a b => a ^ b := rfl

/-- Rocq: `Arith.KnuthUp_two`. -/
theorem knuthUp_two : knuthUp.{u} 2 = fun a => fold 1 (fun b => a ^ b) := rfl

/-- Rocq: `Arith.KnuthUp_monotone`. -/
theorem knuthUp_monotone : ∀ (n : Nat) {a b c d : Ordinal.{u}},
    a ≤ b → c ≤ d → knuthUp n a c ≤ knuthUp n b d
  | 0, _, _, _, _, hab, hcd => mul_le_mul hcd hab
  | n + 1, a, b, c, d, hab, hcd => by
    show fold 1 (knuthUp n a) c ≤ fold 1 (knuthUp n b) d
    refine le_trans (fold_least (fold 1 (knuthUp n b)) (fold_above_z 1 _)
      (fun _ _ h => knuthUp_monotone n (le_refl a) h) (fun x i => ?_) c)
      (fold_monotone (fun _ _ h => knuthUp_monotone n (le_refl b) h) c d hcd)
    exact le_trans (knuthUp_monotone n hab (le_refl _)) (fold_unfold_le 1 (knuthUp n b) x i)

/-- Rocq: `Arith.KnuthUp_continuous`. -/
theorem knuthUp_continuous : ∀ (n : Nat) (a : Ordinal.{u}), 0 < n →
    StronglyContinuous (knuthUp n a)
  | n + 1, a, _ => fold_strongly_continuous 1 (knuthUp n a)

/-- Rocq: `Arith.KnuthUp_one_eq`. -/
theorem knuthUp_one_eq : ∀ (n : Nat) (a : Ordinal.{u}), 0 < a → knuthUp n a 1 ≈ a
  | 0, a, _ => one_mul a
  | n + 1, a, ha => by
    show fold 1 (knuthUp n a) 1 ≈ a
    refine equiv_intro ?_ ?_
    · rw [fold_unfold]
      refine lub_least (succ_least ha) (sup_least fun _ => ?_)
      exact le_trans (knuthUp_monotone n (le_refl a) (fold_zero 1 _).le) (knuthUp_one_eq n a ha).le
    · calc a ≤ knuthUp n a 1 := (knuthUp_one_eq n a ha).ge
        _ ≤ knuthUp n a (fold 1 (knuthUp n a) 0) := knuthUp_monotone n (le_refl a) (fold_zero 1 _).ge
        _ ≤ fold 1 (knuthUp n a) 1 := fold_unfold_le 1 (knuthUp n a) 1 PUnit.unit

private theorem one_le_knuthUp : ∀ (n : Nat) (a x : Ordinal.{u}), 0 < n → 1 ≤ knuthUp n a x
  | n + 1, a, x, _ => fold_above_z 1 (knuthUp n a) x

/-- Rocq: `Arith.KnuthUp_omega_fix`. -/
theorem knuthUp_omega_fix (n : Nat) (a : Ordinal.{u}) (hn : 0 < n) (_ha : 0 < a) :
    knuthUp n a (knuthUp (n + 1) a ω) ≈ knuthUp (n + 1) a ω := by
  show knuthUp n a (fold 1 (knuthUp n a) ω) ≈ fold 1 (knuthUp n a) ω
  have hmono : ∀ x y, x ≤ y → knuthUp n a x ≤ knuthUp n a y :=
    fun _ _ h => knuthUp_monotone n (le_refl a) h
  refine equiv_intro ?_ ?_
  · have hsup : fold 1 (knuthUp n a) ω ≤ sup fun i : (ω : Ordinal.{u}).Carrier =>
        fold 1 (knuthUp n a) (ω i) := by
      rw [fold_unfold]
      refine lub_least (le_trans (fold_above_z 1 _ _)
        (sup_le (fun i : (ω : Ordinal.{u}).Carrier => fold 1 (knuthUp n a) (ω i)) ⟨0⟩))
        (sup_least fun i => ?_)
      exact le_trans (fold_unfold_le 1 (knuthUp n a) (succ (ω i)) PUnit.unit)
        (sup_le (fun i : (ω : Ordinal.{u}).Carrier => fold 1 (knuthUp n a) (ω i)) ⟨i.down + 1⟩)
    calc knuthUp n a (fold 1 (knuthUp n a) ω)
        ≤ knuthUp n a (sup fun i : (ω : Ordinal.{u}).Carrier => fold 1 (knuthUp n a) (ω i)) :=
          hmono _ _ hsup
      _ ≤ sup fun i : (ω : Ordinal.{u}).Carrier => knuthUp n a (fold 1 (knuthUp n a) (ω i)) :=
          knuthUp_continuous n a hn _ _ ⟨0⟩
      _ ≤ fold 1 (knuthUp n a) ω := sup_least fun i => fold_unfold_le 1 (knuthUp n a) ω i
  · rw [fold_unfold 1 (knuthUp n a) ω]
    exact lub_least (one_le_knuthUp n a _ hn) (sup_least fun i =>
      hmono _ _ (fold_monotone hmono _ _ (index_le ω i)))

/-- Rocq: `Arith.KnuthUp_saturates`. -/
theorem knuthUp_saturates (n : Nat) (a : Ordinal.{u}) (hn : 0 < n) (ha : 0 < a) :
    ∀ b : Ordinal.{u}, knuthUp (n + 1) a b ≤ knuthUp (n + 1) a ω
  | mk B g => by
    show fold 1 (knuthUp n a) (mk B g) ≤ fold 1 (knuthUp n a) ω
    rw [fold_unfold 1 (knuthUp n a) (mk B g)]
    refine lub_least (fold_above_z 1 _ _) (sup_least fun i => ?_)
    exact le_trans (knuthUp_monotone n (le_refl a) (knuthUp_saturates n a hn ha (g i)))
      (knuthUp_omega_fix n a hn ha).le

/-- Rocq: `Arith.KnuthUp_not_increasing`. -/
theorem knuthUp_not_increasing : ∀ n : Nat, 1 < n →
    (∀ a b c : Ordinal.{u}, b < c → knuthUp n a b < knuthUp n a c) → False
  | n + 1, hn, h =>
    lt_irrefl (knuthUp (n + 1) ω (succ ω))
      (lt_of_le_of_lt (knuthUp_saturates n ω (Nat.lt_of_succ_lt_succ hn) omega_gt0 (succ ω))
        (h ω ω (succ ω) (succ_lt ω)))

/-- Rocq: `Arith.KnuthUp2_epsilon_number`. -/
theorem knuthUp2_epsilon_number {a : Ordinal.{u}} (ha : ω ≤ a) :
    knuthUp 2 a ω ≈ ω ^ knuthUp 2 a ω :=
  equiv_intro (increasing_inflationary (fun _ _ h => pow_lt_pow_right omega_gt1 h) _)
    (le_trans (pow_le_pow_left ha _)
      (knuthUp_omega_fix 1 a Nat.zero_lt_one (lt_of_lt_of_le omega_gt0 ha)).le)

/-! ## Addition of finite ordinals -/

/-- Rocq: `Arith.add_cancel_finite`. -/
theorem add_cancel_finite (n : (ω : Ordinal.{u}).Carrier) {x y : Ordinal.{u}}
    (h : x + ω n ≈ y + ω n) : x ≈ y := by
  obtain ⟨n⟩ := n
  induction n with
  | zero => exact equiv_trans (equiv_symm (add_zero x)) (equiv_trans h (add_zero y))
  | succ n ih =>
    exact ih (succ_cancel_eq (equiv_trans (equiv_symm (add_succ x _))
      (equiv_trans h (add_succ y _))))

/-- Rocq: `Arith.onePlus_finite_succ`. -/
theorem onePlus_finite_succ : ∀ m : Nat, 1 + ofNat.{u} m ≈ succ (ofNat m)
  | 0 => add_zero 1
  | m + 1 => equiv_trans (add_succ 1 _) (succ_congruence (onePlus_finite_succ m))

/-- Rocq: `Arith.onePlus_lt_cancel`. -/
theorem onePlus_lt_cancel (y : Ordinal.{u}) : ∀ x : Ordinal.{u}, 1 + x < 1 + y → x < y := by
  induction y using ltRec with
  | ind y ih =>
    intro x h
    rw [add_unfold 1 y] at h
    match lub_lt h with
    | .inl h =>
      obtain ⟨_, hu⟩ := lt_elim h
      exact (lt_irrefl 0 (lt_of_lt_of_le (succ_lt 0) (le_trans (le_add_right 1 x) hu))).elim
    | .inr h =>
      obtain ⟨q, hq⟩ := sup_lt h
      obtain ⟨_, hq'⟩ := lt_elim hq
      exact lt_intro q (le_intro fun a =>
        ih (y q) (index_lt y q) (x a) (lt_of_lt_of_le (add_lt_add_left 1 (index_lt x a)) hq'))

/-- Rocq: `Arith.lt_onePlus`. -/
theorem lt_onePlus (x : Ordinal.{u}) : ∀ y : Ordinal.{u}, x < y → 1 + x ≤ y := by
  induction x using ltRec with
  | ind x ih =>
    intro y hy
    rw [add_unfold]
    refine lub_least (succ_least (lt_of_le_of_lt (zero_least x) hy))
      (sup_least fun i => succ_least ?_)
    obtain ⟨q, hq⟩ := lt_elim hy
    exact lt_intro q (ih (x i) (index_lt x i) (y q) (lt_of_lt_of_le (index_lt x i) hq))

end Ordinal

end ConstructiveOrdinals
