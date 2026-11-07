import ConstructiveOrdinals.Operators

/-!
# Classical consequences, and reverse results

Port of `Ordinal/Classical.v`.

The first part shows that the excluded middle makes ordinals behave
classically. In Rocq, these results live in a section with
`Hypothesis EM : excluded_middle`; here each takes `(em : ExcludedMiddle)` as
an explicit argument.

The second part proves reverse results: several reasoning principles about
these ordinals imply (weak) excluded middle. The workhorse is the truth
ordinal of a proposition, which is `0` when the proposition is false and `1`
when it is true. Deciding which case holds is equivalent to the excluded
middle.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

/-! ## Consequences of the excluded middle -/

/-- Rocq: `Classical.ord_swizzle`. -/
theorem ord_swizzle (em : ExcludedMiddle) (x : Ordinal.{u}) :
    ∀ y : Ordinal.{u}, (¬ x ≤ y → y < x) ∧ (¬ x < y → y ≤ x) := by
  induction x using ltRec with
  | ind x ihx =>
    intro y
    induction y using ltRec with
    | ind y ihy =>
      refine ⟨fun h => ?_, fun h => le_intro fun a => (ihy (y a) (index_lt y a)).1 fun hle =>
        h (lt_intro a hle)⟩
      match em (∃ a, ¬ x a < y) with
      | .inl ⟨a, ha⟩ => exact lt_intro a ((ihx (x a) (index_lt x a) y).2 ha)
      | .inr hn =>
        exact (h (le_intro fun a => match em (x a < y) with
          | .inl h' => h'
          | .inr h' => (hn ⟨a, h'⟩).elim)).elim

/-- Classically, ordinals form a total order. Rocq: `Classical.order_total`. -/
theorem order_total (em : ExcludedMiddle) (x y : Ordinal.{u}) : x ≤ y ∨ y < x :=
  match em (x ≤ y) with
  | .inl h => .inl h
  | .inr h => .inr ((ord_swizzle em x y).1 h)

/-- Rocq: `Classical.order_trichotomy`. -/
theorem order_trichotomy (em : ExcludedMiddle) (x y : Ordinal.{u}) :
    x < y ∨ x ≈ y ∨ y < x :=
  match order_total em x y with
  | .inr h => .inr (.inr h)
  | .inl hxy =>
    match order_total em y x with
    | .inl hyx => .inr (.inl (equiv_intro hxy hyx))
    | .inr h => .inl h

/-- Classically, `x ≤ y` splits as `x < y` or `x ≈ y`.
Rocq: `Classical.order_splits`. -/
theorem order_splits (em : ExcludedMiddle) (x y : Ordinal.{u}) :
    x ≤ y ↔ (x < y ∨ x ≈ y) :=
  ⟨fun h => match order_total em y x with
    | .inl hyx => .inr (equiv_intro h hyx)
    | .inr hlt => .inl hlt,
   fun h => h.elim le_of_lt Equiv.le⟩

/-- Rocq: `Classical.max_or_ascending`. -/
theorem max_or_ascending (em : ExcludedMiddle) (A : Type u) (f : A → Ordinal.{u}) :
    HasMaxElement A f ∨ AscendingSet A f :=
  match em (HasMaxElement A f) with
  | .inl h => .inl h
  | .inr hn => .inr fun a =>
    match em (∃ a', f a < f a') with
    | .inl h => h
    | .inr h' => (hn ⟨a, fun a' => match order_total em (f a') (f a) with
        | .inl h => h
        | .inr h => (h' ⟨a', h⟩).elim⟩).elim

/-- Classically, every ordinal is zero, a successor or a limit.
Rocq: `Classical.ordinal_discriminate`. -/
theorem ordinal_discriminate (em : ExcludedMiddle) (x : Ordinal.{u}) :
    IsZero x ∨ IsSucc x ∨ IsLimit x :=
  match max_or_ascending em x.Carrier x.size with
  | .inl h => .inr (.inl h)
  | .inr hasc =>
    match em (Nonempty x.Carrier) with
    | .inl h => .inr (.inr ⟨h, hasc⟩)
    | .inr h => .inl h

/-- Every indexed family of classical ordinals is directed, which follows
easily from totality. Rocq: `Classical.ord_directed`. -/
theorem ord_directed (em : ExcludedMiddle) (A : Type u) (f : A → Ordinal.{u}) : Directed A f :=
  fun a₁ a₂ => match order_total em (f a₁) (f a₂) with
    | .inl h => ⟨a₂, h, le_refl _⟩
    | .inr h => ⟨a₁, le_refl _, le_of_lt h⟩

/-- Classically, every ordinal is complete. Rocq: `Classical.ord_complete`. -/
theorem ord_complete (em : ExcludedMiddle) : ∀ x : Ordinal.{u}, Complete x
  | mk A f => Complete.intro (ord_directed em A f) (em _) fun a => ord_complete em (f a)

/-- Classically, ordinals are well-ordered by `≤`: every nonempty class of
ordinals (given by a predicate) has a least element.
Rocq: `Classical.ord_well_ordered`. -/
theorem ord_well_ordered (em : ExcludedMiddle) (P : Ordinal.{u} → Prop) (o : Ordinal.{u}) :
    P o → ∃ o₀, P o₀ ∧ ∀ o', P o' → o₀ ≤ o' := by
  induction o using ltRec with
  | ind o ih =>
    intro hp
    match em (∃ o₁, P o₁ ∧ o₁ < o) with
    | .inl ⟨o₁, h, h₁⟩ => exact ih o₁ h₁ h
    | .inr hn => exact ⟨o, hp, fun o' ho' => (ord_swizzle em o' o).2 fun hlt => hn ⟨o', ho', hlt⟩⟩

/-- Every nonempty indexed family of ordinals has a least element.
Rocq: `Classical.ord_well_ordered_indexed`. -/
theorem ord_well_ordered_indexed (em : ExcludedMiddle) (A : Type u) (f : A → Ordinal.{u})
    (hinh : Nonempty A) : ∃ a, ∀ a', f a ≤ f a' := by
  obtain ⟨a⟩ := hinh
  obtain ⟨_, ⟨a₀, rfl⟩, hleast⟩ := ord_well_ordered em (fun o => ∃ a, f a = o) (f a) ⟨a, rfl⟩
  exact ⟨a₀, fun a' => hleast _ ⟨a', rfl⟩⟩

/-- Classically, ordinals have the traditional induction principle with cases
for zero, successor and limit ordinals.
Rocq: `Classical.classical_ordinal_induction`. -/
theorem classical_ordinal_induction (em : ExcludedMiddle) (P : Ordinal.{u} → Prop)
    (heq : ∀ x y, x ≈ y → P x → P y) (hzero : P 0) (hsucc : ∀ o, P o → P (succ o))
    (hlimit : ∀ x, (∀ a, a < x → P a) → IsLimit x → P x) (x : Ordinal.{u}) : P x := by
  induction x using ltRec with
  | ind x ih =>
    match ordinal_discriminate em x with
    | .inl hz => exact heq 0 x (equiv_symm ((isZero_iff x).1 hz)) hzero
    | .inr (.inl hs) =>
      obtain ⟨o, ho⟩ := (isSucc_iff x).1 hs
      exact heq _ _ (equiv_symm ho) (hsucc o (ih o (lt_of_lt_of_le (succ_lt o) ho.ge)))
    | .inr (.inr hl) => exact hlimit x ih hl

/-- Rocq: `Classical.inf_loop_member`. -/
theorem infLoop_member (em : ExcludedMiddle) (hc : DependentFunctionalChoice.{u})
    (x : Ordinal.{u}) (A : Type u) (f : A → Ordinal.{u}) :
    infLoop x A f ≈ x ∨ ∃ i, infLoop x A f ≈ f i :=
  match order_total em x (infLoop x A f) with
  | .inl h => .inl (equiv_intro (infLoop_lower_bound x A f).1 h)
  | .inr _ =>
    match em (∃ i, f i ≤ infLoop x A f) with
    | .inl ⟨i, hi⟩ => .inr ⟨i, equiv_intro ((infLoop_lower_bound x A f).2 i) hi⟩
    | .inr hn => by
      have hlt : ∀ i, infLoop x A f < f i := fun i =>
        match order_total em (f i) (infLoop x A f) with
        | .inl h' => (hn ⟨i, h'⟩).elim
        | .inr h' => h'
      match order_total em x (infLoop x A f) with
      | .inl h => exact .inl (equiv_intro (infLoop_lower_bound x A f).1 h)
      | .inr hx =>
        have h := infLoop_greatest hc x A f _ (succ_least hx) fun i => succ_least (hlt i)
        exact (lt_irrefl _ (le_elim h PUnit.unit)).elim

/-- Classically (with choice), the infimum of a family is one of its members.
Rocq: `Classical.inf_member`. -/
theorem inf_member (em : ExcludedMiddle) (hc : DependentFunctionalChoice.{u}) (A : Type u)
    (i₀ : A) (f : A → Ordinal.{u}) : ∃ i, inf A i₀ f ≈ f i :=
  match infLoop_member em hc (f i₀) A f with
  | .inl h => ⟨i₀, h⟩
  | .inr h => h

/-! ## Reverse results -/

/-- The truth ordinal of a proposition: `0` if it is false and `1` if it is
true. Rocq: `Classical.truth_ord`. -/
def truthOrd (P : Prop) : Ordinal.{u} := mk (ULift.{u} (PLift P)) fun _ => 0

/-- Rocq: `Classical.truth_ord_false`. -/
theorem truthOrd_false {P : Prop} (h : ¬P) : truthOrd.{u} P ≈ 0 :=
  equiv_intro (le_intro fun ⟨⟨hp⟩⟩ => (h hp).elim) (zero_least _)

/-- Rocq: `Classical.truth_ord_true`. -/
theorem truthOrd_true {P : Prop} (h : P) : truthOrd.{u} P ≈ 1 :=
  equiv_intro (le_intro fun _ => succ_lt 0)
    (le_intro fun _ => lt_intro (show (truthOrd.{u} P).Carrier from ⟨⟨h⟩⟩) (le_refl _))

/-- Deciding zero-ness, even for ordinals below 1, implies the excluded
middle. Rocq: `Classical.zero_dec_EM`. -/
theorem zero_dec_EM (h : ∀ x : Ordinal.{u}, x ≤ 1 → x ≤ 0 ∨ 0 < x) : ExcludedMiddle := fun P =>
  match h (truthOrd P) (le_intro fun _ => succ_lt 0) with
  | .inl h => .inr fun hp => (le_subord h ⟨⟨hp⟩⟩).elim fun b _ => PEmpty.elim b
  | .inr h => .inl ((lt_elim h).elim fun ⟨⟨hp⟩⟩ _ => hp)

/-- Totality of the order implies the excluded middle.
Rocq: `Classical.order_total_EM`. -/
theorem order_total_EM (h : ∀ x y : Ordinal.{u}, x ≤ y ∨ y < x) : ExcludedMiddle :=
  zero_dec_EM fun x _ => h x 0

/-- Splitting `x ≤ y` as `x < y` or `x ≈ y` implies the excluded middle.
Rocq: `Classical.order_splits_EM`. -/
theorem order_splits_EM (h : ∀ x y : Ordinal.{u}, x ≤ y ↔ (x < y ∨ x ≈ y)) :
    ExcludedMiddle := fun P =>
  match (h (truthOrd P) 1).mp (le_intro fun _ => succ_lt 0) with
  | .inl hlt =>
    .inr fun hp => (lt_elim hlt).elim fun _ hle =>
      (le_subord (show truthOrd.{u} P ≤ 0 from hle) ⟨⟨hp⟩⟩).elim fun b _ => PEmpty.elim b
  | .inr heq => .inl ((lt_elim (le_elim heq.ge PUnit.unit)).elim fun ⟨⟨hp⟩⟩ _ => hp)

/-- Completeness is intensional: it is not invariant under `≈`. The ordinal
with children `n ⊔ truthOrd P` is equivalent to `ω`, which is complete, but
completeness of its child `0 ⊔ truthOrd P` decides `P`.
Rocq: `Classical.complete_intensional_EM`. -/
theorem complete_intensional_EM
    (h : ∀ x y : Ordinal.{u}, x ≈ y → Complete x → Complete y) : ExcludedMiddle := fun P => by
  let y : Ordinal.{u} := mk (ULift Nat) fun n => ofNat n.down ⊔ truthOrd P
  have hy : ω ≈ y := equiv_intro
    (le_intro fun n => lt_intro (show y.Carrier from n) (lub_le1 _ _))
    (le_intro fun n => lt_intro (show (ω : Ordinal.{u}).Carrier from ⟨n.down + 1⟩)
      (lub_least (le_of_lt (succ_lt _))
        (le_intro fun _ => lt_of_le_of_lt (zero_least _) (succ_lt _))))
  have hc : Complete (ofNat.{u} 0 ⊔ truthOrd P) :=
    complete_subord (h _ _ hy omega_complete) (show y.Carrier from ⟨0⟩)
  match complete_zeroDec hc with
  | .inl hz =>
    exact .inr fun hp => lt_irrefl 0 (lt_of_lt_of_le (lt_of_lt_of_le
      (lt_intro (show (truthOrd.{u} P).Carrier from ⟨⟨hp⟩⟩) (le_refl _)) (lub_le2 _ _)) hz)
  | .inr hpos =>
    match lub_lt hpos with
    | .inl h0 => exact ((lt_elim h0).elim fun b _ => PEmpty.elim b)
    | .inr ht => exact .inl ((lt_elim ht).elim fun ⟨⟨hp⟩⟩ _ => hp)

/-- If every ordinal is complete, the excluded middle holds.
Rocq: `Classical.complete_EM`. -/
theorem complete_EM (h : ∀ x : Ordinal.{u}, Complete x) : ExcludedMiddle :=
  zero_dec_EM fun x _ => complete_zeroDec (h x)

/-- Well-ordering implies the weak excluded middle.
Rocq: `Classical.ord_well_ordered_WEM`. -/
theorem ord_well_ordered_WEM
    (hwo : ∀ (P : Ordinal.{u} → Prop) (o : Ordinal.{u}), P o →
      ∃ o₀, P o₀ ∧ ∀ o', P o' → o₀ ≤ o') : WeakExcludedMiddle := fun P => by
  obtain ⟨x₀, hx₀, hleast⟩ :=
    hwo (fun o => o = truthOrd P ∨ o = truthOrd (¬P)) (truthOrd P) (.inl rfl)
  rcases hx₀ with rfl | rfl
  · refine .inr fun hp => ?_
    obtain ⟨⟨⟨hnp⟩⟩, _⟩ := lt_elim (le_elim (hleast (truthOrd (¬P)) (.inr rfl))
      (show (truthOrd.{u} P).Carrier from ⟨⟨hp⟩⟩))
    exact hnp hp
  · refine .inl fun hnp => ?_
    obtain ⟨⟨⟨hp⟩⟩, _⟩ := lt_elim (le_elim (hleast (truthOrd P) (.inl rfl))
      (show (truthOrd.{u} (¬P)).Carrier from ⟨⟨hnp⟩⟩))
    exact hnp hp

/-- The pair of truth ordinals for `P` and `¬P`, indexed by `Bool`. -/
private def truthPair (P : Prop) (b : ULift.{u} Bool) : Ordinal.{u} :=
  cond b.down (truthOrd P) (truthOrd (¬P))

/-- If every ordinal is directed, the weak excluded middle holds.
Rocq: `Classical.directed_WEM`. -/
theorem directed_WEM (h : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) :
    WeakExcludedMiddle := fun P => by
  obtain ⟨⟨b⟩, hb₁, hb₂⟩ := h (mk (ULift Bool) (truthPair P)) ⟨true⟩ ⟨false⟩
  cases b
  · refine .inr fun hp => ?_
    obtain ⟨⟨⟨hnp⟩⟩, _⟩ := lt_elim (le_elim (show truthOrd P ≤ truthOrd (¬P) from hb₁)
      (show (truthOrd.{u} P).Carrier from ⟨⟨hp⟩⟩))
    exact hnp hp
  · refine .inl fun hnp => ?_
    obtain ⟨⟨⟨hp⟩⟩, _⟩ := lt_elim (le_elim (show truthOrd (¬P) ≤ truthOrd P from hb₂)
      (show (truthOrd.{u} (¬P)).Carrier from ⟨⟨hnp⟩⟩))
    exact hnp hp

/-- If infima are always attained, the weak excluded middle holds.
Rocq: `Classical.inf_member_WEM`. -/
theorem inf_member_WEM
    (h : ∀ (A : Type u) (i₀ : A) (f : A → Ordinal.{u}), ∃ i, inf A i₀ f ≈ f i) :
    WeakExcludedMiddle := fun P => by
  obtain ⟨⟨i⟩, hi⟩ := h (ULift Bool) ⟨true⟩ (truthPair P)
  cases i
  · refine .inl fun hnp => ?_
    obtain ⟨⟨j, _⟩, _⟩ := lt_elim (le_elim hi.ge (show (truthOrd.{u} (¬P)).Carrier from ⟨⟨hnp⟩⟩))
    exact hnp j.down.down
  · refine .inr fun hp => ?_
    obtain ⟨⟨_, k⟩, _⟩ := lt_elim (le_elim hi.ge (show (truthOrd.{u} P).Carrier from ⟨⟨hp⟩⟩))
    exact (k ⟨false⟩).down.down hp

/-- A second truth ordinal: `1` if the proposition is false and `ω` if it is
true. Rocq: `Classical.truth_ord'`. -/
def truthOrd' (P : Prop) : Ordinal.{u} :=
  sup fun n : ULift.{u} Nat => 1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down

/-- Rocq: `Classical.truth_ord'_false`. -/
theorem truthOrd'_false {P : Prop} (h : ¬P) : truthOrd'.{u} P ≈ 1 :=
  equiv_intro
    (sup_least fun _ => lub_least (le_refl _) (le_intro fun ⟨⟨hp⟩⟩ => (h hp).elim))
    (le_trans (lub_le1 1 _) (sup_le (fun n : ULift.{u} Nat =>
      1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down) ⟨0⟩))

/-- Rocq: `Classical.truth_ord'_true`. -/
theorem truthOrd'_true {P : Prop} (h : P) : truthOrd'.{u} P ≈ ω :=
  equiv_intro
    (sup_least fun n => lub_least (le_of_lt omega_gt1) (le_intro fun _ => index_lt ω n))
    (le_intro fun n => lt_of_lt_of_le
      (lt_of_lt_of_le (lt_intro (show (mk (ULift.{u} (PLift P)) fun _ => ofNat n.down).Carrier
        from ⟨⟨h⟩⟩) (le_refl _)) (lub_le2 _ _))
      (sup_le (fun n : ULift.{u} Nat => 1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down) n))

/-- Rocq: `Classical.truth_ord'_complete`. -/
theorem truthOrd'_complete (P : Prop) : Complete (truthOrd'.{u} P) := by
  refine Complete.intro ?_ (.inl ⟨⟨⟨0⟩, .inl PUnit.unit⟩⟩) ?_
  · rintro ⟨n₁, q₁⟩ ⟨n₂, q₂⟩
    rcases q₁ with _ | p₁ <;> rcases q₂ with _ | p₂
    · exact ⟨⟨⟨0⟩, .inl PUnit.unit⟩, le_refl _, le_refl _⟩
    · exact ⟨⟨n₂, .inr p₂⟩, zero_least _, le_refl _⟩
    · exact ⟨⟨n₁, .inr p₁⟩, le_refl _, zero_least _⟩
    · exact ⟨⟨⟨Nat.max n₁.down n₂.down⟩, .inr p₁⟩,
        ofNat_monotone (Nat.le_max_left _ _), ofNat_monotone (Nat.le_max_right _ _)⟩
  · rintro ⟨n, _ | _⟩
    · exact zero_complete
    · exact ofNat_complete n.down

/-- Deciding between successor and limit, even for complete ordinals between
`0` and `ω`, implies the excluded middle.
Rocq: `Classical.succ_limit_dec_EM`. -/
theorem succ_limit_dec_EM
    (hdec : ∀ x : Ordinal.{u}, 0 < x → x ≤ ω → Complete x → IsSucc x ∨ IsLimit x) :
    ExcludedMiddle := fun P => by
  have h₀ : 0 < truthOrd'.{u} P :=
    lt_of_lt_of_le (succ_lt 0) (le_trans (lub_le1 1 _) (sup_le (fun n : ULift.{u} Nat =>
      1 ⊔ mk (ULift.{u} (PLift P)) fun _ => ofNat n.down) ⟨0⟩))
  have hle : truthOrd'.{u} P ≤ ω :=
    sup_least fun i => lub_least (succ_least omega_gt0) (le_intro fun _ => index_lt ω i)
  match hdec (truthOrd' P) h₀ hle (truthOrd'_complete P) with
  | .inl ⟨⟨i, s⟩, hmax⟩ =>
    refine .inr fun hp => ?_
    rcases s with _ | _
    · have h := hmax ⟨⟨1⟩, .inr ⟨⟨hp⟩⟩⟩
      exact (le_subord h PUnit.unit).elim fun b _ => PEmpty.elim b
    · have h := hmax ⟨⟨i.down + 1⟩, .inr ⟨⟨hp⟩⟩⟩
      exact lt_irrefl _ (le_elim h PUnit.unit)
  | .inr ⟨_, hasc⟩ =>
    refine .inl ?_
    obtain ⟨⟨_, q⟩, h⟩ := hasc ⟨⟨0⟩, .inl PUnit.unit⟩
    rcases q with _ | hp
    · exact (lt_irrefl _ h).elim
    · exact hp.down.down

end Ordinal

end ConstructiveOrdinals
