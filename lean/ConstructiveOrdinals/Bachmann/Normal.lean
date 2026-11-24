import ConstructiveOrdinals.Bachmann.Cfe

/-!
# Normality of Bachmann's hierarchy, proved directly

In `Bachmann/Calibration` the hierarchy is calibrated against known normal
functions (Veblen, Schütte's columns), which takes us as far as the Large
Veblen Ordinal. Beyond that there is nothing to calibrate against, so here we
prove normality of `φ` directly.

The proof splits in two; (A) and the definition of `bphi` are in
`Bachmann/Cfe`, and the agreement of `bphi` with Bachmann's `bach` in
`Bachmann/Agree`.

- (A) A generic construction, independent of index trees. Given a base normal
  function `f` and a family of normal functions `F_i`, let `E y` be `f y`
  joined with the least fixpoints, above the previous values, of the nonempty
  compositions `F_i ∘ F_{i_1} ∘ … ∘ F_{i_n} ∘ f`. The compositions form a
  directed family (any two are dominated by their concatenation), and every
  one of them dominates `f`, so the family of terms is directed without
  deciding whether there are any `F_i`. With no `F_i`, `E` is `f` itself;
  otherwise `E` enumerates the common fixpoints of `f` and the `F_i`. Strict
  monotonicity of `E` does need that decision, but only as a proposition.
- (B) The Bachmann-specific content. The hierarchy `bphi` applies `E` at each
  node to the node's components; it is normal by construction on trees whose
  nodes decide whether they have components. Bachmann's `φ` takes least
  fixpoints of the components one at a time, and agrees with `bphi` when the
  components are suitably nested and directed. We show, by structural
  conditions preserved by the tree arithmetic, that this holds on the
  canonical trees up to `ε_{Ω+1}`; in particular `φ_{ε_{Ω+1}}(0)` is the
  Bachmann–Howard ordinal.

Ported from the Rocq file `BachmannNormal.v`.

Lean note: the first argument of `bslt` is uniform in Rocq's constructors, so
here it is a parameter of the inductive predicate.
-/

namespace ConstructiveOrdinals

universe u

namespace Bachmann

open Ordinal BOrd

/-! ## `φ` is monotone in the index, for `bsub` -/

/-- Rocq: `BachmannNormal.bphi_mono_index`. -/
theorem bphi_mono_index (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ x y, x ≤ y → f x ≤ f y) :
    ∀ y : BOrd.{u}, BFam y →
      (∀ a b, a ≤ b → bphi f y a ≤ bphi f y b) ∧ (∀ x, bsub x y → ∀ z, bphi f x z ≤ bphi f y z)
  | bnode B g' D h', ⟨Hy1, Hy2, Hy3⟩ =>
    have HFm : ∀ k x y, x ≤ y → bphi_fam f g' h' k x ≤ bphi_fam f g' h' k y := fun k x y hxy =>
      match k with
      | .inl b => (bphi_mono_index f hf (g' b) (Hy1 b)).1 _ _ hxy
      | .inr d => (bphi_mono_index f hf (h' d y) (Hy2 d y)).2 _ (Hy3 d x y hxy) 0
    ⟨cfe_monotone_gen f (B ⊕ D) (bphi_fam f g' h') hf HFm, fun x hs z =>
      match x, hs with
      | bnode A g C h, ⟨Hs1, Hs2⟩ =>
        cfe_mono_family f (A ⊕ C) (B ⊕ D) (bphi_fam f g h) (bphi_fam f g' h') hf HFm (fun k =>
          match k with
          | .inl a => let ⟨b, hb⟩ := Hs1 a; ⟨.inl b, fun x => (bphi_mono_index f hf (g' b) (Hy1 b)).2 _ hb x⟩
          | .inr c => let ⟨d, hd⟩ := Hs2 c
            ⟨.inr d, fun x => (bphi_mono_index f hf (h' d x) (Hy2 d x)).2 _ (hd x) 0⟩) z⟩

/-! ## Strict increase along a family -/

/-- `x` lies strictly below `y` if it lies below a small child of `y`, or
(recursively) strictly below a small child of `y` or a member of one of `y`'s
Ω-families at a finite argument. Rocq: `BachmannNormal.bslt`. -/
inductive bslt (x : BOrd.{u}) : BOrd.{u} → Prop
  /-- Rocq: `BachmannNormal.bslt_small`. -/
  | small (y : BOrd.{u}) (b : bsmall y) : bsub x (bsmallSz y b) → bslt x y
  /-- Rocq: `BachmannNormal.bslt_big`. -/
  | big (y : BOrd.{u}) (d : bbig y) (n : Nat) : bslt x (bbigSz y d (ofNat n)) → bslt x y
  /-- Rocq: `BachmannNormal.bslt_desc`. -/
  | desc (y : BOrd.{u}) (b : bsmall y) : bslt x (bsmallSz y b) → bslt x y

/-- Rocq: `BachmannNormal.fix_onePlus_finite`. -/
theorem fix_onePlus_finite (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (z : Ordinal.{u})
    (hz : Complete z) (hfz : f z ≤ z) : ∀ n : Nat, ofNat n ≤ z
  | 0 => zero_least _
  | n + 1 => succ_least (lt_of_lt_of_le (onePlus_finite n)
      (le_trans (add_le_add (le_refl 1) (fix_onePlus_finite f hf z hz hfz n))
        (le_trans (onePlus_least_normal hf z hz) hfz)))

/-! ## Structural conditions on Ω-families -/

/-- Rocq: `BachmannNormal.bcanon`. -/
def BCanon : BOrd.{u} → Prop
  | bnode _ g _ h =>
    (∀ a, BCanon (g a)) ∧ (∀ c ξ, BCanon (h c ξ)) ∧ (∀ c ξ ξ', ξ ≤ ξ' → bsub (h c ξ) (h c ξ')) ∧
      (∀ c ξ ξ', Complete ξ' → ξ < ξ' → bslt (h c ξ) (h c ξ')) ∧
      ∀ c (B : Type u) (k : B → Ordinal.{u}) (_ : B), Directed B k → (∀ b, Complete (k b)) →
        bsub (h c (sup k)) (bsup fun b => h c (k b))

/-- Rocq: `BachmannNormal.bcanon_bfam`. -/
theorem bcanon_bfam : ∀ T : BOrd.{u}, BCanon T → BFam T
  | bnode _ g _ h, ⟨H1, H2, H3, _⟩ => ⟨fun a => bcanon_bfam (g a) (H1 a), fun c ξ => bcanon_bfam (h c ξ) (H2 c ξ), H3⟩

/-! ## First instances: ordinary ordinals and `Ω` -/

/-- Rocq: `BachmannNormal.bcanon_embed`. -/
theorem bcanon_embed : ∀ ξ : Ordinal.{u}, BCanon (embed ξ)
  | mk _ k => ⟨fun a => bcanon_embed (k a), fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e),
      fun e => (nomatch e)⟩

/-- Rocq: `BachmannNormal.embed_small`. -/
theorem embed_small (x : Ordinal.{u}) (c : x) : ∃ q, bsmallSz (embed x) q = embed (x c) := by
  cases x; exact ⟨c, rfl⟩

/-- Rocq: `BachmannNormal.bcanon_Ω`. -/
theorem bcanon_Ω : BCanon bOmega.{u} := by
  refine ⟨fun e => (nomatch e), fun _ ξ => bcanon_embed ξ, fun _ ξ ξ' H => bsub_embed ξ ξ' H, ?_, ?_⟩
  · intro _ ξ ξ' _ H
    cases ξ' with
    | mk X' k' =>
    obtain ⟨j, hj⟩ := lt_elim H
    exact .small (embed (mk X' k')) j (bsub_embed ξ (k' j) hj)
  · intro _ B k _ _ _
    refine bsub_intro _ _ (fun s => ?_) (fun e => (nomatch e))
    obtain ⟨b, c⟩ := s
    obtain ⟨q, hq⟩ := embed_small (k b) c
    refine ⟨⟨b, q⟩, ?_⟩
    show bsub (embed (k b c)) (bsmallSz (embed (k b)) q)
    rw [hq]
    exact bsub_refl _

/-! ## The arithmetic preserves `BCanon` -/

/-- Rocq: `BachmannNormal.bcanon_small`. -/
theorem bcanon_small (x : BOrd.{u}) (a : bsmall x) (H : BCanon x) : BCanon (bsmallSz x a) := by
  cases x; exact H.1 a

/-- Rocq: `BachmannNormal.bcanon_big`. -/
theorem bcanon_big (x : BOrd.{u}) (c : bbig x) (ξ : Ordinal.{u}) (H : BCanon x) : BCanon (bbigSz x c ξ) := by
  cases x; exact H.2.1 c ξ

/-- Rocq: `BachmannNormal.bcanon_fmono`. -/
theorem bcanon_fmono (x : BOrd.{u}) (c : bbig x) (ξ ξ' : Ordinal.{u}) (H : BCanon x) (h : ξ ≤ ξ') :
    bsub (bbigSz x c ξ) (bbigSz x c ξ') := by
  cases x; exact H.2.2.1 c ξ ξ' h

/-- Rocq: `BachmannNormal.bcanon_fstrict`. -/
theorem bcanon_fstrict (x : BOrd.{u}) (c : bbig x) (ξ ξ' : Ordinal.{u}) (H : BCanon x) (hc : Complete ξ')
    (h : ξ < ξ') : bslt (bbigSz x c ξ) (bbigSz x c ξ') := by
  cases x; exact H.2.2.2.1 c ξ ξ' hc h

/-- Rocq: `BachmannNormal.bcanon_fcont`. -/
theorem bcanon_fcont (x : BOrd.{u}) (c : bbig x) (B : Type u) (k : B → Ordinal.{u}) (b0 : B) (H : BCanon x)
    (hdir : Directed B k) (hk : ∀ b, Complete (k b)) :
    bsub (bbigSz x c (sup k)) (bsup fun b => bbigSz x c (k b)) := by
  cases x; exact H.2.2.2.2 c B k b0 hdir hk

/-- Rocq: `BachmannNormal.bcanon_blub`. -/
theorem bcanon_blub (x y : BOrd.{u}) (hx : BCanon x) (hy : BCanon y) : BCanon (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  obtain ⟨H1, H2, H3, H4, H5⟩ := hx
  obtain ⟨H1', H2', H3', H4', H5'⟩ := hy
  refine ⟨fun ab => ?_, fun cd => ?_, fun cd => ?_, fun cd => ?_, fun cd => ?_⟩
  · match ab with
    | .inl a => exact H1 a
    | .inr b => exact H1' b
  · match cd with
    | .inl c => exact H2 c
    | .inr d => exact H2' d
  · match cd with
    | .inl c => exact H3 c
    | .inr d => exact H3' d
  · match cd with
    | .inl c => exact H4 c
    | .inr d => exact H4' d
  · match cd with
    | .inl c => exact H5 c
    | .inr d => exact H5' d

/-- Rocq: `BachmannNormal.bcanon_bsup`. -/
theorem bcanon_bsup {I : Type u} (F : I → BOrd.{u}) (H : ∀ i, BCanon (F i)) : BCanon (bsup F) :=
  ⟨fun p => bcanon_small _ p.2 (H p.1), fun p ξ => bcanon_big _ p.2 ξ (H p.1),
    fun p ξ ξ' hξ => bcanon_fmono _ p.2 ξ ξ' (H p.1) hξ, fun p ξ ξ' hc hξ => bcanon_fstrict _ p.2 ξ ξ' (H p.1) hc hξ,
    fun p B k b0 hdir hk => bcanon_fcont (F p.1) p.2 B k b0 (H p.1) hdir hk⟩

/-- Rocq: `BachmannNormal.bcanon_bzero`. -/
theorem bcanon_bzero : BCanon bzero.{u} :=
  ⟨fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannNormal.bcanon_bsucc`. -/
theorem bcanon_bsucc (x : BOrd.{u}) (H : BCanon x) : BCanon (bsucc x) :=
  ⟨fun _ => H, fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-! ### `bsub` and `bslt` bookkeeping -/

/-- Rocq: `BachmannNormal.bsub_bzero_l`. -/
theorem bsub_bzero_l (x : BOrd.{u}) : bsub bzero x := bsub_intro _ _ (fun e => (nomatch e)) (fun e => (nomatch e))

/-- Rocq: `BachmannNormal.bsub_le_badd`. -/
theorem bsub_le_badd (w z : BOrd.{u}) : bsub w (badd w z) := by
  rw [badd_eq w z]; exact bsub_blub_l _ _

/-- Rocq: `BachmannNormal.bsub_bsup_le`. -/
theorem bsub_bsup_le {I : Type u} (F : I → BOrd.{u}) (i : I) : bsub (F i) (bsup F) :=
  bsub_intro _ _ (fun a => ⟨⟨i, a⟩, bsub_refl _⟩) (fun c => ⟨⟨i, c⟩, fun _ => bsub_refl _⟩)

/-- Rocq: `BachmannNormal.bslt_bsub_l`. -/
theorem bslt_bsub_l (a' a b : BOrd.{u}) (H1 : bsub a' a) (H2 : bslt a b) : bslt a' b := by
  induction H2 with
  | small y j hj => exact .small y j (bsub_trans H1 hj)
  | big y d n _ ih => exact .big y d n ih
  | desc y j _ ih => exact .desc y j ih

/-- Rocq: `BachmannNormal.bslt_bsub_r`. -/
theorem bslt_bsub_r (a b b' : BOrd.{u}) (H : bslt a b) (Hb : bsub b b') : bslt a b' := by
  induction H generalizing b' with
  | small y j hj =>
    obtain ⟨j', hj'⟩ := bsub_small _ _ Hb j
    exact .small b' j' (bsub_trans hj hj')
  | big y d n _ ih =>
    obtain ⟨d', hd'⟩ := bsub_big _ _ Hb d
    exact .big b' d' n (ih _ (hd' _))
  | desc y j _ ih =>
    obtain ⟨j', hj'⟩ := bsub_small _ _ Hb j
    exact .desc b' j' (ih _ hj')

/-- Rocq: `BachmannNormal.bpos`. -/
def bpos (z : BOrd.{u}) : Prop := bslt bzero z

/-- `w` lies strictly below `w + z` whenever `z` is strictly above something.
Rocq: `BachmannNormal.bslt_badd_pos`. -/
theorem bslt_badd_pos (w : BOrd.{u}) : ∀ x z : BOrd.{u}, bslt x z → bslt w (badd w z) := by
  intro x z H
  induction H with
  | small z j _ =>
    obtain ⟨t, ht⟩ := badd_small_r w z j
    exact .small _ t (by rw [ht]; exact bsub_le_badd _ _)
  | big z d n _ ih =>
    obtain ⟨t, ht⟩ := badd_big_r w z d
    exact .big _ t n (by rw [ht]; exact ih)
  | desc z j _ ih =>
    obtain ⟨t, ht⟩ := badd_small_r w z j
    exact .desc _ t (by rw [ht]; exact ih)

/-- Rocq: `BachmannNormal.bslt_badd_r`. -/
theorem bslt_badd_r (x : BOrd.{u}) : ∀ a b : BOrd.{u}, bslt a b → bslt (badd x a) (badd x b) := by
  intro a b H
  induction H with
  | small b j hj =>
    obtain ⟨t, ht⟩ := badd_small_r x b j
    exact .small _ t (by rw [ht]; exact bsub_badd_r _ _ _ hj)
  | big b d n _ ih =>
    obtain ⟨t, ht⟩ := badd_big_r x b d
    exact .big _ t n (by rw [ht]; exact ih)
  | desc b j _ ih =>
    obtain ⟨t, ht⟩ := badd_small_r x b j
    exact .desc _ t (by rw [ht]; exact ih)

/-- Rocq: `BachmannNormal.bsub_badd_bsup`. -/
theorem bsub_badd_bsup (x : BOrd.{u}) {B : Type u} (H : B → BOrd.{u}) (b0 : B) :
    bsub (badd x (bsup H)) (bsup fun b => badd x (H b)) := by
  refine bsub_intro _ _ (fun s => ?_) (fun c => ?_)
  · match badd_small_cases x (bsup H) s with
    | .inl ⟨a, Ha⟩ =>
      obtain ⟨t, Ht⟩ := badd_small_l x (H b0) a
      refine ⟨⟨b0, t⟩, ?_⟩
      rw [Ha]
      show bsub (bsmallSz x a) (bsmallSz (badd x (H b0)) t)
      rw [Ht]
      exact bsub_refl _
    | .inr ⟨⟨b, q⟩, Hq⟩ =>
      obtain ⟨t, Ht⟩ := badd_small_r x (H b) q
      refine ⟨⟨b, t⟩, ?_⟩
      rw [Hq]
      show bsub (badd x (bsmallSz (H b) q)) (bsmallSz (badd x (H b)) t)
      rw [Ht]
      exact bsub_refl _
  · match badd_big_cases x (bsup H) c with
    | .inl ⟨e, He⟩ =>
      obtain ⟨t, Ht⟩ := badd_big_l x (H b0) e
      refine ⟨⟨b0, t⟩, fun ξ => ?_⟩
      rw [He ξ]
      show bsub (bbigSz x e ξ) (bbigSz (badd x (H b0)) t ξ)
      rw [Ht ξ]
      exact bsub_refl _
    | .inr ⟨⟨b, q⟩, Hq⟩ =>
      obtain ⟨t, Ht⟩ := badd_big_r x (H b) q
      refine ⟨⟨b, t⟩, fun ξ => ?_⟩
      rw [Hq ξ]
      show bsub (badd x (bbigSz (H b) q ξ)) (bbigSz (badd x (H b)) t ξ)
      rw [Ht ξ]
      exact bsub_refl _

/-- Rocq: `BachmannNormal.bcanon_badd`. -/
theorem bcanon_badd (x y : BOrd.{u}) (Hx : BCanon x) : BCanon y → BCanon (badd x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3, Hy4, Hy5⟩ := hy
  rw [badd_eq x (bnode B g D h)]
  exact bcanon_blub _ _ Hx ⟨fun b => ihg b (Hy1 b), fun d ξ => ihh d ξ (Hy2 d ξ),
    fun d ξ ξ' H => bsub_badd_r _ _ _ (Hy3 d ξ ξ' H), fun d ξ ξ' hc H => bslt_badd_r _ _ _ (Hy4 d ξ ξ' hc H),
    fun d B' k b0 hdir hk => bsub_trans (bsub_badd_r _ _ _ (Hy5 d B' k b0 hdir hk)) (bsub_badd_bsup x _ b0)⟩

/-! ### Multiplication -/

/-- Rocq: `BachmannNormal.bmul_small_r`. -/
theorem bmul_small_r (x y : BOrd.{u}) (q : bsmall y) (s : bsmall (badd (bmul x (bsmallSz y q)) x)) :
    ∃ t, bsmallSz (bmul x y) t = bsmallSz (badd (bmul x (bsmallSz y q)) x) s := by
  cases y; exact ⟨.inl ⟨q, s⟩, rfl⟩

/-- Rocq: `BachmannNormal.bmul_big_r`. -/
theorem bmul_big_r (x y : BOrd.{u}) (q : bsmall y) (c : bbig (badd (bmul x (bsmallSz y q)) x)) :
    ∃ t, ∀ ξ, bbigSz (bmul x y) t ξ = bbigSz (badd (bmul x (bsmallSz y q)) x) c ξ := by
  cases y; exact ⟨.inl ⟨q, c⟩, fun _ => rfl⟩

/-- Rocq: `BachmannNormal.bmul_big_fam`. -/
theorem bmul_big_fam (x y : BOrd.{u}) (d : bbig y) : ∃ t, ∀ ξ, bbigSz (bmul x y) t ξ = bmul x (bbigSz y d ξ) := by
  cases y; exact ⟨.inr d, fun _ => rfl⟩

/-- Rocq: `BachmannNormal.bsub_bmul_bsup`. -/
theorem bsub_bmul_bsup (x : BOrd.{u}) {B : Type u} (H : B → BOrd.{u}) :
    bsub (bmul x (bsup H)) (bsup fun b => bmul x (H b)) := by
  refine bsub_intro _ _ (fun s => ?_) (fun c => ?_)
  · match s with
    | .inl ⟨⟨b, q⟩, s⟩ =>
      obtain ⟨t, Ht⟩ := bmul_small_r x (H b) q s
      refine ⟨⟨b, t⟩, ?_⟩
      show bsub (bsmallSz (badd (bmul x (bsmallSz (H b) q)) x) s) (bsmallSz (bmul x (H b)) t)
      rw [Ht]
      exact bsub_refl _
    | .inr e => exact nomatch e
  · match c with
    | .inl ⟨⟨b, q⟩, c⟩ =>
      obtain ⟨t, Ht⟩ := bmul_big_r x (H b) q c
      refine ⟨⟨b, t⟩, fun ξ => ?_⟩
      show bsub (bbigSz (badd (bmul x (bsmallSz (H b) q)) x) c ξ) (bbigSz (bmul x (H b)) t ξ)
      rw [Ht ξ]
      exact bsub_refl _
    | .inr ⟨b, d⟩ =>
      obtain ⟨t, Ht⟩ := bmul_big_fam x (H b) d
      refine ⟨⟨b, t⟩, fun ξ => ?_⟩
      show bsub (bmul x (bbigSz (H b) d ξ)) (bbigSz (bmul x (H b)) t ξ)
      rw [Ht ξ]
      exact bsub_refl _

/-- `x·b_j + x ⊑ x·b`, for any small child `b_j` of `b`. Rocq: `BachmannNormal.bsub_bmul_step`. -/
theorem bsub_bmul_step (x b : BOrd.{u}) (j : bsmall b) : bsub (badd (bmul x (bsmallSz b j)) x) (bmul x b) := by
  rw [bmul_eq x b]
  exact bsub_trans (bsub_bsup_le (fun j => badd (bmul x (bsmallSz b j)) x) j) (bsub_blub_l _ _)

/-- Rocq: `BachmannNormal.bslt_bmul_r`. -/
theorem bslt_bmul_r (x : BOrd.{u}) (Hx : bpos x) : ∀ a b : BOrd.{u}, bslt a b → bslt (bmul x a) (bmul x b) := by
  intro a b H
  induction H with
  | small b j hj =>
    exact bslt_bsub_l _ _ _ (bsub_bmul_r _ _ _ hj)
      (bslt_bsub_r _ _ _ (bslt_badd_pos _ bzero x Hx) (bsub_bmul_step x b j))
  | big b d n _ ih =>
    obtain ⟨t, Ht⟩ := bmul_big_fam x b d
    exact .big _ t n (by rw [Ht]; exact ih)
  | desc b j _ ih => exact bslt_bsub_r _ _ _ ih (bsub_trans (bsub_le_badd _ _) (bsub_bmul_step x b j))

/-- Rocq: `BachmannNormal.bcanon_bmul`. -/
theorem bcanon_bmul (x y : BOrd.{u}) (Hx : BCanon x) (Hpos : bpos x) : BCanon y → BCanon (bmul x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3, Hy4, Hy5⟩ := hy
  rw [bmul_eq x (bnode B g D h)]
  exact bcanon_blub _ _ (bcanon_bsup _ fun b => bcanon_badd _ _ (ihg b (Hy1 b)) Hx)
    ⟨fun e => (nomatch e), fun d ξ => ihh d ξ (Hy2 d ξ), fun d ξ ξ' H => bsub_bmul_r _ _ _ (Hy3 d ξ ξ' H),
      fun d ξ ξ' hc H => bslt_bmul_r _ Hpos _ _ (Hy4 d ξ ξ' hc H),
      fun d B' k b0 hdir hk => bsub_trans (bsub_bmul_r _ _ _ (Hy5 d B' k b0 hdir hk)) (bsub_bmul_bsup x _)⟩

/-- Rocq: `BachmannNormal.bpos_Ω`. -/
theorem bpos_Ω : bpos bOmega.{u} := .big bOmega ⟨⟩ 1 (.small (embed 1) ⟨⟩ (bsub_bzero_l _))

/-! ### Exponentiation -/

/-- Rocq: `BachmannNormal.bexpΩ_small_zero`. -/
theorem bexpΩ_small_zero (y : BOrd.{u}) : ∃ t, bsmallSz (bexpΩ y) t = bzero := by
  cases y; exact ⟨.inl ⟨⟩, rfl⟩

/-- Rocq: `BachmannNormal.bpos_bexpΩ`. -/
theorem bpos_bexpΩ (y : BOrd.{u}) : bpos (bexpΩ y) := by
  obtain ⟨t, ht⟩ := bexpΩ_small_zero y
  exact .small _ t (by rw [ht]; exact bsub_refl _)

/-- Rocq: `BachmannNormal.bexpΩ_big_s`. -/
theorem bexpΩ_big_s (y : BOrd.{u}) (q : bsmall y) (c : bbig (bmul (bexpΩ (bsmallSz y q)) bOmega)) :
    ∃ t, ∀ ξ, bbigSz (bexpΩ y) t ξ = bbigSz (bmul (bexpΩ (bsmallSz y q)) bOmega) c ξ := by
  cases y; exact ⟨.inr (.inl ⟨q, c⟩), fun _ => rfl⟩

/-- Rocq: `BachmannNormal.bexpΩ_big_b`. -/
theorem bexpΩ_big_b (y : BOrd.{u}) (d : bbig y) : ∃ t, ∀ ξ, bbigSz (bexpΩ y) t ξ = bexpΩ (bbigSz y d ξ) := by
  cases y; exact ⟨.inr (.inr d), fun _ => rfl⟩

/-- A positive `P` lies strictly below `P·2`. Rocq: `BachmannNormal.bslt_two`. -/
theorem bslt_two (P : BOrd.{u}) (HP : bpos P) : bslt P (bmul P (embed 2)) :=
  bslt_bsub_l _ _ _ (bsub_bmul_one P).2
    (bslt_bsub_r _ _ _ (bslt_badd_pos (bmul P (embed 1)) bzero P HP) (bsub_bmul_step P (embed 2) ⟨⟩))

/-- Rocq: `BachmannNormal.bsub_P_P2`. -/
theorem bsub_P_P2 (P : BOrd.{u}) : bsub P (bmul P (embed 2)) :=
  bsub_trans (bsub_bmul_one P).2 (bsub_trans (bsub_le_badd (bmul P (embed 1)) P) (bsub_bmul_step P (embed 2) ⟨⟩))

/-- Rocq: `BachmannNormal.bslt_bexpΩ`. -/
theorem bslt_bexpΩ : ∀ a b : BOrd.{u}, bslt a b → bslt (bexpΩ a) (bexpΩ b) := by
  intro a b H
  induction H with
  | small b j hj =>
    refine bslt_bsub_l _ _ _ (bsub_bexpΩ _ _ hj) ?_
    obtain ⟨t, ht⟩ := bexpΩ_big_s b j (.inr ⟨⟩)
    exact .big _ t 2 (by rw [ht]; exact bslt_two _ (bpos_bexpΩ _))
  | big b d n _ ih =>
    obtain ⟨t, ht⟩ := bexpΩ_big_b b d
    exact .big _ t n (by rw [ht]; exact ih)
  | desc b j _ ih =>
    obtain ⟨t, ht⟩ := bexpΩ_big_s b j (.inr ⟨⟩)
    exact .big _ t 2 (by rw [ht]; exact bslt_bsub_r _ _ _ ih (bsub_P_P2 _))

/-- Rocq: `BachmannNormal.bsub_bexpΩ_bsup`. -/
theorem bsub_bexpΩ_bsup {B : Type u} (H : B → BOrd.{u}) (b0 : B) : bsub (bexpΩ (bsup H)) (bsup fun b => bexpΩ (H b)) := by
  refine bsub_intro _ _ (fun s => ?_) (fun c => ?_)
  · match s with
    | .inl _ =>
      obtain ⟨t, ht⟩ := bexpΩ_small_zero (H b0)
      refine ⟨⟨b0, t⟩, ?_⟩
      show bsub bzero (bsmallSz (bexpΩ (H b0)) t)
      rw [ht]
      exact bsub_refl _
    | .inr (.inl ⟨_, .inl ⟨e, _⟩⟩) => exact nomatch e
    | .inr (.inl ⟨_, .inr e⟩) => exact nomatch e
    | .inr (.inr e) => exact nomatch e
  · match c with
    | .inl e => exact nomatch e
    | .inr (.inl ⟨⟨b, q⟩, c⟩) =>
      obtain ⟨t, ht⟩ := bexpΩ_big_s (H b) q c
      refine ⟨⟨b, t⟩, fun ξ => ?_⟩
      show bsub (bbigSz (bmul (bexpΩ (bsmallSz (H b) q)) bOmega) c ξ) (bbigSz (bexpΩ (H b)) t ξ)
      rw [ht ξ]
      exact bsub_refl _
    | .inr (.inr ⟨b, d⟩) =>
      obtain ⟨t, ht⟩ := bexpΩ_big_b (H b) d
      refine ⟨⟨b, t⟩, fun ξ => ?_⟩
      show bsub (bexpΩ (bbigSz (H b) d ξ)) (bbigSz (bexpΩ (H b)) t ξ)
      rw [ht ξ]
      exact bsub_refl _

/-- Rocq: `BachmannNormal.bcanon_bexpΩ`. -/
theorem bcanon_bexpΩ (y : BOrd.{u}) : BCanon y → BCanon (bexpΩ y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Hy1, Hy2, Hy3, Hy4, Hy5⟩ := hy
  rw [bexpΩ_eq (bnode B g D h)]
  exact bcanon_blub _ _ (bcanon_bsucc _ bcanon_bzero) (bcanon_blub _ _
    (bcanon_bsup _ fun b => bcanon_bmul _ _ (ihg b (Hy1 b)) (bpos_bexpΩ _) bcanon_Ω)
    ⟨fun e => (nomatch e), fun d ξ => ihh d ξ (Hy2 d ξ), fun d ξ ξ' H => bsub_bexpΩ _ _ (Hy3 d ξ ξ' H),
      fun d ξ ξ' hc H => bslt_bexpΩ _ _ (Hy4 d ξ ξ' hc H),
      fun d B' k b0 hdir hk => bsub_trans (bsub_bexpΩ _ _ (Hy5 d B' k b0 hdir hk)) (bsub_bexpΩ_bsup _ b0)⟩)

/-! ### The tower and `ε_{Ω+1}` -/

/-- Rocq: `BachmannNormal.bcanon_btower`. -/
theorem bcanon_btower : ∀ n : Nat, BCanon (btower.{u} n)
  | 0 => bcanon_bsucc _ bcanon_Ω
  | n + 1 => bcanon_bexpΩ _ (bcanon_btower n)

/-- Rocq: `BachmannNormal.bcanon_bεΩ1`. -/
theorem bcanon_bεΩ1 : BCanon bεΩ1.{u} :=
  ⟨fun n => bcanon_btower n.down, fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-! ## Deciding whether a node has components

Every node decides, as a proposition, whether it has any components;
Ω-family members are required to do so only at complete arguments. Ordinary
trees cannot decide this constructively, but every tree the arithmetic builds
from complete ordinals does. The structural layer carries the decision so that
it is available to the hierarchy `bphi`, which needs it for strictness. -/

/-- Rocq: `BachmannNormal.bdec`. -/
def BDec : BOrd.{u} → Prop
  | bnode A g C h => (Nonempty (A ⊕ C) ∨ ¬ Nonempty (A ⊕ C)) ∧ (∀ a, BDec (g a)) ∧ ∀ c ξ, Complete ξ → BDec (h c ξ)

/-- Rocq: `BachmannNormal.bdec_small`. -/
theorem bdec_small (x : BOrd.{u}) (a : bsmall x) (H : BDec x) : BDec (bsmallSz x a) := by
  cases x; exact H.2.1 a

/-- Rocq: `BachmannNormal.bdec_big`. -/
theorem bdec_big (x : BOrd.{u}) (c : bbig x) (ξ : Ordinal.{u}) (H : BDec x) (hξ : Complete ξ) : BDec (bbigSz x c ξ) := by
  cases x; exact H.2.2 c ξ hξ

/-- Rocq: `BachmannNormal.bdec_bzero`. -/
theorem bdec_bzero : BDec bzero.{u} :=
  ⟨.inr fun ⟨k⟩ => match k with
    | .inl e => nomatch e
    | .inr e => (nomatch e), fun e => (nomatch e), fun e => (nomatch e)⟩

/-- Rocq: `BachmannNormal.bdec_bsucc`. -/
theorem bdec_bsucc (x : BOrd.{u}) (H : BDec x) : BDec (bsucc x) := ⟨.inl ⟨.inl ⟨⟩⟩, fun _ => H, fun e => (nomatch e)⟩

/-- Rocq: `BachmannNormal.bdec_blub`. -/
theorem bdec_blub (x y : BOrd.{u}) (hx : BDec x) (hy : BDec y) : BDec (blub x y) := by
  cases x with
  | bnode A g C h =>
  cases y with
  | bnode B g' D h' =>
  obtain ⟨Dx, Hx1, Hx2⟩ := hx
  obtain ⟨Dy, Hy1, Hy2⟩ := hy
  refine ⟨?_, fun ab => ?_, fun cd ξ hξ => ?_⟩
  · match Dx with
    | .inl ⟨.inl a⟩ => exact .inl ⟨.inl (.inl a)⟩
    | .inl ⟨.inr c⟩ => exact .inl ⟨.inr (.inl c)⟩
    | .inr Nx =>
      match Dy with
      | .inl ⟨.inl b⟩ => exact .inl ⟨.inl (.inr b)⟩
      | .inl ⟨.inr d⟩ => exact .inl ⟨.inr (.inr d)⟩
      | .inr Ny =>
        exact .inr fun ⟨k⟩ => match k with
          | .inl (.inl a) => Nx ⟨.inl a⟩
          | .inl (.inr b) => Ny ⟨.inl b⟩
          | .inr (.inl c) => Nx ⟨.inr c⟩
          | .inr (.inr d) => Ny ⟨.inr d⟩
  · match ab with
    | .inl a => exact Hx1 a
    | .inr b => exact Hy1 b
  · match cd with
    | .inl c => exact Hx2 c ξ hξ
    | .inr d => exact Hy2 d ξ hξ

/-- Rocq: `BachmannNormal.bdec_blimΩ`. -/
theorem bdec_blimΩ (h : Ordinal.{u} → BOrd.{u}) (H : ∀ ξ, Complete ξ → BDec (h ξ)) : BDec (blimΩ h) :=
  ⟨.inl ⟨.inr ⟨⟩⟩, fun e => (nomatch e), fun _ ξ hξ => H ξ hξ⟩

/-- Rocq: `BachmannNormal.bdec_blimΩ_inv`. -/
theorem bdec_blimΩ_inv (h : Ordinal.{u} → BOrd.{u}) (H : BDec (blimΩ h)) : ∀ ξ, Complete ξ → BDec (h ξ) :=
  fun ξ hξ => H.2.2 ⟨⟩ ξ hξ

/-- Rocq: `BachmannNormal.bdec_badd`. -/
theorem bdec_badd (x y : BOrd.{u}) (Hx : BDec x) : BDec y → BDec (badd x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Dy, Hy1, Hy2⟩ := hy
  rw [badd_eq x (bnode B g D h)]
  exact bdec_blub _ _ Hx ⟨Dy, fun b => ihg b (Hy1 b), fun d ξ hξ => ihh d ξ (Hy2 d ξ hξ)⟩

/-- Rocq: `BachmannNormal.bslt_inh`. -/
theorem bslt_inh (x y : BOrd.{u}) (H : bslt x y) : Nonempty (bsmall y ⊕ bbig y) :=
  match H with
  | .small _ b _ => ⟨.inl b⟩
  | .big _ d _ _ => ⟨.inr d⟩
  | .desc _ b _ => ⟨.inl b⟩

/-- Rocq: `BachmannNormal.bdec_bmul`. -/
theorem bdec_bmul (x y : BOrd.{u}) (Hi : Nonempty (bsmall x ⊕ bbig x)) (Hx : BDec x) : BDec y → BDec (bmul x y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨Dy, Hy1, Hy2⟩ := hy
  refine ⟨?_, fun s => ?_, fun c ξ hξ => ?_⟩
  · match Dy with
    | .inl ⟨.inl b⟩ =>
      match Hi with
      | ⟨.inl s⟩ =>
        obtain ⟨t, _⟩ := badd_small_r (bmul x (g b)) x s
        exact .inl ⟨.inl (.inl ⟨b, t⟩)⟩
      | ⟨.inr c⟩ =>
        obtain ⟨t, _⟩ := badd_big_r (bmul x (g b)) x c
        exact .inl ⟨.inr (.inl ⟨b, t⟩)⟩
    | .inl ⟨.inr d⟩ => exact .inl ⟨.inr (.inr d)⟩
    | .inr N =>
      exact .inr fun ⟨k⟩ => match k with
        | .inl (.inl ⟨b, _⟩) => N ⟨.inl b⟩
        | .inl (.inr e) => nomatch e
        | .inr (.inl ⟨b, _⟩) => N ⟨.inl b⟩
        | .inr (.inr d) => N ⟨.inr d⟩
  · match s with
    | .inl ⟨b, s⟩ => exact bdec_small (badd (bmul x (g b)) x) s (bdec_badd _ _ (ihg b (Hy1 b)) Hx)
    | .inr e => exact nomatch e
  · match c with
    | .inl ⟨b, c⟩ => exact bdec_big (badd (bmul x (g b)) x) c ξ (bdec_badd _ _ (ihg b (Hy1 b)) Hx) hξ
    | .inr d => exact ihh d ξ (Hy2 d ξ hξ)

/-- Rocq: `BachmannNormal.bexpΩ_inh`. -/
theorem bexpΩ_inh (y : BOrd.{u}) : Nonempty (bsmall (bexpΩ y) ⊕ bbig (bexpΩ y)) := by
  cases y; exact ⟨.inl (.inl ⟨⟩)⟩

/-- Rocq: `BachmannNormal.bdec_embed`. -/
theorem bdec_embed : ∀ ξ : Ordinal.{u}, Complete ξ → BDec (embed ξ)
  | mk _ k, ⟨_, Hi, Hc⟩ =>
    ⟨match Hi with
      | .inl ⟨x⟩ => .inl ⟨.inl x⟩
      | .inr N => .inr fun ⟨kk⟩ => match kk with
        | .inl x => N ⟨x⟩
        | .inr e => (nomatch e),
     fun a => bdec_embed (k a) (Hc a), fun e => (nomatch e)⟩

/-- Rocq: `BachmannNormal.bdec_Ω`. -/
theorem bdec_Ω : BDec bOmega.{u} := bdec_blimΩ embed fun ξ hξ => bdec_embed ξ hξ

/-- Rocq: `BachmannNormal.bdec_bexpΩ`. -/
theorem bdec_bexpΩ (y : BOrd.{u}) : BDec y → BDec (bexpΩ y) := by
  induction y with
  | bnode B g D h ihg ihh =>
  intro hy
  obtain ⟨_, Hy1, Hy2⟩ := hy
  refine ⟨.inl ⟨.inl (.inl ⟨⟩)⟩, fun s => ?_, fun c ξ hξ => ?_⟩
  · match s with
    | .inl _ => exact bdec_bzero
    | .inr (.inl ⟨b, s⟩) =>
      exact bdec_small (bmul (bexpΩ (g b)) bOmega) s (bdec_bmul _ _ (bexpΩ_inh _) (ihg b (Hy1 b)) bdec_Ω)
    | .inr (.inr e) => exact nomatch e
  · match c with
    | .inl e => exact nomatch e
    | .inr (.inl ⟨b, c⟩) =>
      exact bdec_big (bmul (bexpΩ (g b)) bOmega) c ξ (bdec_bmul _ _ (bexpΩ_inh _) (ihg b (Hy1 b)) bdec_Ω) hξ
    | .inr (.inr d) => exact ihh d ξ (Hy2 d ξ hξ)

/-- Rocq: `BachmannNormal.bdec_btower`. -/
theorem bdec_btower : ∀ n : Nat, BDec (btower.{u} n)
  | 0 => bdec_bsucc _ bdec_Ω
  | n + 1 => bdec_bexpΩ _ (bdec_btower n)

/-- Rocq: `BachmannNormal.bdec_bεΩ1`. -/
theorem bdec_bεΩ1 : BDec bεΩ1.{u} := ⟨.inl ⟨.inl ⟨0⟩⟩, fun n => bdec_btower n.down, fun e => (nomatch e)⟩

/-- Canonical and decided. Rocq: `BachmannNormal.bcd`. -/
def BCd (T : BOrd.{u}) : Prop := BCanon T ∧ BDec T

/-- Rocq: `BachmannNormal.bcd_small`. -/
theorem bcd_small (x : BOrd.{u}) (a : bsmall x) (H : BCd x) : BCd (bsmallSz x a) :=
  ⟨bcanon_small x a H.1, bdec_small x a H.2⟩

/-- Rocq: `BachmannNormal.bcd_big`. -/
theorem bcd_big (x : BOrd.{u}) (c : bbig x) (ξ : Ordinal.{u}) (H : BCd x) (hξ : Complete ξ) : BCd (bbigSz x c ξ) :=
  ⟨bcanon_big x c ξ H.1, bdec_big x c ξ H.2 hξ⟩

/-- Rocq: `BachmannNormal.bcd_badd`. -/
theorem bcd_badd (x y : BOrd.{u}) (hx : BCd x) (hy : BCd y) : BCd (badd x y) :=
  ⟨bcanon_badd x y hx.1 hy.1, bdec_badd x y hx.2 hy.2⟩

/-- Rocq: `BachmannNormal.bcd_bmul`. -/
theorem bcd_bmul (x y : BOrd.{u}) (hx : BCd x) (hp : bpos x) (hy : BCd y) : BCd (bmul x y) :=
  ⟨bcanon_bmul x y hx.1 hp hy.1, bdec_bmul x y (bslt_inh _ _ hp) hx.2 hy.2⟩

/-- Rocq: `BachmannNormal.bcd_bexpΩ`. -/
theorem bcd_bexpΩ (y : BOrd.{u}) (H : BCd y) : BCd (bexpΩ y) := ⟨bcanon_bexpΩ y H.1, bdec_bexpΩ y H.2⟩

/-- Rocq: `BachmannNormal.bcd_embed`. -/
theorem bcd_embed (ξ : Ordinal.{u}) (H : Complete ξ) : BCd (embed ξ) := ⟨bcanon_embed ξ, bdec_embed ξ H⟩

/-- Rocq: `BachmannNormal.bcd_Ω`. -/
theorem bcd_Ω : BCd bOmega.{u} := ⟨bcanon_Ω, bdec_Ω⟩

/-- Rocq: `BachmannNormal.bcd_btower`. -/
theorem bcd_btower (n : Nat) : BCd (btower.{u} n) := ⟨bcanon_btower n, bdec_btower n⟩

/-- Rocq: `BachmannNormal.bcd_bεΩ1`. -/
theorem bcd_bεΩ1 : BCd bεΩ1.{u} := ⟨bcanon_bεΩ1, bdec_bεΩ1⟩

/-! ## Strict increase along a family -/

/-- Rocq: `BachmannNormal.bphi_child_lt`. -/
theorem bphi_child_lt (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (y : BOrd.{u}) (b : bsmall y)
    (hgood : BGood f y) : bphi f (bsmallSz y b) 0 < bphi f y 0 :=
  lt_of_lt_of_le ((bphi_normal hf _ (bgood_small f y b hgood)).increasing _ _ (bphi_complete hf y 0 hgood zero_complete)
      (bphi_nonzero hf y 0))
    (bphi_fix_small' hf y b 0 hgood zero_complete)

/-- Rocq: `BachmannNormal.bphi_strict`. -/
theorem bphi_strict (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ x y : BOrd.{u}, bslt x y → BGood f y → BFam y → bphi f x 0 < bphi f y 0 := by
  have hfm := hf.monotone
  intro x y H
  induction H with
  | small y b hb =>
    intro hgood hfam
    exact lt_of_le_of_lt ((bphi_mono_index f hfm _ (bfam_small _ hfam b)).2 _ hb 0) (bphi_child_lt f hf y b hgood)
  | big y d n _ ih =>
    intro hgood hfam
    refine lt_of_lt_of_le (ih (bgood_big f y d _ hgood (ofNat_complete n)) (bfam_big _ hfam d _)) ?_
    refine le_trans ((bphi_mono_index f hfm _ (bfam_big _ hfam d (bphi f y 0))).2 _ (bfam_fam _ hfam d _ _
      (fix_onePlus_finite f hf _ (bphi_complete hf y 0 hgood zero_complete)
        (bphi_fix_base' hf y 0 hgood ⟨.inr d⟩ zero_complete) n)) 0) ?_
    exact bphi_fix_big' hf y d 0 hgood zero_complete
  | desc y b _ ih =>
    intro hgood hfam
    exact lt_trans (ih (bgood_small f y b hgood) (bfam_small _ hfam b)) (bphi_child_lt f hf y b hgood)

/-! ## Continuity of the diagonal -/

/-- Rocq: `BachmannNormal.bsub_inh`. -/
theorem bsub_inh (x y : BOrd.{u}) (H : bsub x y) (Hi : Nonempty (bsmall x ⊕ bbig x)) : Nonempty (bsmall y ⊕ bbig y) :=
  match Hi with
  | ⟨.inl a⟩ => let ⟨b, _⟩ := bsub_small _ _ H a; ⟨.inl b⟩
  | ⟨.inr c⟩ => let ⟨d, _⟩ := bsub_big _ _ H c; ⟨.inr d⟩

/-- Rocq: `BachmannNormal.bphi_diag_cont`. -/
theorem bphi_diag_cont (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (h : Ordinal.{u} → BOrd.{u})
    (Hgood : ∀ ξ, Complete ξ → BGood f (h ξ)) (Hfam : ∀ ξ, BFam (h ξ))
    (Hmono : ∀ ξ ξ', ξ ≤ ξ' → bsub (h ξ) (h ξ'))
    (Hcont : ∀ (A : Type u) (g : A → Ordinal.{u}) (_ : A), Directed A g → (∀ a, Complete (g a)) →
      bsub (h (sup g)) (bsup fun a => h (g a))) :
    ScottContinuous fun ξ => bphi f (h ξ) 0 := by
  intro A g a0 hdir hc
  have hfm := hf.monotone
  have Hg : ∀ a, BGood f (h (g a)) := fun a => Hgood _ (hc a)
  have Hzc : ∀ a, Complete (bphi f (h (g a)) 0) := fun a => bphi_complete hf _ 0 (Hg a) zero_complete
  have Hzmono : ∀ a b, g a ≤ g b → bphi f (h (g a)) 0 ≤ bphi f (h (g b)) 0 := fun a b hab =>
    (bphi_mono_index f hfm _ (Hfam _)).2 _ (Hmono _ _ hab) 0
  have Hzdir : Directed A fun a => bphi f (h (g a)) 0 := fun a1 a2 =>
    let ⟨a', h1, h2⟩ := hdir a1 a2
    ⟨a', Hzmono _ _ h1, Hzmono _ _ h2⟩
  -- if some member has a component, the supremum is a fixpoint of f
  have Hfz : ∀ a, Nonempty (bsmall (h (g a)) ⊕ bbig (h (g a))) →
      f (sup fun a => bphi f (h (g a)) 0) ≤ sup fun a => bphi f (h (g a)) 0 := fun a ha =>
    le_trans (hf.continuous A _ a0 Hzdir Hzc) (sup_least fun b =>
      let ⟨b', hab', hbb'⟩ := hdir a b
      le_trans (hfm _ _ (Hzmono b b' hbb'))
        (le_trans (bphi_fix_base' hf _ 0 (Hg b') (bsub_inh _ _ (Hmono _ _ hab') ha) zero_complete)
          (sup_le (fun a => bphi f (h (g a)) 0) b')))
  refine le_trans ((bphi_mono_index f hfm _ (bfam_bsup _ fun a => Hfam (g a))).2 _ (Hcont A g a0 hdir hc) 0) ?_
  have HFam : ∀ k, NormalFunction (bphi_fam f (fun p : Σ a, bsmall (h (g a)) => bsmallSz (h (g p.1)) p.2)
      (fun p : Σ a, bbig (h (g a)) => bbigSz (h (g p.1)) p.2) k) := fun k =>
    match k with
    | .inl ⟨a, s⟩ => bphi_normal hf _ (bgood_small f _ s (Hg a))
    | .inr ⟨a, c⟩ => bgood_diag f _ c (Hg a)
  refine cfe_least f hf _ _ HFam _ _ (le_trans (bphi_ge_f f (h (g a0)) 0) (sup_le (fun a => bphi f (h (g a)) 0) a0))
    (limit_least fun e => (nomatch e)) fun k => ?_
  match k with
  | .inl ⟨a, s⟩ =>
    have HG := bphi_normal hf _ (bgood_small f _ s (Hg a))
    refine ⟨le_trans (HG.continuous A _ a0 Hzdir Hzc) (sup_least fun b => ?_), Hfz a ⟨.inl s⟩⟩
    obtain ⟨b', hab', hbb'⟩ := hdir a b
    obtain ⟨s', hs'⟩ := bsub_small _ _ (Hmono _ _ hab') s
    exact le_trans (HG.monotone _ _ (Hzmono b b' hbb'))
      (le_trans ((bphi_mono_index f hfm _ (bfam_small _ (Hfam _) s')).2 _ hs' _)
        (le_trans (bphi_fix_small' hf (h (g b')) s' 0 (Hg b') zero_complete) (sup_le (fun a => bphi f (h (g a)) 0) b')))
  | .inr ⟨a, c⟩ =>
    have HD := bgood_diag f _ c (Hg a)
    refine ⟨le_trans (HD.continuous A _ a0 Hzdir Hzc) (sup_least fun b => ?_), Hfz a ⟨.inr c⟩⟩
    obtain ⟨b', hab', hbb'⟩ := hdir a b
    obtain ⟨c', hc'⟩ := bsub_big _ _ (Hmono _ _ hab') c
    exact le_trans (HD.monotone _ _ (Hzmono b b' hbb'))
      (le_trans ((bphi_mono_index f hfm _ (bfam_big _ (Hfam _) c' _)).2 _ (hc' _) 0)
        (le_trans (bphi_fix_big' hf (h (g b')) c' 0 (Hg b') zero_complete) (sup_le (fun a => bphi f (h (g a)) 0) b')))

/-! ## Canonical, decided trees are good -/

private theorem bcanon_good_aux (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) :
    ∀ T : BOrd.{u}, BCanon T → BDec T → BGood f T
  | bnode _ g _ h, HT, ⟨D1, D2, D3⟩ => by
    have hfm := hf.monotone
    obtain ⟨H1, H2, H3, H4, H5⟩ := HT
    have HF : ∀ c ξ, BFam (h c ξ) := fun c ξ => bcanon_bfam _ (H2 c ξ)
    have HG : ∀ c ξ, Complete ξ → BGood f (h c ξ) := fun c ξ hξ => bcanon_good_aux f hf _ (H2 c ξ) (D3 c ξ hξ)
    refine ⟨fun a => bcanon_good_aux f hf _ (H1 a) (D2 a), HG, fun c => ⟨?_, ?_, ?_, ?_, ?_⟩,
      fun c ξ hξ hpos => bslt_inh (h c 0) _ (H4 c 0 ξ hξ hpos), D1⟩
    · exact fun x y hxy => (bphi_mono_index f hfm (h c y) (HF c y)).2 _ (H3 c x y hxy) 0
    · exact fun x y hy hxy => bphi_strict f hf _ _ (H4 c x y hy hxy) (HG c y hy) (HF c y)
    · exact bphi_diag_cont f hf (h c) (fun ξ hξ => HG c ξ hξ) (HF c) (H3 c) (fun B k b0 hdir hk => H5 c B k b0 hdir hk)
    · exact fun x hx => bphi_complete hf _ 0 (HG c x hx) zero_complete
    · exact fun _ => bphi_nonzero hf _ 0

/-- Rocq: `BachmannNormal.bcanon_good`. -/
theorem bcanon_good (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (T : BOrd.{u}) (HT : BCanon T)
    (HD : BDec T) : BFam T ∧ BGood f T :=
  ⟨bcanon_bfam T HT, bcanon_good_aux f hf T HT HD⟩

/-! ## Normality of the canonical hierarchy -/

/-- Rocq: `BachmannNormal.bcanon_normal`. -/
theorem bcanon_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (T : BOrd.{u}) (H : BCd T) :
    NormalFunction (bphi f T) :=
  bphi_normal hf T (bcanon_good f hf T H.1 H.2).2

/-- Rocq: `BachmannNormal.bphi_Ω_normal`. -/
theorem bphi_Ω_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : NormalFunction (bphi f bOmega) :=
  bcanon_normal f hf _ bcd_Ω

/-- `φ_{ε_{Ω+1}}` is a normal function. Rocq: `BachmannNormal.bphi_εΩ1_normal`. -/
theorem bphi_εΩ1_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) : NormalFunction (bphi f bεΩ1) :=
  bcanon_normal f hf _ bcd_bεΩ1

/-- The Bachmann–Howard ordinal, defined via the provably normal hierarchy
`bphi`. Rocq: `BachmannNormal.BachmannHoward`. -/
def BachmannHoward : Ordinal.{u} := bphi powOmega bεΩ1 0

/-- Rocq: `BachmannNormal.BachmannHoward_complete`. -/
theorem BachmannHoward_complete : Complete BachmannHoward.{u} :=
  (bphi_εΩ1_normal _ powOmega_normal).complete 0 zero_complete

/-- Every canonical tree `Ω^ζ·ξ`, and `Ω^Ω`, gives a normal function.
Rocq: `BachmannNormal.bphi_canonical_normal`. -/
theorem bphi_canonical_normal (f : Ordinal.{u} → Ordinal.{u}) (hf : NormalFunction f) (ξ ζ : Ordinal.{u})
    (hξ : Complete ξ) (hζ : Complete ζ) :
    NormalFunction (bphi f (bmul (bexpΩ (embed ζ)) (embed ξ))) ∧ NormalFunction (bphi f (bexpΩ bOmega)) :=
  ⟨bcanon_normal f hf _ (bcd_bmul _ _ (bcd_bexpΩ _ (bcd_embed ζ hζ)) (bpos_bexpΩ _) (bcd_embed ξ hξ)),
    bcanon_normal f hf _ (bcd_bexpΩ _ bcd_Ω)⟩

end Bachmann

end ConstructiveOrdinals
