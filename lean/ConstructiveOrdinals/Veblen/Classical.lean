import ConstructiveOrdinals.Veblen.Defs
import ConstructiveOrdinals.Classical
import ConstructiveOrdinals.Enumerate

/-!
# The Veblen hierarchy, classically

Port of `Ordinal/VeblenClassical.v`. This is a standalone alternative to
`Veblen/Constructive.lean`; nothing else imports it.

Here normal functions are strictly increasing and strongly continuous, with no
completeness side conditions. In place of completeness, the Veblen results
assume two principles that hold classically:

* every ordinal is either `≤ 0` or `> 0` (`hzd`);
* every ordinal is directed (`hd`).

Rocq states these as section hypotheses, so each lemma takes exactly those of
them that its proof uses, as reported by Rocq's `Check`. The final results
about `Γ` and `Ξ` take `ExcludedMiddle`, from which both principles follow.

Everything lives in the namespace `Ordinal.VeblenClassical`, because the
names coincide with those of `Veblen/Constructive.lean`.
-/

namespace ConstructiveOrdinals

universe u

namespace Ordinal

namespace VeblenClassical

/-- Normal functions, classically: monotone, strictly increasing, strongly
continuous and nonzero. Rocq: `VeblenClassical.normal_function`. -/
structure NormalFunction (f : Ordinal.{u} → Ordinal.{u}) : Prop where
  /-- Rocq: `normal_monotone`. -/
  monotone : ∀ x y, x ≤ y → f x ≤ f y
  /-- Rocq: `normal_increasing`. -/
  increasing : ∀ x y, x < y → f x < f y
  /-- Rocq: `normal_continuous`. -/
  continuous : StronglyContinuous f
  /-- Rocq: `normal_nonzero`. -/
  nonzero : ∀ x, 0 < f x

/-- Rocq: `VeblenClassical.critical_ordinal`. -/
def CriticalOrdinal (f : Ordinal.{u} → Ordinal.{u}) (β x : Ordinal.{u}) : Prop :=
  ∀ α, α < β → x ≈ veblen f α x

/-- Rocq: `VeblenClassical.strongly_critical_ordinal`. -/
def StronglyCriticalOrdinal (f : Ordinal.{u} → Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  0 < β ∧ CriticalOrdinal f β β

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- Rocq: `VeblenClassical.normal_inflationary`. -/
theorem normal_inflationary (hf : NormalFunction f) (x : Ordinal.{u}) : x ≤ f x :=
  increasing_inflationary hf.increasing x

private theorem f_le_veblen (β y : Ordinal.{u}) : f y ≤ veblen f β y := by
  rw [veblen_unroll]; exact lub_le1 _ _

/-- Rocq: `VeblenClassical.veblen_nonzero`. -/
theorem veblen_nonzero (hf : NormalFunction f) (β y : Ordinal.{u}) : 0 < veblen f β y :=
  lt_of_lt_of_le (hf.nonzero y) (f_le_veblen β y)

/-- Rocq: `VeblenClassical.veblen_inflationary`. -/
theorem veblen_inflationary (hf : NormalFunction f) (β x : Ordinal.{u}) : x ≤ veblen f β x :=
  le_trans (normal_inflationary hf x) (f_le_veblen β x)

private theorem f_le_fixOrd (hf : NormalFunction f) (β γ y : Ordinal.{u}) :
    f y ≤ fixOrd (veblen f γ) (lim fun z : y => veblen f β (y z)) :=
  le_trans (hf.monotone _ _ (le_intro fun z =>
      lt_intro (show (lim fun z : y => veblen f β (y z)).Carrier from z)
        (veblen_inflationary hf β (y z))))
    (le_trans (f_le_veblen γ _) (sup_le (fun n : ULift.{u} Nat =>
      iterF (veblen f γ) (lim fun z : y => veblen f β (y z)) n.down) ⟨1⟩))

/-- Rocq: `VeblenClassical.veblen_unroll_nonzero`. -/
theorem veblen_unroll_nonzero (hf : NormalFunction f) (β y : Ordinal.{u}) (h₀ : 0 < β) :
    veblen f β y ≈ sup fun α : β => fixOrd (veblen f (β α)) (lim fun x : y => veblen f β (y x)) := by
  obtain ⟨b, _⟩ := lt_elim h₀
  rw [veblen_unroll]
  exact equiv_intro (lub_least (le_trans (f_le_fixOrd hf β (β b) y)
      (sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun x : y => veblen f β (y x))) b))
      (le_refl _))
    (lub_le2 _ _)

/-- Rocq: `VeblenClassical.veblen_increasing0`. -/
theorem veblen_increasing0 (hf : NormalFunction f) (x y : Ordinal.{u}) (h : x < y) :
    veblen f 0 x < veblen f 0 y := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (hf.increasing x y h) (f_le_veblen 0 y))
  rw [veblen_unroll]
  exact lub_least (le_refl _) (sup_least fun a => PEmpty.elim a)

/-- Rocq: `VeblenClassical.veblen_increasing_nonzero`. -/
theorem veblen_increasing_nonzero (hf : NormalFunction f) (β : Ordinal.{u}) (h₀ : 0 < β)
    (x y : Ordinal.{u}) (h : x < y) : veblen f β x < veblen f β y := by
  obtain ⟨b, _⟩ := lt_elim h₀
  obtain ⟨q, hq⟩ := lt_elim h
  refine lt_of_le_of_lt (veblen_monotone hf.monotone β _ _ hq) ?_
  rw [veblen_unroll f β y]
  refine lt_of_lt_of_le (limit_lt (fun z : y => veblen f β (y z)) q)
    (le_trans (fixOrd_above (veblen f (β b)) _) (le_trans ?_ (lub_le2 _ _)))
  exact sup_le (fun i : β => fixOrd (veblen f (β i)) (lim fun z : y => veblen f β (y z))) b

/-- Rocq: `VeblenClassical.veblen_increasing`. -/
theorem veblen_increasing (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (β x y : Ordinal.{u}) (h : x < y) : veblen f β x < veblen f β y :=
  match hzd β with
  | .inl hβ₀ =>
    lt_of_le_of_lt (veblen_monotone_first hf.monotone 0 β x hβ₀)
      (lt_of_lt_of_le (veblen_increasing0 hf x y h)
        (veblen_monotone_first hf.monotone β 0 y (zero_least β)))
  | .inr h₀ => veblen_increasing_nonzero hf β h₀ x y h

/-- Rocq: `VeblenClassical.veblen_lt_lemma`. -/
theorem veblen_lt_lemma (hf : NormalFunction f) (β : Ordinal.{u}) (h₀ : 0 < β) (x q : Ordinal.{u})
    (h : q < veblen f β x) :
    ∃ a, a < β ∧ q < fixOrd (veblen f a) (lim fun i : x => veblen f β (x i)) :=
  let ⟨b, hb⟩ := sup_lt (lt_of_lt_of_le h (veblen_unroll_nonzero hf β x h₀).le)
  ⟨β b, index_lt β b, hb⟩

/-- Rocq: `VeblenClassical.veblen_fixpoints_aux`. -/
theorem veblen_fixpoints_aux (hf : NormalFunction f) (_hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u})
    (hcont : ∀ y, y < β → StronglyContinuous (veblen f y)) (α : Ordinal.{u}) :
    ∀ x, α < β → veblen f α (veblen f β x) ≤ veblen f β x := by
  induction α using ltRec with
  | ind α ihα =>
    intro x hαβ
    have h₀ : 0 < β := lt_of_le_of_lt (zero_least α) hαβ
    have hV := veblen_unroll_nonzero hf β x h₀
    have hpre : ∀ b : β.Carrier, veblen f (β b) (fixOrd (veblen f (β b))
        (lim fun i : x => veblen f β (x i))) ≤ fixOrd (veblen f (β b)) (lim fun i : x => veblen f β (x i)) :=
      fun b => fixOrd_prefixpoint (hcont (β b) (index_lt β b)) _
    rw [veblen_unroll f α]
    refine lub_least ?_ (sup_least fun y => ?_)
    · obtain ⟨b₀, _⟩ := lt_elim h₀
      exact le_trans (hf.monotone _ _ hV.le) (le_trans (hf.continuous β.Carrier _ b₀)
        (le_trans (sup_monotone fun b => le_trans (f_le_veblen (β b) _) (hpre b)) hV.ge))
    · refine fixOrd_least (veblen_monotone hf.monotone (α y)) _ _ (le_intro fun z => ?_)
        (ihα (α y) (index_lt α y) x (lt_trans (index_lt α y) hαβ))
      obtain ⟨a', ha', hq⟩ := veblen_lt_lemma hf β h₀ x _ (index_lt (veblen f β x) z)
      obtain ⟨b₁, hb₁⟩ := lt_elim hαβ
      obtain ⟨b₂, hb₂⟩ := lt_elim ha'
      obtain ⟨w, hw₁, hw₂⟩ := hd β b₁ b₂
      have hF : veblen f β x z < fixOrd (veblen f (β w)) (lim fun i : x => veblen f β (x i)) :=
        lt_of_lt_of_le hq (fixOrd_monotone_func
          (fun q => veblen_monotone_first hf.monotone _ _ q (le_trans hb₂ hw₂))
          (veblen_monotone hf.monotone _) _)
      calc veblen f α (veblen f β x z)
          < veblen f α (fixOrd (veblen f (β w)) (lim fun i : x => veblen f β (x i))) :=
            veblen_increasing_nonzero hf α (lt_intro y (zero_least _)) _ _ hF
        _ ≤ veblen f (β w) (fixOrd (veblen f (β w)) (lim fun i : x => veblen f β (x i))) :=
            veblen_monotone_first hf.monotone _ _ _ (le_trans hb₁ hw₁)
        _ ≤ fixOrd (veblen f (β w)) (lim fun i : x => veblen f β (x i)) := hpre w
        _ ≤ veblen f β x := le_trans (sup_le (fun b : β =>
              fixOrd (veblen f (β b)) (lim fun i : x => veblen f β (x i))) w) hV.ge

/-- Rocq: `VeblenClassical.veblen_continuous`. -/
theorem veblen_continuous (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u}) :
    StronglyContinuous (veblen f β) := by
  induction β using ltRec with
  | ind β ih =>
    intro X h x₀
    rw [veblen_unroll f β (sup h)]
    refine lub_least (le_trans (hf.continuous X h x₀)
      (sup_monotone fun i => f_le_veblen β (h i))) (sup_least fun a => ?_)
    refine fixOrd_least (veblen_monotone hf.monotone _) _ _ (le_intro fun p => ?_) ?_
    · exact lt_of_lt_of_le (veblen_increasing_nonzero hf β (lt_intro a (zero_least _)) _ _
        (index_lt (h p.1) p.2)) (sup_le (fun i => veblen f β (h i)) p.1)
    · exact le_trans (ih (β a) (index_lt β a) X _ x₀)
        (sup_monotone fun i => veblen_fixpoints_aux hf hzd hd β (fun y hy => ih y hy) (β a)
          (h i) (index_lt β a))

/-- Rocq: `VeblenClassical.veblen_fixpoints`. -/
theorem veblen_fixpoints (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (α β x : Ordinal.{u}) (h : α < β) :
    veblen f α (veblen f β x) ≈ veblen f β x :=
  equiv_intro (veblen_fixpoints_aux hf hzd hd β (fun y _ => veblen_continuous hf hzd hd y) α x h)
    (veblen_inflationary hf α _)

/-- Rocq: `VeblenClassical.veblen_continuous_first`. -/
theorem veblen_continuous_first (hf : NormalFunction f) :
    StronglyContinuous fun β => veblen f β 0 := fun A g a => by
  show veblen f (sup g) 0 ≤ sup fun i => veblen f (g i) 0
  rw [veblen_unroll]
  refine lub_least (le_trans (f_le_veblen (g a) 0) (sup_le (fun i => veblen f (g i) 0) a))
    (sup_least fun p => ?_)
  refine le_trans ?_ (sup_le (fun i => veblen f (g i) 0) p.1)
  rw [veblen_unroll f (g p.1)]
  refine le_trans ?_ (le_trans (sup_le (fun α : g p.1 => fixOrd (veblen f (g p.1 α))
    (lim fun x : (0 : Ordinal.{u}).Carrier => veblen f (g p.1) ((0 : Ordinal.{u}) x))) p.2) (lub_le2 _ _))
  exact fixOrd_monotone (veblen_monotone hf.monotone _) (le_intro fun a => PEmpty.elim a)

/-- Rocq: `VeblenClassical.veblen_normal`. -/
theorem veblen_normal (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u}) :
    NormalFunction (veblen f β) where
  monotone := veblen_monotone hf.monotone β
  increasing := veblen_increasing hf hzd β
  continuous := veblen_continuous hf hzd hd β
  nonzero := veblen_nonzero hf β

/-- Rocq: `VeblenClassical.veblen_increasing_first`. -/
theorem veblen_increasing_first (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (a β : Ordinal.{u}) (h : a < β) :
    veblen f a 0 < veblen f β 0 := by
  obtain ⟨b, hb⟩ := lt_elim h
  have hfix := fixOrd_fixpoint (veblen_continuous hf hzd hd (β b)) (veblen_inflationary hf (β b))
    (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z))
  refine lt_of_le_of_lt (veblen_monotone_first hf.monotone _ _ 0 hb) ?_
  refine lt_of_lt_of_le (veblen_increasing hf hzd _ _ _
    (lt_of_lt_of_le (veblen_nonzero hf _ _) hfix.ge)) (le_trans hfix.ge ?_)
  rw [veblen_unroll f β]
  exact le_trans (sup_le (fun i : β => fixOrd (veblen f (β i))
    (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z))) b) (lub_le2 _ _)

private theorem fixOrd_lim0 (hf : NormalFunction f) (β γ : Ordinal.{u}) :
    fixOrd (veblen f γ) (lim fun z : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) z)) ≈
      fixOrd (veblen f γ) 0 :=
  equiv_intro (fixOrd_monotone (veblen_monotone hf.monotone γ) (le_intro fun a => PEmpty.elim a))
    (fixOrd_monotone (veblen_monotone hf.monotone γ) (zero_least _))

/-- Rocq: `VeblenClassical.veblen_first_unroll`. -/
theorem veblen_first_unroll (hf : NormalFunction f) (β : Ordinal.{u}) :
    veblen f β 0 ≈ f 0 ⊔ boundedSup β fun α => fixOrd (veblen f α) 0 := by
  rw [veblen_unroll]
  exact lub_congr (equiv_refl _) (sup_congr fun a => fixOrd_lim0 hf β (β a))

/-- Rocq: `VeblenClassical.veblen_first_unroll_nonzero`. -/
theorem veblen_first_unroll_nonzero (hf : NormalFunction f) (β : Ordinal.{u}) (h₀ : 0 < β) :
    veblen f β 0 ≈ boundedSup β fun α => fixOrd (veblen f α) 0 :=
  equiv_trans (veblen_unroll_nonzero hf β 0 h₀) (sup_congr fun a => fixOrd_lim0 hf β (β a))

/-- Rocq: `VeblenClassical.veblen_first_normal`. -/
theorem veblen_first_normal (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) : NormalFunction fun β => veblen f β 0 where
  monotone x y h := veblen_monotone_first hf.monotone y x 0 h
  increasing x y h := veblen_increasing_first hf hzd hd x y h
  continuous := veblen_continuous_first hf
  nonzero x := veblen_nonzero hf x 0

/-- Rocq: `VeblenClassical.veblen_zero`. -/
theorem veblen_zero (f : Ordinal.{u} → Ordinal.{u}) (x : Ordinal.{u}) : veblen f 0 x ≈ f x := by
  rw [veblen_unroll]
  exact equiv_intro (lub_least (le_refl _) (sup_least fun a => PEmpty.elim a)) (lub_le1 _ _)

/-- Rocq: `VeblenClassical.veblen_succ`. -/
theorem veblen_succ (hf : NormalFunction f) (_hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (_hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (a : Ordinal.{u}) :
    ∀ x : Ordinal.{u}, Complete a → veblen f (succ a) x ≈ enumFixpoints (veblen f a) x
  | mk X g, ha => by
    have hm := veblen_monotone hf.monotone a
    rw [veblen_unroll, enumFixpoints_unfold]
    refine equiv_intro (lub_least ?_ (sup_least fun _ => fixOrd_monotone hm (le_intro fun z =>
        lt_intro (show (mk X fun z => enumFixpoints (veblen f a) (g z)).Carrier from z)
          (veblen_succ hf _hzd _hd a (g z) ha).le))) ?_
    · refine le_trans (le_trans (hf.monotone _ _ (le_intro fun z =>
          lt_intro (show (mk X fun z => enumFixpoints (veblen f a) (g z)).Carrier from z)
            (increasing_inflationary (fun _ _ h => enumFixpoints_increasing hm h) (g z))))
        (f_le_veblen a _)) ?_
      exact sup_le (fun n : ULift.{u} Nat =>
        iterF (veblen f a) (mk X fun z => enumFixpoints (veblen f a) (g z)) n.down) ⟨1⟩
    · refine le_trans (fixOrd_monotone hm (le_intro fun z =>
        lt_intro (show (lim fun z : (mk X g).Carrier => veblen f (succ a) (mk X g z)).Carrier from z)
          (veblen_succ hf _hzd _hd a (g z) ha).ge)) (le_trans ?_ (lub_le2 _ _))
      exact sup_le (fun i : (succ a).Carrier => fixOrd (veblen f (succ a i))
        (lim fun z : (mk X g).Carrier => veblen f (succ a) (mk X g z))) PUnit.unit

/-- `veblen f β y` is below the fixpoint `fixOrd (veblen f (β b)) base`
whenever `y` is below its base. -/
private theorem fixOrd_le_veblen_of_lt (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) {α α' y base : Ordinal.{u}}
    (hlt : α < α') (hbase : base ≤ veblen f α' y) : fixOrd (veblen f α) base ≤ veblen f α' y :=
  fixOrd_least (veblen_monotone hf.monotone α) _ _ hbase
    (veblen_fixpoints hf hzd hd α α' y hlt).le

private theorem le_fixOrd_iter1 (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (γ base : Ordinal.{u}) :
    veblen f γ base ≤ fixOrd (veblen f γ) base :=
  le_trans (veblen_monotone hf.monotone γ _ _ (fixOrd_above _ base))
    (fixOrd_fixpoint (veblen_continuous hf hzd hd γ) (veblen_inflationary hf γ) base).ge

/-- Rocq: `VeblenClassical.veblen_limit_zero`. -/
theorem veblen_limit_zero (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u}) (hl : IsLimit β) :
    veblen f β 0 ≈ boundedSup β fun a => veblen f a 0 := by
  obtain ⟨⟨b₀⟩, hasc⟩ := hl
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · exact le_trans (le_trans (veblen_zero f 0).ge (veblen_monotone_first hf.monotone _ 0 0
      (zero_least _))) (sup_le (fun i : β => veblen f (β i) 0) b₀)
  · obtain ⟨b', hb'⟩ := hasc b
    exact le_trans (fixOrd_le_veblen_of_lt hf hzd hd hb' (le_intro fun a => PEmpty.elim a))
      (sup_le (fun i : β => veblen f (β i) 0) b')
  · refine le_trans ?_ (le_trans (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun x : (0 : Ordinal.{u}).Carrier => veblen f β ((0 : Ordinal.{u}) x))) b) (lub_le2 _ _))
    exact le_trans (veblen_monotone hf.monotone _ _ _ (zero_least _)) (le_fixOrd_iter1 hf hzd hd _ _)

/-- Rocq: `VeblenClassical.veblen_limit_succ`. -/
theorem veblen_limit_succ (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β x : Ordinal.{u}) (hl : IsLimit β) :
    veblen f β (succ x) ≈ boundedSup β fun a => veblen f a (succ (veblen f β x)) := by
  obtain ⟨⟨b₀⟩, hasc⟩ := hl
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · exact le_trans (le_trans (hf.monotone _ _ (succ_monotone (veblen_inflationary hf β x)))
      (f_le_veblen (β b₀) _)) (sup_le (fun i : β => veblen f (β i) (succ (veblen f β x))) b₀)
  · obtain ⟨b', hb'⟩ := hasc b
    exact le_trans (fixOrd_le_veblen_of_lt hf hzd hd hb' (veblen_inflationary hf _ _))
      (sup_le (fun i : β => veblen f (β i) (succ (veblen f β x))) b')
  · exact le_trans (le_fixOrd_iter1 hf hzd hd _ _) (le_trans (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun z : (succ x).Carrier => veblen f β (succ x z))) b) (lub_le2 _ _))

/-- Rocq: `VeblenClassical.veblen_limit_limit`. -/
theorem veblen_limit_limit (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β x : Ordinal.{u}) (hlβ : IsLimit β)
    (hlx : IsLimit x) :
    veblen f β x ≈ boundedSup β fun a => veblen f a (boundedSup x fun y => veblen f β y) := by
  obtain ⟨⟨b₀⟩, hascβ⟩ := hlβ
  obtain ⟨_, hascx⟩ := hlx
  have hβ₀ : 0 < β := lt_intro b₀ (zero_least _)
  have hLS : (lim fun z : x => veblen f β (x z)) ≤ boundedSup x fun y => veblen f β y :=
    le_intro fun z =>
      let ⟨z', hz'⟩ := hascx z
      lt_of_lt_of_le (veblen_increasing_nonzero hf β hβ₀ _ _ hz')
        (sup_le (fun i : x => veblen f β (x i)) z')
  have hSL : (boundedSup x fun y => veblen f β y) ≤ lim fun z : x => veblen f β (x z) :=
    sup_least fun z => le_of_lt (limit_lt (fun z : x => veblen f β (x z)) z)
  rw [veblen_unroll]
  refine equiv_intro (lub_least ?_ (sup_least fun b => ?_)) (sup_least fun b => ?_)
  · refine le_trans (le_trans (hf.monotone _ _ (le_intro fun z => ?_)) (f_le_veblen (β b₀) _))
      (sup_le (fun i : β => veblen f (β i) (boundedSup x fun y => veblen f β y)) b₀)
    obtain ⟨z', hz'⟩ := hascx z
    exact lt_of_lt_of_le hz' (le_trans (veblen_inflationary hf β _)
      (sup_le (fun i : x => veblen f β (x i)) z'))
  · obtain ⟨b', hb'⟩ := hascβ b
    exact le_trans (fixOrd_le_veblen_of_lt hf hzd hd hb' (le_trans hLS (veblen_inflationary hf _ _)))
      (sup_le (fun i : β => veblen f (β i) (boundedSup x fun y => veblen f β y)) b')
  · refine le_trans ?_ (le_trans (sup_le (fun i : β => fixOrd (veblen f (β i))
      (lim fun z : x => veblen f β (x z))) b) (lub_le2 _ _))
    exact le_trans (veblen_monotone hf.monotone _ _ _ hSL) (le_fixOrd_iter1 hf hzd hd _ _)

/-- For `β > 0`, `veblen f β` enumerates the `β`-critical ordinals.
Rocq: `VeblenClassical.veblen_enumerates_critical`. -/
theorem veblen_enumerates_critical (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u}) (h₀ : 0 < β) :
    Enumerates (veblen f β) (CriticalOrdinal f β) where
  included x α hαβ := equiv_symm (veblen_fixpoints hf hzd hd α β x hαβ)
  monotone := veblen_monotone hf.monotone β
  increasing := veblen_increasing hf hzd β
  least x z hz₁ hz₂ := by
    rw [veblen_unroll]
    refine lub_least ?_ (sup_least fun i => fixOrd_least (veblen_monotone hf.monotone _) _ z
      (le_intro fun a => hz₂ _ (index_lt x a)) (hz₁ (β i) (index_lt β i)).ge)
    exact le_trans (hf.monotone _ _ (le_of_forall_lt fun y hy =>
      lt_of_le_of_lt (veblen_inflationary hf β y) (hz₂ y hy)))
      (equiv_trans (hz₁ 0 h₀) (veblen_zero f z)).ge

/-- Rocq: `VeblenClassical.strongly_critical_fixpoint`. -/
theorem strongly_critical_fixpoint (hf : NormalFunction f) (hzd : ∀ x : Ordinal.{u}, x ≤ 0 ∨ 0 < x)
    (hd : ∀ x : Ordinal.{u}, Directed x.Carrier x.size) (β : Ordinal.{u}) :
    StronglyCriticalOrdinal f β ↔ veblen f β 0 ≈ β := by
  refine ⟨fun ⟨h₀, h⟩ => equiv_intro ?_ (increasing_inflationary
      (fun x y h => veblen_increasing_first hf hzd hd x y h) β),
    fun h => ⟨lt_of_lt_of_le (veblen_nonzero hf β 0) h.le, fun α hαβ => ?_⟩⟩
  · rw [veblen_unroll]
    refine lub_least ?_ (sup_least fun a => fixOrd_least (veblen_monotone hf.monotone _) _ β
      (le_intro fun z => PEmpty.elim z) (h (β a) (index_lt β a)).ge)
    exact le_trans (hf.monotone _ _ (zero_least β)) (equiv_trans (h 0 h₀) (veblen_zero f β)).ge
  · refine equiv_trans (equiv_symm h) (equiv_trans (equiv_symm
      (veblen_fixpoints hf hzd hd α β 0 hαβ)) ?_)
    exact equiv_intro (veblen_monotone hf.monotone α _ _ h.le) (veblen_monotone hf.monotone α _ _ h.ge)

/-- Rocq: `VeblenClassical.powOmega_normal`. -/
theorem powOmega_normal : NormalFunction (powOmega : Ordinal.{u} → Ordinal.{u}) where
  monotone := powOmega_monotone'
  increasing _ _ h := powOmega_increasing h
  continuous := pow_continuous ω
  nonzero x := pow_pos ω x

/-- Rocq: `VeblenClassical.enum_fixpoints_normal`. -/
theorem enum_fixpoints_normal (hf : NormalFunction f) : NormalFunction (enumFixpoints f) where
  monotone := enumFixpoints_monotone hf.monotone
  increasing _ _ h := enumFixpoints_increasing hf.monotone h
  continuous := enumFixpoints_cont hf.monotone (normal_inflationary hf) hf.continuous
  nonzero x := lt_of_lt_of_le (hf.nonzero _)
    (enum_are_fixpoints hf.continuous (normal_inflationary hf) x).ge

private theorem zeroDec_of_em (em : ExcludedMiddle) (x : Ordinal.{u}) : x ≤ 0 ∨ 0 < x :=
  order_total em x 0

private theorem directed_of_em (em : ExcludedMiddle) (x : Ordinal.{u}) : Directed x.Carrier x.size :=
  ord_directed em x.Carrier x.size

/-- Rocq: `VeblenClassical.Γ_fixpoints`. -/
theorem Γ_fixpoints (em : ExcludedMiddle) (a : Ordinal.{u}) : Γ a ≈ veblen powOmega (Γ a) 0 :=
  enum_are_fixpoints (veblen_continuous_first powOmega_normal)
    (increasing_inflationary fun x y h =>
      veblen_increasing_first powOmega_normal (zeroDec_of_em em) (directed_of_em em) x y h) a

/-- Rocq: `VeblenClassical.Γ_normal`. -/
theorem Γ_normal (em : ExcludedMiddle) : NormalFunction (Γ : Ordinal.{u} → Ordinal.{u}) :=
  enum_fixpoints_normal (veblen_first_normal powOmega_normal (zeroDec_of_em em) (directed_of_em em))

/-- Rocq: `VeblenClassical.Γ₀_least`. -/
theorem Γ₀_least (x : Ordinal.{u}) (h : veblen powOmega x 0 ≈ x) : Γ 0 ≤ x :=
  le_trans (enumFixpoints_zero fun a b h => veblen_monotone_first powOmega_monotone' b a 0 h).le
    (fixOrd_least (fun a b h => veblen_monotone_first powOmega_monotone' b a 0 h) 0 x
      (zero_least x) h.le)

/-- Rocq: `VeblenClassical.Γ_enumerates`. -/
theorem Γ_enumerates (em : ExcludedMiddle) :
    Enumerates (Γ : Ordinal.{u} → Ordinal.{u}) (StronglyCriticalOrdinal powOmega) :=
  have hn := veblen_first_normal powOmega_normal (zeroDec_of_em em) (directed_of_em em)
  Enumerates.of_iff
    (fun x => ⟨fun h => (strongly_critical_fixpoint powOmega_normal (zeroDec_of_em em)
        (directed_of_em em) x).2 (equiv_symm h),
      fun h => equiv_symm ((strongly_critical_fixpoint powOmega_normal (zeroDec_of_em em)
        (directed_of_em em) x).1 h)⟩)
    (enumFixpoints_enumerates (normal_inflationary hn) hn.monotone hn.continuous)

/-- The fixpoints of `b ↦ veblen Γ b 0`. Rocq: `VeblenClassical.Ξ`. -/
def Ξ (a : Ordinal.{u}) : Ordinal.{u} := enumFixpoints (fun b => veblen Γ b 0) a

/-- Rocq: `VeblenClassical.Ξ_fixpoints`. -/
theorem Ξ_fixpoints (em : ExcludedMiddle) (a : Ordinal.{u}) : Ξ a ≈ veblen Γ (Ξ a) 0 :=
  enum_are_fixpoints (veblen_continuous_first (Γ_normal em))
    (increasing_inflationary fun x y h =>
      veblen_increasing_first (Γ_normal em) (zeroDec_of_em em) (directed_of_em em) x y h) a

/-- Rocq: `VeblenClassical.Ξ_normal`. -/
theorem Ξ_normal (em : ExcludedMiddle) : NormalFunction (Ξ : Ordinal.{u} → Ordinal.{u}) :=
  enum_fixpoints_normal (veblen_first_normal (Γ_normal em) (zeroDec_of_em em) (directed_of_em em))

/-- Rocq: `VeblenClassical.Ξ_enumerates`. -/
theorem Ξ_enumerates (em : ExcludedMiddle) :
    Enumerates (Ξ : Ordinal.{u} → Ordinal.{u}) (StronglyCriticalOrdinal Γ) :=
  have hn := veblen_first_normal (Γ_normal em) (zeroDec_of_em em) (directed_of_em em)
  Enumerates.of_iff
    (fun x => ⟨fun h => (strongly_critical_fixpoint (Γ_normal em) (zeroDec_of_em em)
        (directed_of_em em) x).2 (equiv_symm h),
      fun h => equiv_symm ((strongly_critical_fixpoint (Γ_normal em) (zeroDec_of_em em)
        (directed_of_em em) x).1 h)⟩)
    (enumFixpoints_enumerates (normal_inflationary hn) hn.monotone hn.continuous)

end VeblenClassical

end Ordinal

end ConstructiveOrdinals
