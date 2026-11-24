From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import AckermannTower.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.

From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannAssoc.
From Ordinal Require Import BachmannPower.

Open Scope ord_scope.

(** * Calibration against known hierarchies

The step theorems of @BachmannDefs@ and the power theorem of
@BachmannPower@ give φ_Ω = Γ₀, φ_{Ω·ξ} as ternary Veblen,
φ_{Ω²}(0) as Ackermann's ordinal, and the Small and Large Veblen
Ordinals. *)

(** ** Calibrations, as corollaries of the step theorems *)

Lemma powOmega_le_veblen0 x : complete x -> powOmega x ≤ veblen powOmega x 0.
Proof.
  intro Hx.
  transitivity (powOmega (x + 0)).
  - apply powOmega_monotone, (proj2 (addOrd_zero_r x)).
  - apply veblen_fax; auto using powOmega_normal, zero_complete.
Qed.

(** φ_Ω enumerates the strongly critical ordinals: φ_Ω(0) = Γ₀. *)
Theorem bach_Ω_rep : BRep powOmega bOmega Γ.
Proof.
  apply bach_Ωlim_step.
  - apply veblen_first_normal, powOmega_normal.
  - apply bach_embed0_mono.
  - intros x _; apply bach_embed, powOmega_monotone.
  - apply powOmega_le_veblen0.
Qed.

Corollary bach_Ω_Γ : forall y, complete y -> bach powOmega bOmega y ≈ Γ y.
Proof. apply bach_Ω_rep. Qed.

(** φ_{Ω+ξ} is the Veblen hierarchy over Γ. *)
Theorem bach_Ω_plus_rep ξ : complete ξ -> BRep powOmega (badd bOmega (embed ξ)) (veblen Γ ξ).
Proof.
  apply bach_veblen_step; auto using powOmega_monotone, bach_Ω_rep.
  apply bmono_Ω, powOmega_monotone.
Qed.

Corollary bach_Ω_plus : forall ξ, complete ξ -> forall y, complete y ->
  bach powOmega (badd bOmega (embed ξ)) y ≈ veblen Γ ξ y.
Proof.
  intros ξ Hξ. apply (bach_Ω_plus_rep ξ Hξ).
Qed.

Theorem bach_Ω1_rep : BRep powOmega (badd bOmega (bsucc bzero)) (enum_fixpoints Γ).
Proof.
  apply bach_succ_step.
  - apply powOmega_monotone.
  - apply bmono_Ω, powOmega_monotone.
  - apply bach_Ω_rep.
Qed.

(** *** φ_{Ω·2} enumerates the fixpoints of ξ ↦ φ_{Ω+ξ}(0) *)

Definition bOmega2 : BOrd := badd bOmega bOmega.

Lemma bmono_Ω2 f (Hf : forall x y, x ≤ y -> f x ≤ f y) : bmono f bOmega2.
Proof.
  apply bmono_badd_Ω, bmono_Ω; auto.
Qed.

Definition Γ2 : Ord -> Ord := enum_fixpoints (fun ξ => veblen Γ ξ 0).

Theorem bach_Ω2_rep : BRep powOmega bOmega2 Γ2.
Proof.
  apply bach_plusΩ_step.
  - apply powOmega_monotone.
  - apply bmono_Ω, powOmega_monotone.
  - apply bach_Ω_rep.
Qed.

Corollary bach_Ω2 : forall y, complete y -> bach powOmega bOmega2 y ≈ Γ2 y.
Proof. apply bach_Ω2_rep. Qed.

(** *** φ_{Ω·n} is the n-fold iterated Γ construction *)

Fixpoint bOmegaMul (n:nat) : BOrd :=
  match n with
  | O => bzero
  | S n' => badd (bOmegaMul n') bOmega
  end.

Fixpoint Γiter (f:Ord -> Ord) (n:nat) : Ord -> Ord :=
  match n with
  | O => f
  | S n' => enum_fixpoints (fun ξ => veblen (Γiter f n') ξ 0)
  end.

Theorem bach_Ωmul_rep f : normal_function f ->
  forall n, bmono f (bOmegaMul n) /\ BRep f (bOmegaMul n) (Γiter f n).
Proof.
  intros Hf n.
  assert (Hm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction n as [|n [IH1 IH2]]; simpl.
  - split; [ apply bmono_bzero | apply bach_zero_rep; auto ].
  - split; [ apply bmono_badd_Ω; auto | apply bach_plusΩ_step; auto ].
Qed.

(** In particular φ_{0+Ω} is Γ, definitionally on the right. *)
Example bach_Ωmul1_Γ : forall y, complete y -> bach powOmega (bOmegaMul 1) y ≈ Γ y.
Proof.
  apply (proj2 (bach_Ωmul_rep powOmega powOmega_normal 1)).
Qed.

(** ** Multiples of Ω: φ_{Ω·ξ} is ternary Veblen

The tree @bmul bOmega (embed ξ)@ merges, via @bsup@, the children of
the trees Ω·ξ_i + Ω.  Its components are therefore the components of
each Ω·ξ_i together with each diagonal ζ ↦ φ_{Ω·ξ_i+ζ}(0).  We show
that it represents the third column of Schütte's Klammersymbols,
@schutte_column f 2 ξ@, i.e., the ternary Veblen function φ(ξ,0,·),
for all complete ξ (including limits), and deduce that φ_{Ω²}
enumerates the fixpoints of ξ ↦ φ(ξ,0,0).
*)

Lemma bmono_small f x : bmono f x -> forall a, bmono f (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_big f x : bmono f x -> forall c ξ, bmono f (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_diag f x : bmono f x ->
  forall c ξ ξ', ξ ≤ ξ' -> bach f (bbigSz x c ξ) 0 ≤ bach f (bbigSz x c ξ') 0.
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_bsup f {I:Type} (F:I -> BOrd) : (forall i, bmono f (F i)) -> bmono f (bsup F).
Proof.
  intro H; simpl.
  split; [ | split ].
  - intros [i a]. apply bmono_small; auto.
  - intros [i c] ξ. apply bmono_big; auto.
  - intros [i c] ξ ξ' Hξ. apply bmono_diag; auto.
Qed.

Lemma bmono_bmulΩ f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall ξ, bmono f (bmul bOmega (embed ξ)).
Proof.
  induction ξ as [X k Hk].
  rewrite (bmul_eq bOmega (embed (ord X k))).
  apply bmono_blub.
  - unfold bmulS. apply bmono_bsup. intro a.
    apply bmono_badd_Ω; auto. apply (Hk a).
  - unfold bmulB; simpl. split; [ intros [] | split; intros [] ].
Qed.

Lemma bsub_badd_embed_l x x' : bsub x x' -> forall ζ, bsub (badd x (embed ζ)) (badd x' (embed ζ)).
Proof.
  intros H ζ.
  induction ζ as [Z m Hm].
  rewrite (badd_eq x (embed (ord Z m))), (badd_eq x' (embed (ord Z m))).
  apply bsub_blub; auto.
  unfold baddR; simpl; split.
  - intro b. exists b. apply Hm.
  - intros [].
Qed.

Lemma bsub_badd_Ω_l x x' : bsub x x' -> bsub (badd x bOmega) (badd x' bOmega).
Proof.
  intro H.
  rewrite (badd_eq x bOmega), (badd_eq x' bOmega).
  apply bsub_blub; auto.
  unfold baddR; simpl; split.
  - intros [].
  - intros _. exists tt. intro ζ. apply bsub_badd_embed_l; auto.
Qed.

Lemma bsub_bmulΩ : forall ξ ξ', ξ ≤ ξ' ->
  bsub (bmul bOmega (embed ξ)) (bmul bOmega (embed ξ')).
Proof.
  induction ξ as [X k Hk]; intros [X' k'] H.
  rewrite (bmul_eq _ (embed (ord X k))), (bmul_eq _ (embed (ord X' k'))).
  apply bsub_blub.
  - unfold bmulS. apply bsub_bsup. intro a.
    destruct (ord_le_subord _ _ H a) as [b Hb].
    exists b. apply bsub_badd_Ω_l. apply Hk. exact Hb.
  - unfold bmulB; simpl; split; intros [].
Qed.

(** Classification of the components of α+Ω and of Ω·ξ. *)
Lemma bcomp_badd_Ω_forall f T (P:(Ord -> Ord) -> Prop) :
  (forall k, P (bcomp f T k)) ->
  P (fun ζ => bach f (badd T (embed ζ)) 0) ->
  forall k, P (bcomp f (badd T bOmega) k).
Proof.
  destruct T as [A g C h].
  intros H1 H2 [[a|[]]|[c|[]]].
  - apply (H1 (inl a)).
  - apply (H1 (inr c)).
  - apply H2.
Qed.

Lemma badd_Ω_diag f T :
  exists k, bcomp f (badd T bOmega) k = (fun ζ => bach f (badd T (embed ζ)) 0).
Proof.
  destruct T. exists (inr (inr tt)). reflexivity.
Qed.

Lemma bcomp_bmulΩ_forall f X (k:X -> Ord) (P:(Ord -> Ord) -> Prop) :
  (forall b kk, P (bcomp f (badd (bmul bOmega (embed (k b))) bOmega) kk)) ->
  forall kk, P (bcomp f (bmul bOmega (embed (ord X k))) kk).
Proof.
  intro H.
  intros [[[b a]|[]]|[[b c]|[]]].
  - apply (H b (inl a)).
  - apply (H b (inr c)).
Qed.

Lemma bach_bmulΩ_diag_le f X (k:X -> Ord) (y:Ord) b :
  fixOrd (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
         (limOrd (fun j => bach f (bmul bOmega (embed (ord X k))) (y j)))
  ≤ bach f (bmul bOmega (embed (ord X k))) y.
Proof.
  destruct (badd_Ω_diag f (bmul bOmega (embed (k b)))) as [kk Hkk].
  rewrite <- Hkk.
  destruct kk as [a|c].
  - exact (bach_comp_le f (bmul bOmega (embed (ord X k))) y (inl (inl (existT _ b a)))).
  - exact (bach_comp_le f (bmul bOmega (embed (ord X k))) y (inr (inl (existT _ b c)))).
Qed.

Lemma lt_0_2 : 0 < succOrd 1.
Proof. rewrite ord_lt_unfold. exists tt. apply zero_least. Qed.

Theorem bach_Ωtimes_rep f (Hf : normal_function f) :
  forall ξ, complete ξ -> BRep f (bmul bOmega (embed ξ)) (S2 f ξ).
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [_ Hkc]].
  assert (HS : normal_function (S2 f (ord X k))).
  { apply schutte_column_normal; auto using complete_2. }
  assert (HSk : forall b, normal_function (S2 f (k b))).
  { intro b. apply schutte_column_normal; auto using complete_2. }
  assert (HT : bmono f (bmul bOmega (embed (ord X k)))) by (apply bmono_bmulΩ; auto).
  assert (HTk : forall b, bmono f (bmul bOmega (embed (k b)))) by (intro; apply bmono_bmulΩ; auto).
  assert (Hplus : forall b ζ, complete ζ ->
             BRep f (badd (bmul bOmega (embed (k b))) (embed ζ)) (veblen (S2 f (k b)) ζ)).
  { intros b ζ Hζ. apply bach_veblen_step; auto. }
  assert (Hdiag : forall b x, complete x ->
             bach f (badd (bmul bOmega (embed (k b))) (embed x)) 0 ≈
             schutte_column (S2 f (k b)) 1 x 0).
  { intros b x Hx.
    transitivity (veblen (S2 f (k b)) x 0).
    - apply (Hplus b x Hx); apply zero_complete.
    - symmetry. apply schutte_column_veblen; auto using zero_complete. }
  (* every component fixes the values of S2 ξ *)
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (bmul bOmega (embed (ord X k))) kk (S2 f (ord X k) y) ≤ S2 f (ord X k) y).
  { intros kk y Hy.
    assert (Hv : complete (S2 f (ord X k) y)) by (apply normal_complete; auto).
    apply (bcomp_bmulΩ_forall f X k (fun g => g (S2 f (ord X k) y) ≤ S2 f (ord X k) y)).
    intro b.
    assert (Hfix0 : S2 f (k b) (S2 f (ord X k) y) ≤ S2 f (ord X k) y).
    { transitivity (schutte_column (S2 f (k b)) 0 (S2 f (ord X k) y) 0).
      - rewrite schutte_column0. apply normal_monotone; auto. apply addOrd_le1.
      - apply schutte_column_fixpoint; auto using complete_2, zero_complete, lt_0_2.
        apply (index_lt (ord X k) b). }
    apply (bcomp_badd_Ω_forall f (bmul bOmega (embed (k b)))
             (fun g => g (S2 f (ord X k) y) ≤ S2 f (ord X k) y)).
    - intro kk'.
      transitivity (bcomp f (bmul bOmega (embed (k b))) kk' (S2 f (k b) (S2 f (ord X k) y))).
      { apply bmono_bcomp; auto. apply normal_inflationary; auto. }
      transitivity (S2 f (k b) (S2 f (ord X k) y)); auto.
      apply (Hk b (Hkc b)); auto.
    - transitivity (schutte_column (S2 f (k b)) 1 (S2 f (ord X k) y) 0).
      + apply (proj1 (Hdiag b _ Hv)).
      + apply schutte_column_fixpoint; auto using complete_2, complete_1, succ_lt.
        apply (index_lt (ord X k) b). }
  split; [ exact HS | split; [ | exact Hcomp ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (bmul bOmega (embed (ord X k))) (ord Y h j)) ≈
               limOrd (fun j => S2 f (ord X k) (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => S2 f (ord X k) (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (f (ord X k + ord Y h)).
      * apply Hfm, addOrd_le2.
      * apply schutte_column_le_f; auto.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hfm _ HT) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply normal_increasing; auto.
      apply (index_lt (ord Y h) j).
  - eapply ord_le_trans;
      [ apply (proj1 (schutte_column_succ f 1 (ord X k) (ord Y h) Hf complete_1 Hξ Hyc)) | ].
    apply lub_least; [ apply f_le_bach | ].
    apply sup_least; intro b.
    eapply ord_le_trans; [ | apply (bach_bmulΩ_diag_le f X k (ord Y h) b) ].
    assert (HN1 : normal_function (fun δ => schutte_column (S2 f (k b)) 1 δ 0)).
    { apply schutte_column_normal_arg; auto using complete_1. }
    apply (proj2 (fixOrd_eq_func_complete
                    (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
                    (fun δ => schutte_column (S2 f (k b)) 1 δ 0) _ _
                    (Hdiag b)
                    (badd_embed_diag_mono f Hfm _ (HTk b))
                    (normal_monotone _ HN1) (normal_complete _ HN1) Hs Hsc)).
Qed.

(** φ_{Ω²} enumerates the fixpoints of ξ ↦ φ(ξ,0,0). *)
Definition bOmegaSq : BOrd := bmul bOmega bOmega.

Theorem bach_Ωsq_rep f (Hf : normal_function f) :
  BRep f bOmegaSq (enum_fixpoints (fun ξ => S2 f ξ 0)).
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HN : normal_function (fun ξ => S2 f ξ 0)).
  { apply schutte_column_normal_arg; auto using complete_2. }
  refine (bach_enum_step f bOmegaSq _ (inr (inr tt)) HN _ _ _ _).
  - intros [[[[] ?]|[]]|[[[] ?]|[]]] x y Hxy.
    apply bach_mono_index; auto.
    + apply bsub_bmulΩ; auto.
    + apply bmono_bmulΩ; auto.
  - intros x Hx. apply (bach_Ωtimes_rep f Hf x Hx); apply zero_complete.
  - intros x Hx.
    transitivity (f (x + 0)); [ apply Hfm, (proj2 (addOrd_zero_r x)) | ].
    apply schutte_column_le_f; auto.
  - intros [[[[] ?]|[]]|[[[] ?]|[]]] y Hy.
    assert (Hv : complete (enum_fixpoints (fun ξ => S2 f ξ 0) y)).
    { apply normal_complete; [ apply enum_fixpoints_normal; auto | auto ]. }
    change (bach f (bmul bOmega (embed (enum_fixpoints (fun ξ => S2 f ξ 0) y))) 0
            ≤ enum_fixpoints (fun ξ => S2 f ξ 0) y).
    transitivity (S2 f (enum_fixpoints (fun ξ => S2 f ξ 0) y) 0).
    + apply (bach_Ωtimes_rep f Hf _ Hv); apply zero_complete.
    + apply (proj2 (enum_are_fixpoints _ HN y Hy)).
Qed.

(** With base 1+x, φ_{Ω²}(0) is Ackermann's ordinal, as defined in
    @AckermannTower@. *)
Theorem bach_Ωsq_Ackermann : bach (addOrd 1) bOmegaSq 0 ≈ AckermannOrdinal.
Proof.
  assert (HN : normal_function (fun ξ => S2 (addOrd 1) ξ 0)).
  { apply schutte_column_normal_arg; auto using complete_2, onePlus_normal. }
  transitivity (enum_fixpoints (fun ξ => S2 (addOrd 1) ξ 0) 0).
  { apply (bach_Ωsq_rep (addOrd 1) onePlus_normal); apply zero_complete. }
  transitivity (fixOrd (fun ξ => S2 (addOrd 1) ξ 0) 0).
  { apply enum_fixpoints_zero; auto. }
  unfold AckermannOrdinal.
  apply fixOrd_eq_func_complete.
  - intros x Hx. apply schutte_column_2_ackermann_tower; auto using onePlus_normal, zero_complete.
  - apply normal_monotone; auto.
  - intros x y Hxy. apply ackermann_tower_monotone; auto with ord.
  - apply normal_complete, ackermann_tower_normal_first, onePlus_normal.
  - reflexivity.
  - apply zero_complete.
Qed.

(** ** The Small and Large Veblen Ordinals *)

Theorem bach_SVO f (Hf : normal_function f) :
  bach f (bexpΩ (embed ω)) 0 ≈ schutte_column f ω 1 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  transitivity (schutte_column f (1 + ω) 1 0).
  { apply bach_bexpΩ_zero; auto using omega_complete. }
  split; apply schutte_column_monotoneβ; auto.
  - apply limit_onePlus, omega_limit.
  - apply addOrd_le2.
Qed.

Corollary bach_SVO_SmallVeblen : bach powOmega (bexpΩ (embed ω)) 0 ≈ SmallVeblenOrdinal.
Proof.
  exact (bach_SVO powOmega powOmega_normal).
Qed.

Lemma LVO_onePlus f (Hf : normal_function f) :
  fixOrd (fun ζ => schutte_column f (1 + ζ) 1 0) 0 ≈ fixOrd (fun β => schutte_column f β 1 0) 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HF : normal_function (fun β => schutte_column f β 1 0)) by (apply schutte_column_normalβ; auto).
  assert (HLc : complete (fixOrd (fun β => schutte_column f β 1 0) 0)).
  { apply normal_fix_complete; auto using zero_complete.
    - apply normal_inflationary; auto.
    - apply normal_monotone; auto.
    - apply normal_complete; auto. }
  assert (HLfix := normal_fixpoint _ HF 0 zero_complete).
  split.
  - apply fixOrd_least; auto using zero_least.
    + intros x y Hxy. apply schutte_column_monotoneβ; auto.
      apply addOrd_monotone; auto. reflexivity.
    + transitivity (schutte_column f (fixOrd (fun β => schutte_column f β 1 0) 0) 1 0).
      * apply schutte_column_monotoneβ; auto.
        transitivity (schutte_column f (fixOrd (fun β => schutte_column f β 1 0) 0) 1 0).
        -- apply (onePlus_least_normal (fun β => schutte_column f β 1 0)); auto.
        -- apply (proj2 HLfix).
      * apply (proj2 HLfix).
  - apply fixOrd_monotone_func.
    + intro x. apply schutte_column_monotoneβ; auto. apply addOrd_le2.
    + intros x y Hxy. apply schutte_column_monotoneβ; auto.
      apply addOrd_monotone; auto. reflexivity.
Qed.

(** Ω^Ω is the canonical tree @bexpΩ bOmega@: the small child 0 (from
    the leading 1) and the single family ζ ↦ Ω^ζ. *)
Theorem bach_LVO f (Hf : normal_function f) :
  bach f (bexpΩ bOmega) 0 ≈ fixOrd (fun β => schutte_column f β 1 0) 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HF : normal_function (fun β => schutte_column f β 1 0)) by (apply schutte_column_normalβ; auto).
  assert (HLc : complete (fixOrd (fun β => schutte_column f β 1 0) 0)).
  { apply normal_fix_complete; auto using zero_complete.
    - apply normal_inflationary; auto.
    - apply normal_monotone; auto.
    - apply normal_complete; auto. }
  assert (HLfix := normal_fixpoint _ HF 0 zero_complete).
  assert (HDmono : forall x y, x ≤ y -> bach f (bexpΩ (embed x)) 0 ≤ bach f (bexpΩ (embed y)) 0).
  { intros x y Hxy. apply bach_mono_index; auto.
    - apply bsub_bexpΩ, bsub_embed; auto.
    - apply bfam_bmono; auto. apply bfam_bexpΩ, bfam_embed. }
  assert (HD'mono : forall x y, x ≤ y -> schutte_column f (1 + x) 1 0 ≤ schutte_column f (1 + y) 1 0).
  { intros x y Hxy. apply schutte_column_monotoneβ; auto.
    apply addOrd_monotone; auto. reflexivity. }
  assert (HD'c : forall x, complete x -> complete (schutte_column f (1 + x) 1 0)).
  { intros x Hx. apply normal_complete; auto using zero_complete.
    apply schutte_column_normal; auto using onePlus_complete, complete_1. }
  assert (Hs0 : limOrd (fun j:ordCarrier 0 => bach f (bexpΩ bOmega) (0 j)) ≈ 0).
  { split; [ apply limit_least; intros [] | apply zero_least ]. }
  assert (Hdiag : fixOrd (fun ζ => bach f (bexpΩ (embed ζ)) 0)
                         (limOrd (fun j:ordCarrier 0 => bach f (bexpΩ bOmega) (0 j)))
                  ≈ fixOrd (fun β => schutte_column f β 1 0) 0).
  { transitivity (fixOrd (fun ζ => schutte_column f (1 + ζ) 1 0) 0).
    - apply fixOrd_eq_func_complete; auto using zero_complete.
      intros x Hx. apply bach_bexpΩ_zero; auto.
    - apply LVO_onePlus; auto. }
  (* the value L is a fixpoint of f *)
  assert (HfL : f (fixOrd (fun β => schutte_column f β 1 0) 0) ≤ fixOrd (fun β => schutte_column f β 1 0) 0).
  { set (L := fixOrd (fun β => schutte_column f β 1 0) 0) in *.
    assert (HL0 : 0 < L).
    { eapply ord_lt_le_trans; [ | apply (proj2 HLfix) ].
      eapply ord_lt_le_trans; [ apply (normal_nonzero f Hf (1 + 0)) | ].
      apply schutte_column_le_f; auto. }
    transitivity (f (schutte_column f L 1 0)); [ apply Hfm, (proj1 HLfix) | ].
    transitivity (schutte_column (schutte_column f L 0) 0 (schutte_column f L 1 0) 0).
    - rewrite schutte_column0.
      transitivity (schutte_column f L 0 (schutte_column f L 1 0)).
      + rewrite schutte_column_arg0; auto. reflexivity.
      + apply schutte_column_monotone; auto. reflexivity. apply addOrd_le1.
    - eapply ord_le_trans; [ apply schutte_column_fixpoint; auto using complete_1, zero_complete | ].
      + rewrite ord_lt_unfold. exists tt. reflexivity.
      + apply (proj2 HLfix). }
  split.
  - apply bach_le_comp.
    + transitivity (f (fixOrd (fun β => schutte_column f β 1 0) 0)); auto.
      apply Hfm, zero_least.
    + intros [[[]|[[[] _]|[]]]|[[]|[[[] _]|[]]]].
      * apply fixOrd_least; [ apply bmono_bcomp; auto; apply bfam_bmono; auto using bfam_bexpΩ, bfam_Ω | | ].
        { apply limit_least; intros []. }
        change (bach f bzero (fixOrd (fun β => schutte_column f β 1 0) 0)
                ≤ fixOrd (fun β => schutte_column f β 1 0) 0).
        rewrite bach_bzero. exact HfL.
      * exact (proj1 Hdiag).
  - eapply ord_le_trans; [ apply (proj2 Hdiag) | ].
    apply (bach_comp_le f (bexpΩ bOmega) 0 (inr (inr (inr tt)))).
Qed.

Corollary bach_LVO_LargeVeblen : bach powOmega (bexpΩ bOmega) 0 ≈ LargeVeblenOrdinal.
Proof.
  exact (bach_LVO powOmega powOmega_normal).
Qed.
