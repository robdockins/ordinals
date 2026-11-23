From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.

Import ListNotations.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannAssoc.
From Ordinal Require Import BachmannPower.

Open Scope ord_scope.

(** * The enumerator of common fixpoints, and the hierarchy @bphi@

Parts (A) and (B) of the direct proof of normality; the rest is in
@BachmannNormal@ and @BachmannAgree@. *)

(** ** (A) Enumerating the common fixpoints of a family of normal functions *)

Section common_fixpoints.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Variable I : Type.
  Variable F : I -> Ord -> Ord.
  Hypothesis HF : forall i, normal_function (F i).

  (** Finite compositions F_{i_1} ∘ … ∘ F_{i_n} ∘ f. *)
  Fixpoint comps (L:list I) : Ord -> Ord :=
    match L with
    | [] => f
    | i :: L' => fun x => F i (comps L' x)
    end.

  Lemma comps_normal L : normal_function (comps L).
  Proof.
    induction L as [|i L IH]; simpl; auto.
    apply compose_normal; auto.
  Qed.

  Lemma comps_complete L : forall x, complete x -> complete (comps L x).
  Proof. apply normal_complete, comps_normal. Qed.

  Lemma comps_app_le_l L1 L2 x : complete x -> comps L1 x ≤ comps (L1 ++ L2) x.
  Proof.
    intro Hx.
    induction L1 as [|i L1 IH]; simpl.
    - induction L2 as [|j L2 IH2]; simpl; [ reflexivity | ].
      transitivity (comps L2 x); auto.
      apply normal_inflationary; auto. apply comps_complete; auto.
    - apply normal_monotone; auto.
  Qed.

  Lemma comps_app_le_r L1 L2 x : complete x -> comps L2 x ≤ comps (L1 ++ L2) x.
  Proof.
    intro Hx.
    induction L1 as [|i L1 IH]; simpl; [ reflexivity | ].
    transitivity (comps (L1 ++ L2) x); auto.
    apply normal_inflationary; auto. apply comps_complete; auto.
  Qed.

  (** Every composition fixes a point that f and all the F_i fix. *)
  Lemma comps_closed L z : f z ≤ z -> (forall i, F i z ≤ z) -> comps L z ≤ z.
  Proof.
    intros H1 H2.
    induction L as [|i L IH]; simpl; auto.
    transitivity (F i z); auto.
    apply normal_monotone; auto.
  Qed.

End common_fixpoints.

(** ** Monotonicity of the enumerator in its family *)

Lemma comps_monotone_gen f I F :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall i x y, x ≤ y -> F i x ≤ F i y) ->
  forall L x y, x ≤ y -> comps f I F L x ≤ comps f I F L y.
Proof.
  intros Hf HF L.
  induction L as [|i L IH]; simpl; auto.
Qed.

Lemma comps_mono_family f I J F F' :
  (forall j x y, x ≤ y -> F' j x ≤ F' j y) ->
  (forall i, exists j, forall x, F i x ≤ F' j x) ->
  forall L, exists L', forall x, comps f I F L x ≤ comps f J F' L' x.
Proof.
  intros HF' Hfam L.
  induction L as [|i L [L' HL']].
  - exists []. intro; reflexivity.
  - destruct (Hfam i) as [j Hj].
    exists (j :: L'). intro x. simpl.
    transitivity (F' j (comps f I F L x)); auto.
Qed.


(** ** The enumerator *)

Section cfe.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Variable I : Type.
  Variable F : I -> Ord -> Ord.
  Hypothesis HF : forall i, normal_function (F i).

  Let Hfm : forall x y, x ≤ y -> f x ≤ f y.
  Proof. apply normal_monotone; auto. Qed.

  (** A nonempty composition: F_i after the composition L (which ends with f). *)
  Definition c1 (p:(I * list I)%type) : Ord -> Ord :=
    fun x => F (fst p) (comps f I F (snd p) x).

  Lemma c1_normal p : normal_function (c1 p).
  Proof.
    unfold c1. apply compose_normal; auto. apply comps_normal; auto.
  Qed.

  Lemma c1_ge_f p x : complete x -> f x ≤ c1 p x.
  Proof.
    intro Hx. unfold c1.
    transitivity (comps f I F (snd p) x).
    - apply (comps_app_le_l f Hf I F HF [] (snd p) x Hx).
    - apply normal_inflationary; auto. apply comps_complete; auto.
  Qed.

  Lemma c1_fix_f p z : complete z -> c1 p z ≤ z -> f z ≤ z.
  Proof. intros Hz H. transitivity (c1 p z); auto. apply c1_ge_f; auto. Qed.

  Lemma c1_fix_F p z : complete z -> c1 p z ≤ z -> F (fst p) z ≤ z.
  Proof.
    intros Hz H. transitivity (c1 p z); auto. unfold c1.
    apply normal_monotone; auto.
    apply normal_inflationary; auto. apply comps_normal; auto.
  Qed.

  Fixpoint cfe (y:Ord) : Ord :=
    match y with
    | ord Y h =>
      supOrd (fun o:option (I * list I) =>
                match o with
                | None => f (ord Y h)
                | Some p => fixOrd (c1 p) (ord Y (fun j => cfe (h j)))
                end)
    end.

  Definition cfe_term (y s:Ord) (o:option (I * list I)) : Ord :=
    match o with
    | None => f y
    | Some p => fixOrd (c1 p) s
    end.

  Lemma cfe_unroll (y:Ord) :
    cfe y = supOrd (cfe_term y (limOrd (fun j => cfe (y j)))).
  Proof. destruct y; reflexivity. Qed.

  Global Opaque cfe.

  Lemma cfe_ge_term y o : cfe_term y (limOrd (fun j => cfe (y j))) o ≤ cfe y.
  Proof. rewrite (cfe_unroll y). apply (sup_le _ (cfe_term _ _) o). Qed.

  Lemma cfe_ge_f y : f y ≤ cfe y.
  Proof. apply (cfe_ge_term y None). Qed.

  Lemma cfe_monotone : forall x y, x ≤ y -> cfe x ≤ cfe y.
  Proof.
    intros x y; revert x.
    induction y as [Y h Hy]; intros [X g] Hxy.
    rewrite (cfe_unroll (ord X g)).
    apply sup_least. intros [p|].
    - eapply ord_le_trans; [ | apply (cfe_ge_term (ord Y h) (Some p)) ].
      simpl. apply fixOrd_monotone; [ apply normal_monotone, c1_normal | ].
      apply limit_least; intro i.
      destruct (ord_le_subord _ _ Hxy i) as [j Hj].
      apply ord_le_lt_trans with (cfe (h j)); [ apply Hy; auto | ].
      rewrite ord_lt_unfold. exists j. reflexivity.
    - eapply ord_le_trans; [ | apply cfe_ge_f ]. simpl. apply Hfm; auto.
  Qed.

  Lemma cfe_inflationary y : complete y -> y ≤ cfe y.
  Proof.
    intro Hy. transitivity (f y); [ apply normal_inflationary; auto | apply cfe_ge_f ].
  Qed.

  Lemma cfe_start_ge (y:Ord) : (forall j, complete (y j)) -> y ≤ limOrd (fun j => cfe (y j)).
  Proof.
    destruct y as [Y h]. intro Hc.
    apply lim_le_mor. intro j. apply cfe_inflationary; auto.
  Qed.

  (** The terms at a node, with a complete start above y, are directed. *)
  Lemma cfe_dir (y s:Ord) : complete s -> y ≤ s -> directed _ (cfe_term y s).
  Proof.
    intros Hs Hys.
    assert (HfP : forall p, f y ≤ fixOrd (c1 p) s).
    { intro p.
      transitivity (f s); [ apply Hfm; auto | ].
      transitivity (c1 p s); [ apply c1_ge_f; auto | ].
      unfold fixOrd. apply (sup_le _ (iter_f (c1 p) s) 1%nat). }
    intros [[i1 L1]|] [[i2 L2]|].
    - exists (Some (i1, L1 ++ i2 :: L2)). simpl. split.
      + apply fixOrd_monotone_func''; auto.
        * intros x Hx. unfold c1; simpl. apply normal_monotone; auto.
          apply comps_app_le_l; auto.
        * intros x Hx. apply (normal_complete _ (c1_normal _)); auto.
        * apply normal_monotone, c1_normal.
      + apply fixOrd_monotone_func''; auto.
        * intros x Hx. unfold c1; simpl.
          transitivity (comps f I F (L1 ++ i2 :: L2) x).
          { apply (comps_app_le_r f Hf I F HF L1 (i2 :: L2) x Hx). }
          apply normal_inflationary; auto. apply comps_complete; auto.
        * intros x Hx. apply (normal_complete _ (c1_normal _)); auto.
        * apply normal_monotone, c1_normal.
    - exists (Some (i1, L1)). simpl. split; [ reflexivity | apply HfP ].
    - exists (Some (i2, L2)). simpl. split; [ apply HfP | reflexivity ].
    - exists None. split; reflexivity.
  Qed.

  Lemma cfe_term_complete (y s:Ord) o : complete y -> complete s -> complete (cfe_term y s o).
  Proof.
    intros Hy Hs. destruct o as [p|]; simpl.
    - apply normal_fix_complete; auto.
      + apply normal_inflationary, c1_normal.
      + apply normal_monotone, c1_normal.
      + apply normal_complete, c1_normal.
    - apply normal_complete; auto.
  Qed.

  Lemma cfe_complete_start : forall y, complete y ->
    complete (cfe y) /\ complete (limOrd (fun j => cfe (y j))).
  Proof.
    induction y as [Y h Hy]; intro Hyc.
    assert (Hyc' := Hyc). destruct Hyc' as [Hdir [Hinh Hhc]].
    assert (Hs : complete (limOrd (fun j => cfe (ord Y h j)))).
    { apply lim_complete.
      - intro j. apply Hy; auto.
      - intros j1 j2. destruct (Hdir j1 j2) as [j' [H1 H2]].
        exists j'. split; apply cfe_monotone; auto.
      - exact Hinh. }
    split; auto.
    rewrite cfe_unroll.
    apply sup_complete.
    - intro o. apply cfe_term_complete; auto.
    - apply cfe_dir; auto. apply cfe_start_ge; auto.
    - left. exists None. simpl. apply normal_nonzero; auto.
  Qed.

  Lemma cfe_complete y : complete y -> complete (cfe y).
  Proof. intro Hy. apply (cfe_complete_start y Hy). Qed.

  Lemma cfe_nonzero y : 0 < cfe y.
  Proof. eapply ord_lt_le_trans; [ apply (normal_nonzero f Hf y) | apply cfe_ge_f ]. Qed.

  (** Least fixpoints of the compositions are fixed by f and by the F_i. *)
  Lemma c1_fixOrd_fix p s : complete s -> c1 p (fixOrd (c1 p) s) ≤ fixOrd (c1 p) s.
  Proof. intro Hs. apply (proj2 (normal_fixpoint _ (c1_normal p) s Hs)). Qed.

  Lemma cfe_fix_F i y : complete y -> F i (cfe y) ≤ cfe y.
  Proof.
    intro Hy.
    destruct (cfe_complete_start y Hy) as [_ Hs].
    assert (Hys := cfe_start_ge y (complete_subord y Hy)).
    rewrite (cfe_unroll y).
    eapply ord_le_trans;
      [ apply (normal_continuous _ (HF i) _ _ None (cfe_dir y _ Hs Hys)
                                 (fun o => cfe_term_complete y _ o Hy Hs)) | ].
    apply sup_least. intros [[j L]|]; simpl.
    - set (s := limOrd (fun j0 => cfe (y j0))) in *.
      assert (Hle : fixOrd (c1 (j, L)) s ≤ fixOrd (c1 (i, j :: L)) s).
      { apply fixOrd_monotone_func''; auto.
        - intros x Hx. unfold c1; simpl.
          apply normal_inflationary; auto. apply normal_complete; auto. apply comps_complete; auto.
        - intros x Hx. apply (normal_complete _ (c1_normal _)); auto.
        - apply normal_monotone, c1_normal. }
      eapply ord_le_trans; [ | apply (sup_le _ (cfe_term y s) (Some (i, j :: L))) ].
      transitivity (F i (fixOrd (c1 (i, j :: L)) s)); [ apply normal_monotone; auto | ].
      apply (c1_fix_F (i, j :: L)).
      + apply (cfe_term_complete y s (Some (i, j :: L)) Hy Hs).
      + apply c1_fixOrd_fix; auto.
    - set (s := limOrd (fun j0 => cfe (y j0))) in *.
      eapply ord_le_trans; [ | apply (sup_le _ (cfe_term y s) (Some (i, []))) ].
      transitivity (F i (fixOrd (c1 (i, [])) s)).
      + apply normal_monotone; auto.
        destruct (cfe_dir y s Hs Hys None (Some (i, []))) as [o3 _].
        transitivity (f s); [ apply Hfm; auto | ].
        transitivity (c1 (i, []) s); [ apply c1_ge_f; auto | ].
        unfold fixOrd. apply (sup_le _ (iter_f (c1 (i, [])) s) 1%nat).
      + apply (c1_fix_F (i, [])).
        * apply (cfe_term_complete y s (Some (i, [])) Hy Hs).
        * apply c1_fixOrd_fix; auto.
  Qed.

  (** With at least one component, values are fixpoints of f. *)
  Lemma cfe_fix_f (i:I) y : complete y -> f (cfe y) ≤ cfe y.
  Proof.
    intro Hy.
    destruct (cfe_complete_start y Hy) as [_ Hs].
    assert (Hys := cfe_start_ge y (complete_subord y Hy)).
    rewrite (cfe_unroll y).
    eapply ord_le_trans;
      [ apply (normal_continuous _ Hf _ _ None (cfe_dir y _ Hs Hys)
                                 (fun o => cfe_term_complete y _ o Hy Hs)) | ].
    set (s := limOrd (fun j0 => cfe (y j0))) in *.
    apply sup_least. intros [p|]; simpl.
    - eapply ord_le_trans; [ | apply (sup_le _ (cfe_term y s) (Some p)) ].
      apply (c1_fix_f p).
      + apply (cfe_term_complete y s (Some p) Hy Hs).
      + apply c1_fixOrd_fix; auto.
    - eapply ord_le_trans; [ | apply (sup_le _ (cfe_term y s) (Some (i, []))) ].
      transitivity (f (fixOrd (c1 (i, [])) s)).
      + apply Hfm.
        transitivity (f s); [ apply Hfm; auto | ].
        transitivity (c1 (i, []) s); [ apply c1_ge_f; auto | ].
        unfold fixOrd. apply (sup_le _ (iter_f (c1 (i, [])) s) 1%nat).
      + apply (c1_fix_f (i, [])).
        * apply (cfe_term_complete y s (Some (i, [])) Hy Hs).
        * apply c1_fixOrd_fix; auto.
  Qed.

  (** The value is the least ordinal above f y and the previous values
      that is fixed by f and every F_i (f only when some F_i exists). *)
  Lemma cfe_least (y z:Ord) :
    f y ≤ z -> limOrd (fun j => cfe (y j)) ≤ z ->
    (forall i, F i z ≤ z /\ f z ≤ z) -> cfe y ≤ z.
  Proof.
    intros H1 H2 H3.
    rewrite cfe_unroll. apply sup_least. intros [[i L]|]; simpl; auto.
    apply fixOrd_least; [ apply normal_monotone, c1_normal | auto | ].
    unfold c1; simpl.
    transitivity (F i z); [ | apply (proj1 (H3 i)) ].
    apply normal_monotone; auto.
    apply (comps_closed f I F HF L z); [ apply (proj2 (H3 i)) | intro j; apply (proj1 (H3 j)) ].
  Qed.

  (** Strict monotonicity needs to know, as a proposition, whether there
      are any components. *)
  Hypothesis HdecI : inhabited I \/ ~ inhabited I.

  Lemma cfe_increasing : forall x y, complete y -> x < y -> cfe x < cfe y.
  Proof.
    intros x [Y h] Hyc Hxy.
    rewrite ord_lt_unfold in Hxy. destruct Hxy as [j Hj].
    apply ord_le_lt_trans with (cfe (h j)); [ apply cfe_monotone; auto | ].
    destruct HdecI as [[i]|Hn].
    - eapply ord_lt_le_trans; [ | apply (cfe_ge_term (ord Y h) (Some (i, []))) ].
      simpl. eapply ord_lt_le_trans; [ | apply fixOrd_above ].
      rewrite ord_lt_unfold. exists j. reflexivity.
    - apply ord_le_lt_trans with (f (h j)).
      + rewrite (cfe_unroll (h j)). apply sup_least. intros [p|]; simpl.
        * elim Hn. exact (inhabits (fst p)).
        * reflexivity.
      + eapply ord_lt_le_trans; [ | apply cfe_ge_f ].
        apply normal_increasing; auto. apply (index_lt (ord Y h) j).
  Qed.

  Lemma cfe_continuous : scott_continuous cfe.
  Proof.
    intros A g a0 Hdir Hc.
    assert (Hdir' : directed A (fun a => cfe (g a))).
    { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
      exists a'. split; apply cfe_monotone; auto. }
    assert (Hc' : forall a, complete (cfe (g a))) by (intro; apply cfe_complete; auto).
    apply cfe_least.
    - eapply ord_le_trans; [ apply (normal_continuous f Hf A g a0 Hdir Hc) | ].
      apply sup_ord_le_morphism. intro a. apply cfe_ge_f.
    - apply limit_least. intros [a c].
      eapply ord_lt_le_trans; [ | apply (sup_le _ (fun a => cfe (g a)) a) ].
      apply cfe_increasing; [ apply Hc | apply (index_lt (g a) c) ].
    - intro i. split.
      + eapply ord_le_trans; [ apply (normal_continuous _ (HF i) A _ a0 Hdir' Hc') | ].
        apply sup_ord_le_morphism. intro a. apply cfe_fix_F; auto.
      + eapply ord_le_trans; [ apply (normal_continuous f Hf A _ a0 Hdir' Hc') | ].
        apply sup_ord_le_morphism. intro a. apply (cfe_fix_f i); auto.
  Qed.

  Theorem cfe_normal : normal_function cfe.
  Proof.
    constructor.
    - apply cfe_monotone.
    - apply cfe_increasing.
    - apply cfe_continuous.
    - apply cfe_complete.
    - apply cfe_nonzero.
  Qed.
End cfe.

(** ** Monotonicity of the enumerator in its family *)

Lemma c1_monotone_gen f I F :
  (forall x y, x ≤ y -> f x ≤ f y) -> (forall i x y, x ≤ y -> F i x ≤ F i y) ->
  forall p x y, x ≤ y -> c1 f I F p x ≤ c1 f I F p y.
Proof.
  intros Hf HF p x y Hxy. unfold c1. apply HF. apply comps_monotone_gen; auto.
Qed.

Lemma cfe_monotone_gen f I F :
  (forall x y, x ≤ y -> f x ≤ f y) -> (forall i x y, x ≤ y -> F i x ≤ F i y) ->
  forall x y, x ≤ y -> cfe f I F x ≤ cfe f I F y.
Proof.
  intros Hf HF x y; revert x.
  induction y as [Y h Hy]; intros [X g] Hxy.
  rewrite (cfe_unroll f I F (ord X g)).
  apply sup_least. intros [p|].
  - eapply ord_le_trans; [ | apply (cfe_ge_term f I F (ord Y h) (Some p)) ].
    simpl. apply fixOrd_monotone; [ apply c1_monotone_gen; auto | ].
    apply limit_least; intro i.
    destruct (ord_le_subord _ _ Hxy i) as [j Hj].
    apply ord_le_lt_trans with (cfe f I F (h j)); [ apply Hy; auto | ].
    rewrite ord_lt_unfold. exists j. reflexivity.
  - eapply ord_le_trans; [ | apply (cfe_ge_f f I F) ]. simpl. apply Hf; auto.
Qed.

Lemma cfe_mono_family f I J F F' :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall j x y, x ≤ y -> F' j x ≤ F' j y) ->
  (forall i, exists j, forall x, F i x ≤ F' j x) ->
  forall y, cfe f I F y ≤ cfe f J F' y.
Proof.
  intros Hf HF' Hfam y.
  induction y as [Y h Hy].
  rewrite (cfe_unroll f I F (ord Y h)).
  apply sup_least. intros [[i L]|].
  - destruct (Hfam i) as [j Hj].
    destruct (comps_mono_family f I J F F' HF' Hfam L) as [L' HL'].
    eapply ord_le_trans; [ | apply (cfe_ge_term f J F' (ord Y h) (Some (j, L'))) ].
    simpl.
    transitivity (fixOrd (c1 f J F' (j, L')) (limOrd (fun j0 => cfe f I F (ord Y h j0)))).
    + apply fixOrd_monotone_func; [ | apply c1_monotone_gen; auto ].
      intro x. unfold c1; simpl.
      transitivity (F' j (comps f I F L x)); auto.
    + apply fixOrd_monotone; [ apply c1_monotone_gen; auto | ].
      apply lim_le_mor; intro j0. apply Hy.
  - eapply ord_le_trans; [ | apply (cfe_ge_f f J F') ]. reflexivity.
Qed.

(** ** (B) A hierarchy that is normal by construction *)

Section bphi.
  Variable f : Ord -> Ord.

  Fixpoint bphi (T:BOrd) : Ord -> Ord :=
    match T with
    | bnode A g C h =>
      cfe f (A + C) (fun k => match k with
                               | inl a => bphi (g a)
                               | inr c => fun ξ => bphi (h c ξ) 0
                               end)
    end.

  Definition bphi_fam {A C:Type} (g:A -> BOrd) (h:C -> Ord -> BOrd) (k:(A + C)%type) : Ord -> Ord :=
    match k with
    | inl a => bphi (g a)
    | inr c => fun ξ => bphi (h c ξ) 0
    end.

  (** Every node decides (as a proposition) whether it has components;
      every Ω-family has a normal diagonal, and its members at positive
      complete arguments have components; members are required to be
      good at complete arguments. *)
  Fixpoint bgood (T:BOrd) : Prop :=
    match T with
    | bnode A g C h =>
      (forall a, bgood (g a)) /\
      (forall c ξ, complete ξ -> bgood (h c ξ)) /\
      (forall c, normal_function (fun ξ => bphi (h c ξ) 0)) /\
      (forall c ξ, complete ξ -> 0 < ξ -> inhabited (bsmall (h c ξ) + bbig (h c ξ))) /\
      (inhabited (A + C) \/ ~ inhabited (A + C))
    end.

  Hypothesis Hf : normal_function f.

  Lemma bphi_fam_normal A g C h :
    (forall a, normal_function (bphi (g a))) ->
    (forall c, normal_function (fun ξ => bphi (h c ξ) 0)) ->
    forall k, normal_function (@bphi_fam A C g h k).
  Proof. intros H1 H2 [a|c]; simpl; auto. Qed.

  Theorem bphi_normal : forall T, bgood T -> normal_function (bphi T).
  Proof.
    induction T as [A g Hg C h Hh]; simpl; intros [H1 [H2 [H3 [H5 H4]]]].
    apply (cfe_normal f Hf (A + C) (bphi_fam g h)); auto.
    apply bphi_fam_normal; auto.
  Qed.

  Lemma bphi_ge_f T y : f y ≤ bphi T y.
  Proof. destruct T as [A g C h]. apply (cfe_ge_f f (A + C)). Qed.

  Lemma bphi_fix_small A g C h a y :
    bgood (bnode A g C h) -> complete y ->
    bphi (g a) (bphi (bnode A g C h) y) ≤ bphi (bnode A g C h) y.
  Proof.
    intros HT Hy. assert (HT' := HT). destruct HT' as [H1 [H2 [H3 [H5 H4]]]].
    exact (cfe_fix_F f Hf (A + C) (bphi_fam g h)
             (bphi_fam_normal A g C h (fun a => bphi_normal _ (H1 a)) H3) (inl a) y Hy).
  Qed.

  Lemma bphi_fix_big A g C h c y :
    bgood (bnode A g C h) -> complete y ->
    bphi (h c (bphi (bnode A g C h) y)) 0 ≤ bphi (bnode A g C h) y.
  Proof.
    intros HT Hy. assert (HT' := HT). destruct HT' as [H1 [H2 [H3 [H5 H4]]]].
    exact (cfe_fix_F f Hf (A + C) (bphi_fam g h)
             (bphi_fam_normal A g C h (fun a => bphi_normal _ (H1 a)) H3) (inr c) y Hy).
  Qed.
End bphi.

(** ** Accessors for good trees *)

Section good0.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Let Hfm : forall x y, x ≤ y -> f x ≤ f y.
  Proof. apply normal_monotone; auto. Qed.

  Lemma bgood_small x a : bgood f x -> bgood f (bsmallSz x a).
  Proof. destruct x; simpl; intuition. Qed.

  Lemma bgood_big x c ξ : bgood f x -> complete ξ -> bgood f (bbigSz x c ξ).
  Proof. destruct x; simpl; intuition. Qed.

  Lemma bgood_diag x c : bgood f x -> normal_function (fun ξ => bphi f (bbigSz x c ξ) 0).
  Proof. destruct x; simpl; intuition. Qed.

  Lemma bgood_pos x c ξ : bgood f x -> complete ξ -> 0 < ξ ->
    inhabited (bsmall (bbigSz x c ξ) + bbig (bbigSz x c ξ)).
  Proof. destruct x; simpl; intuition. Qed.

  Lemma bphi_fam_normal' A g C h : bgood f (bnode A g C h) ->
    forall k, normal_function (bphi_fam f g h k).
  Proof.
    intros [H1 [H2 [H3 _]]]. apply bphi_fam_normal; auto.
    intro a. apply bphi_normal; auto.
  Qed.

  Lemma bphi_fix_small' T a y :
    bgood f T -> complete y -> bphi f (bsmallSz T a) (bphi f T y) ≤ bphi f T y.
  Proof. destruct T as [A g C h]. apply bphi_fix_small; auto. Qed.

  Lemma bphi_fix_big' T c y :
    bgood f T -> complete y -> bphi f (bbigSz T c (bphi f T y)) 0 ≤ bphi f T y.
  Proof. destruct T as [A g C h]. apply bphi_fix_big; auto. Qed.

  (** With a component, every value is a fixpoint of the base. *)
  Lemma bphi_fix_base' T y : bgood f T -> inhabited (bsmall T + bbig T) -> complete y ->
    f (bphi f T y) ≤ bphi f T y.
  Proof.
    destruct T as [A g C h]. intros HT [k] Hy.
    exact (cfe_fix_f f Hf (A + C) (bphi_fam f g h) (bphi_fam_normal' A g C h HT) k y Hy).
  Qed.

  Lemma bphi_nonzero T y : 0 < bphi f T y.
  Proof. destruct T as [A g C h]. apply (cfe_nonzero f Hf). Qed.

  Lemma bphi_complete T y : bgood f T -> complete y -> complete (bphi f T y).
  Proof. intros HT Hy. apply normal_complete; auto. apply bphi_normal; auto. Qed.
End good0.
