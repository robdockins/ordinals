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

(** * Normality of Bachmann's hierarchy, proved directly

In @BachmannCalibration@ the hierarchy is calibrated against known normal
functions (Veblen, Schütte's columns), which takes us as far as the
Large Veblen Ordinal.  Beyond that there is nothing to calibrate
against, so here we prove normality of φ directly.

The proof splits in two.

 (A) A generic construction, independent of index trees.  Given a base
     normal function f and a family of normal functions F_i, let E y
     be f y joined with the least fixpoints, above the previous
     values, of the nonempty compositions F_i ∘ F_{i_1} ∘ … ∘ F_{i_n}
     ∘ f.  The compositions form a directed family (any two are
     dominated by their concatenation), and every one of them
     dominates f, so the family of terms is directed without deciding
     whether there are any F_i.  With no F_i, E is f itself;
     otherwise E enumerates the common fixpoints of f and the F_i.
     Strict monotonicity of E does need that decision, but only as a
     proposition.

 (B) The Bachmann-specific content.  The hierarchy @bphi@ applies E
     at each node to the node's components; it is normal by
     construction on trees whose nodes decide whether they have
     components.  Bachmann's φ takes least fixpoints of the components
     one at a time, and agrees with @bphi@ when the components are
     suitably nested and directed.  We show, by structural conditions
     preserved by the tree arithmetic, that this holds on the
     canonical trees up to ε_{Ω+1}; in particular φ_{ε_{Ω+1}}(0) is
     the Bachmann–Howard ordinal.
*)

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

(** ** φ is monotone in the index, for @bsub@ *)

Theorem bphi_mono_index f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall y, bfam y ->
    (forall a b, a ≤ b -> bphi f y a ≤ bphi f y b) /\
    (forall x, bsub x y -> forall z, bphi f x z ≤ bphi f y z).
Proof.
  induction y as [B g' Hg D h' Hh]; intros [Hy1 [Hy2 Hy3]].
  assert (HFm : forall k x y, x ≤ y -> bphi_fam f g' h' k x ≤ bphi_fam f g' h' k y).
  { intros [b|d] x y Hxy; simpl.
    - apply (proj1 (Hg b (Hy1 b))); auto.
    - apply (proj2 (Hh d y (Hy2 d y))). apply Hy3; auto. }
  split.
  - change (forall a b, a ≤ b -> cfe f (B + D) (bphi_fam f g' h') a ≤ cfe f (B + D) (bphi_fam f g' h') b).
    apply cfe_monotone_gen; auto.
  - intros [A g C h] [Hs1 Hs2] z.
    change (cfe f (A + C) (bphi_fam f g h) z ≤ cfe f (B + D) (bphi_fam f g' h') z).
    apply cfe_mono_family; auto.
    intros [a|c].
    + destruct (Hs1 a) as [b Hb]. exists (inl b). intro x. simpl.
      apply (proj2 (Hg b (Hy1 b))); auto.
    + destruct (Hs2 c) as [d Hd]. exists (inr d). intro x. simpl.
      apply (proj2 (Hh d x (Hy2 d x))); auto.
Qed.


(** ** Strict increase along a family *)

(** x lies strictly below y if it lies below a small child of y, or
    (recursively) strictly below a small child of y or a member of one
    of y's Ω-families at a finite argument. *)
Inductive bslt : BOrd -> BOrd -> Prop :=
| bslt_small : forall x y b, bsub x (bsmallSz y b) -> bslt x y
| bslt_big : forall x y d n, bslt x (bbigSz y d (natOrdSize n)) -> bslt x y
| bslt_desc : forall x y b, bslt x (bsmallSz y b) -> bslt x y.

Lemma fix_onePlus_finite f (Hf : normal_function f) z :
  complete z -> f z ≤ z -> forall n, natOrdSize n ≤ z.
Proof.
  intros Hz Hfz n.
  induction n as [|n IH]; simpl; [ apply zero_least | ].
  apply succ_least.
  eapply ord_lt_le_trans; [ apply onePlus_finite | ].
  transitivity (1 + z); [ apply addOrd_monotone; auto; reflexivity | ].
  transitivity (f z); auto.
  apply onePlus_least_normal; auto.
Qed.


(** ** Structural conditions on Ω-families *)

Fixpoint bcanon (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (forall a, bcanon (g a)) /\
    (forall c ξ, bcanon (h c ξ)) /\
    (forall c ξ ξ', ξ ≤ ξ' -> bsub (h c ξ) (h c ξ')) /\
    (forall c ξ ξ', complete ξ' -> ξ < ξ' -> bslt (h c ξ) (h c ξ')) /\
    (forall c B (k:B -> Ord) (b0:B), directed B k -> (forall b, complete (k b)) ->
       bsub (h c (supOrd k)) (bsup (fun b => h c (k b))))
  end.


Lemma bcanon_bfam : forall T, bcanon T -> bfam T.
Proof.
  induction T as [A g Hg C h Hh]; intros [H1 [H2 [H3 _]]].
  simpl. split; [ intro a; apply Hg; auto | split; [ intros c ξ; apply Hh; auto | exact H3 ] ].
Qed.

(** ** First instances: ordinary ordinals and Ω *)

Lemma bcanon_embed : forall ξ, bcanon (embed ξ).
Proof.
  induction ξ as [X k Hk]; simpl.
  split; [ auto | repeat split; intros [] ].
Qed.

Lemma embed_small (x:Ord) (c:x) : exists q, bsmallSz (embed x) q = embed (x c).
Proof. destruct x. exists c. reflexivity. Qed.

Lemma bcanon_Ω : bcanon bOmega.
Proof.
  simpl. split; [ intros [] | split; [ intros _ ξ; apply bcanon_embed | split; [ | split ] ] ].
  - intros _ ξ ξ' H. apply bsub_embed; auto.
  - intros _ ξ [X' k'] _ H.
    rewrite ord_lt_unfold in H. destruct H as [j Hj].
    apply (bslt_small (embed ξ) (embed (ord X' k')) j).
    change (bsub (embed ξ) (embed (k' j))). apply bsub_embed; auto.
  - intros _ B k b0 _ _.
    apply bsub_intro.
    + intros [b c].
      destruct (embed_small (k b) c) as [q Hq].
      exists (existT _ b q).
      change (bsub (embed (k b c)) (bsmallSz (embed (k b)) q)).
      rewrite Hq. apply bsub_refl.
    + intros [].
Qed.


(** ** The arithmetic preserves @bcanon@ *)

Lemma bcanon_small x a : bcanon x -> bcanon (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bcanon_big x c ξ : bcanon x -> bcanon (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bcanon_fmono x c ξ ξ' : bcanon x -> ξ ≤ ξ' -> bsub (bbigSz x c ξ) (bbigSz x c ξ').
Proof. destruct x; simpl; intros [? [? [H ?]]]; auto. Qed.

Lemma bcanon_fstrict x c ξ ξ' : bcanon x -> complete ξ' -> ξ < ξ' ->
  bslt (bbigSz x c ξ) (bbigSz x c ξ').
Proof. destruct x; simpl; intros [? [? [? [H ?]]]]; auto. Qed.

Lemma bcanon_fcont x c B (k:B -> Ord) (b0:B) : bcanon x -> directed B k -> (forall b, complete (k b)) ->
  bsub (bbigSz x c (supOrd k)) (bsup (fun b => bbigSz x c (k b))).
Proof. destruct x; simpl; intros [? [? [? [? H]]]]; eauto. Qed.

Lemma bcanon_blub x y : bcanon x -> bcanon y -> bcanon (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [H1 [H2 [H3 [H4 H5]]]] [H1' [H2' [H3' [H4' H5']]]].
  repeat split.
  - intros [a|b]; auto.
  - intros [c|d] ξ; auto.
  - intros [c|d]; auto.
  - intros [c|d]; auto.
  - intros [c|d]; eauto.
Qed.

Lemma bcanon_bsup {I:Type} (F:I -> BOrd) : (forall i, bcanon (F i)) -> bcanon (bsup F).
Proof.
  intro H; simpl. repeat split.
  - intros [i a]. apply bcanon_small; auto.
  - intros [i c] ξ. apply bcanon_big; auto.
  - intros [i c] ξ ξ' Hξ. apply bcanon_fmono; auto.
  - intros [i c] ξ ξ' Hc Hξ. apply bcanon_fstrict; auto.
  - intros [i c] B k b0 Hdir Hk. apply (bcanon_fcont (F i) c B k b0); auto.
Qed.

Lemma bcanon_bzero : bcanon bzero.
Proof. simpl. repeat split; intros []. Qed.

Lemma bcanon_bsucc x : bcanon x -> bcanon (bsucc x).
Proof. intro H. simpl. split; [ auto | repeat split; intros [] ]. Qed.

(** *** @bsub@ and @bslt@ bookkeeping *)

Lemma bsub_bzero_l x : bsub bzero x.
Proof. apply bsub_intro; intros []. Qed.

Lemma bsub_le_badd w z : bsub w (badd w z).
Proof. rewrite (badd_eq w z). apply bsub_blub_l. Qed.

Lemma bsub_bsup_le {I:Type} (F:I -> BOrd) i : bsub (F i) (bsup F).
Proof.
  apply bsub_intro.
  - intro a. exists (existT _ i a). apply bsub_refl.
  - intro c. exists (existT _ i c). intro; apply bsub_refl.
Qed.

Lemma bslt_bsub_l a' a b : bsub a' a -> bslt a b -> bslt a' b.
Proof.
  intros H1 H2. induction H2 as [a b j Hj | a b d n H IH | a b j H IH].
  - apply (bslt_small _ _ j). eapply bsub_trans; eauto.
  - apply (bslt_big _ _ d n). auto.
  - apply (bslt_desc _ _ j). auto.
Qed.

Lemma bslt_bsub_r a b b' : bslt a b -> bsub b b' -> bslt a b'.
Proof.
  intro H. revert b'.
  induction H as [a b j Hj | a b d n H IH | a b j H IH]; intros b' Hb.
  - destruct (bsub_small _ _ Hb j) as [j' Hj'].
    apply (bslt_small _ _ j'). eapply bsub_trans; eauto.
  - destruct (bsub_big _ _ Hb d) as [d' Hd'].
    apply (bslt_big _ _ d' n). apply IH. apply Hd'.
  - destruct (bsub_small _ _ Hb j) as [j' Hj'].
    apply (bslt_desc _ _ j'). apply IH. exact Hj'.
Qed.

Definition bpos (z:BOrd) : Prop := bslt bzero z.

(** w lies strictly below w + z whenever z is strictly above something. *)
Lemma bslt_badd_pos w : forall x z, bslt x z -> bslt w (badd w z).
Proof.
  intros x z H.
  induction H as [x z j Hj | x z d n H IH | x z j H IH].
  - destruct (badd_small_r w z j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_le_badd.
  - destruct (badd_big_r w z d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (badd_small_r w z j) as [t Ht].
    apply (bslt_desc _ _ t). rewrite Ht. exact IH.
Qed.

Lemma bslt_badd_r x : forall a b, bslt a b -> bslt (badd x a) (badd x b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - destruct (badd_small_r x b j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_badd_r; auto.
  - destruct (badd_big_r x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (badd_small_r x b j) as [t Ht].
    apply (bslt_desc _ _ t). rewrite Ht. exact IH.
Qed.

Lemma bsub_badd_bsup x {B:Type} (H:B -> BOrd) (b0:B) :
  bsub (badd x (bsup H)) (bsup (fun b => badd x (H b))).
Proof.
  apply bsub_intro.
  - intro s.
    destruct (badd_small_cases x (bsup H) s) as [[a Ha]|[[b q] Hq]]; rewrite Ha || rewrite Hq.
    + destruct (badd_small_l x (H b0) a) as [t Ht].
      exists (existT _ b0 t). change (bsub (bsmallSz x a) (bsmallSz (badd x (H b0)) t)).
      rewrite Ht. apply bsub_refl.
    + destruct (badd_small_r x (H b) q) as [t Ht].
      exists (existT _ b t). change (bsub (badd x (bsmallSz (H b) q)) (bsmallSz (badd x (H b)) t)).
      rewrite Ht. apply bsub_refl.
  - intro c.
    destruct (badd_big_cases x (bsup H) c) as [[e He]|[[b q] Hq]].
    + destruct (badd_big_l x (H b0) e) as [t Ht].
      exists (existT _ b0 t). intro ξ. rewrite He.
      change (bsub (bbigSz x e ξ) (bbigSz (badd x (H b0)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (badd_big_r x (H b) q) as [t Ht].
      exists (existT _ b t). intro ξ. rewrite Hq.
      change (bsub (badd x (bbigSz (H b) q ξ)) (bbigSz (badd x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

Lemma bcanon_badd x y : bcanon x -> bcanon y -> bcanon (badd x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intro Hy.
  destruct Hy as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (badd_eq x (bnode B g D h)).
  apply bcanon_blub; auto.
  unfold baddR; simpl. repeat split.
  - intro b. apply Hg; auto.
  - intros d ξ. apply Hh; auto.
  - intros d ξ ξ' H. apply bsub_badd_r; auto.
  - intros d ξ ξ' Hc H. apply bslt_badd_r; auto.
  - intros d B' k b0 Hdir Hk.
    eapply bsub_trans; [ apply bsub_badd_r, (Hy5 d B' k b0); auto | ].
    apply bsub_badd_bsup; auto.
Qed.

(** *** Multiplication *)

Lemma bmul_small_r x y q s :
  exists t, bsmallSz (bmul x y) t = bsmallSz (badd (bmul x (bsmallSz y q)) x) s.
Proof. destruct y as [B g D h]. exists (inl (existT _ q s)). reflexivity. Qed.

Lemma bmul_big_r x y q c :
  exists t, forall ξ, bbigSz (bmul x y) t ξ = bbigSz (badd (bmul x (bsmallSz y q)) x) c ξ.
Proof. destruct y as [B g D h]. exists (inl (existT _ q c)). intro; reflexivity. Qed.

Lemma bmul_big_fam x y d :
  exists t, forall ξ, bbigSz (bmul x y) t ξ = bmul x (bbigSz y d ξ).
Proof. destruct y as [B g D h]. exists (inr d). intro; reflexivity. Qed.

Lemma bsub_bmul_bsup x {B:Type} (H:B -> BOrd) :
  bsub (bmul x (bsup H)) (bsup (fun b => bmul x (H b))).
Proof.
  apply bsub_intro.
  - intros [[[b q] s]|[]].
    destruct (bmul_small_r x (H b) q s) as [t Ht].
    exists (existT _ b t).
    change (bsub (bsmallSz (badd (bmul x (bsmallSz (H b) q)) x) s) (bsmallSz (bmul x (H b)) t)).
    rewrite Ht. apply bsub_refl.
  - intros [[[b q] c]|[b d]].
    + destruct (bmul_big_r x (H b) q c) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bbigSz (badd (bmul x (bsmallSz (H b) q)) x) c ξ) (bbigSz (bmul x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (bmul_big_fam x (H b) d) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bmul x (bbigSz (H b) d ξ)) (bbigSz (bmul x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

(** x·b_j + x ⊑ x·b, for any small child b_j of b. *)
Lemma bsub_bmul_step x b j : bsub (badd (bmul x (bsmallSz b j)) x) (bmul x b).
Proof.
  rewrite (bmul_eq x b).
  eapply bsub_trans; [ | apply bsub_blub_l ].
  apply (bsub_bsup_le (fun j => badd (bmul x (bsmallSz b j)) x) j).
Qed.

Lemma bslt_bmul_r x : bpos x -> forall a b, bslt a b -> bslt (bmul x a) (bmul x b).
Proof.
  intros Hx a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - eapply bslt_bsub_l; [ apply bsub_bmul_r, Hj | ].
    eapply bslt_bsub_r; [ | apply bsub_bmul_step ].
    apply (bslt_badd_pos _ bzero x Hx).
  - destruct (bmul_big_fam x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - eapply bslt_bsub_r; [ exact IH | ].
    eapply bsub_trans; [ apply bsub_le_badd | apply bsub_bmul_step ].
Qed.

Lemma bcanon_bmul x y : bcanon x -> bpos x -> bcanon y -> bcanon (bmul x y).
Proof.
  intros Hx Hpos.
  induction y as [B g Hg D h Hh]; intro Hy.
  assert (Hy' := Hy). destruct Hy' as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (bmul_eq x (bnode B g D h)).
  apply bcanon_blub.
  - unfold bmulS. apply bcanon_bsup. intro b.
    apply bcanon_badd; auto.
  - unfold bmulB; simpl. repeat split.
    + intros [].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bmul_r; auto.
    + intros d ξ ξ' Hc H. apply bslt_bmul_r; auto.
    + intros d B' k b0 Hdir Hk.
      eapply bsub_trans; [ apply bsub_bmul_r, (Hy5 d B' k b0); auto | ].
      apply bsub_bmul_bsup.
Qed.

Lemma bpos_Ω : bpos bOmega.
Proof.
  apply (bslt_big bzero bOmega tt 1).
  apply (bslt_small bzero (embed 1) tt).
  apply bsub_bzero_l.
Qed.

(** *** Exponentiation *)

Lemma bexpΩ_small_zero y : exists t, bsmallSz (bexpΩ y) t = bzero.
Proof. destruct y. exists (inl tt). reflexivity. Qed.

Lemma bpos_bexpΩ y : bpos (bexpΩ y).
Proof.
  destruct (bexpΩ_small_zero y) as [t Ht].
  apply (bslt_small _ _ t). rewrite Ht. apply bsub_refl.
Qed.

Lemma bexpΩ_big_s y q c :
  exists t, forall ξ, bbigSz (bexpΩ y) t ξ = bbigSz (bmul (bexpΩ (bsmallSz y q)) bOmega) c ξ.
Proof. destruct y. exists (inr (inl (existT _ q c))). intro; reflexivity. Qed.

Lemma bexpΩ_big_b y d : exists t, forall ξ, bbigSz (bexpΩ y) t ξ = bexpΩ (bbigSz y d ξ).
Proof. destruct y. exists (inr (inr d)). intro; reflexivity. Qed.

(** A positive P lies strictly below P·2. *)
Lemma bslt_two P : bpos P -> bslt P (bmul P (embed 2)).
Proof.
  intro HP.
  eapply bslt_bsub_l; [ apply (proj2 (bsub_bmul_one P)) | ].
  eapply bslt_bsub_r; [ | apply (bsub_bmul_step P (embed 2) tt) ].
  exact (bslt_badd_pos (bmul P (embed 1)) bzero P HP).
Qed.

Lemma bsub_P_P2 P : bsub P (bmul P (embed 2)).
Proof.
  eapply bsub_trans; [ apply (proj2 (bsub_bmul_one P)) | ].
  eapply bsub_trans; [ apply (bsub_le_badd (bmul P (embed 1)) P) | ].
  apply (bsub_bmul_step P (embed 2) tt).
Qed.

Lemma bslt_bexpΩ : forall a b, bslt a b -> bslt (bexpΩ a) (bexpΩ b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - eapply bslt_bsub_l; [ apply bsub_bexpΩ, Hj | ].
    destruct (bexpΩ_big_s b j (inr tt)) as [t Ht].
    apply (bslt_big _ _ t 2). rewrite Ht.
    change (bslt (bexpΩ (bsmallSz b j)) (bmul (bexpΩ (bsmallSz b j)) (embed 2))).
    apply bslt_two, bpos_bexpΩ.
  - destruct (bexpΩ_big_b b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (bexpΩ_big_s b j (inr tt)) as [t Ht].
    apply (bslt_big _ _ t 2). rewrite Ht.
    change (bslt (bexpΩ a) (bmul (bexpΩ (bsmallSz b j)) (embed 2))).
    eapply bslt_bsub_r; [ exact IH | apply bsub_P_P2 ].
Qed.

Lemma bsub_bexpΩ_bsup {B:Type} (H:B -> BOrd) (b0:B) :
  bsub (bexpΩ (bsup H)) (bsup (fun b => bexpΩ (H b))).
Proof.
  apply bsub_intro.
  - intros [[]|[[p [[[] _]|[]]]|[]]].
    destruct (bexpΩ_small_zero (H b0)) as [t Ht].
    exists (existT _ b0 t).
    change (bsub bzero (bsmallSz (bexpΩ (H b0)) t)).
    rewrite Ht. apply bsub_refl.
  - intros [[]|[[[b q] c]|[b d]]].
    + destruct (bexpΩ_big_s (H b) q c) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bbigSz (bmul (bexpΩ (bsmallSz (H b) q)) bOmega) c ξ) (bbigSz (bexpΩ (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (bexpΩ_big_b (H b) d) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bexpΩ (bbigSz (H b) d ξ)) (bbigSz (bexpΩ (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

Lemma bcanon_bexpΩ y : bcanon y -> bcanon (bexpΩ y).
Proof.
  induction y as [B g Hg D h Hh]; intro Hy.
  assert (Hy' := Hy). destruct Hy' as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (bexpΩ_eq (bnode B g D h)).
  apply bcanon_blub; [ apply bcanon_bsucc, bcanon_bzero | apply bcanon_blub ].
  - unfold bexpS. apply bcanon_bsup. intro b.
    apply bcanon_bmul; auto using bcanon_Ω, bpos_bexpΩ.
  - unfold bexpB; simpl. repeat split.
    + intros [].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bexpΩ; auto.
    + intros d ξ ξ' Hc H. apply bslt_bexpΩ; auto.
    + intros d B' k b0 Hdir Hk.
      eapply bsub_trans; [ apply bsub_bexpΩ, (Hy5 d B' k b0); auto | ].
      apply bsub_bexpΩ_bsup; auto.
Qed.

(** *** The tower and ε_{Ω+1} *)

Lemma bcanon_btower n : bcanon (btower n).
Proof.
  induction n.
  - change (bcanon (bsucc bOmega)). apply bcanon_bsucc, bcanon_Ω.
  - change (bcanon (bexpΩ (btower n))). apply bcanon_bexpΩ; auto.
Qed.

Lemma bcanon_bεΩ1 : bcanon bεΩ1.
Proof.
  simpl. split; [ apply bcanon_btower | repeat split; intros [] ].
Qed.

(** ** Deciding whether a node has components *)

(** Every node decides, as a proposition, whether it has any
    components; Ω-family members are required to do so only at complete
    arguments.  Ordinary trees cannot decide this constructively, but
    every tree the arithmetic builds from complete ordinals does.  The
    structural layer carries the decision so that it is available to
    hierarchy @bphi@, which needs it for strictness. *)
Fixpoint bdec (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (inhabited (A + C) \/ ~ inhabited (A + C)) /\
    (forall a, bdec (g a)) /\
    (forall c ξ, complete ξ -> bdec (h c ξ))
  end.

Lemma bdec_small x a : bdec x -> bdec (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bdec_big x c ξ : bdec x -> complete ξ -> bdec (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bdec_bzero : bdec bzero.
Proof. simpl. split; [ right; intros [[[]|[]]] | split; intros [] ]. Qed.

Lemma bdec_bsucc x : bdec x -> bdec (bsucc x).
Proof. intro H. simpl. split; [ left; exact (inhabits (inl tt)) | split; [ auto | intros [] ] ]. Qed.

Lemma bdec_blub x y : bdec x -> bdec y -> bdec (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [Dx [Hx1 Hx2]] [Dy [Hy1 Hy2]]. split; [ | split ].
  - destruct Dx as [[[a|c]]|Nx].
    + left. exact (inhabits (inl (inl a))).
    + left. exact (inhabits (inr (inl c))).
    + destruct Dy as [[[b|d]]|Ny].
      * left. exact (inhabits (inl (inr b))).
      * left. exact (inhabits (inr (inr d))).
      * right. intros [[[a|b]|[c|d]]];
          [ apply Nx; exact (inhabits (inl a)) | apply Ny; exact (inhabits (inl b))
          | apply Nx; exact (inhabits (inr c)) | apply Ny; exact (inhabits (inr d)) ].
  - intros [a|b]; auto.
  - intros [c|d] ξ Hξ; auto.
Qed.

Lemma bdec_blimΩ h : (forall ξ, complete ξ -> bdec (h ξ)) -> bdec (blimΩ h).
Proof. intro H. simpl. split; [ left; exact (inhabits (inr tt)) | split; [ intros [] | auto ] ]. Qed.

Lemma bdec_blimΩ_inv h : bdec (blimΩ h) -> forall ξ, complete ξ -> bdec (h ξ).
Proof. simpl. intros [_ [_ H]] ξ Hξ. apply (H tt); auto. Qed.

Lemma bdec_badd x y : bdec x -> bdec y -> bdec (badd x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  rewrite (badd_eq x (bnode B g D h)). apply bdec_blub; auto.
  simpl. split; [ exact Dy | split; [ intro b; apply Hg; auto | intros d ξ Hξ; apply Hh; auto ] ].
Qed.

Lemma bslt_inh x y : bslt x y -> inhabited (bsmall y + bbig y).
Proof. intros [x' y' b _ | x' y' d n _ | x' y' b _]; constructor; [ left | right | left ]; assumption. Qed.

Lemma bdec_bmul x y : inhabited (bsmall x + bbig x) -> bdec x -> bdec y -> bdec (bmul x y).
Proof.
  intros Hi Hx.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  simpl. split; [ | split ].
  - destruct Dy as [[[b|d]]|N].
    + left. destruct Hi as [[s|c]].
      * destruct (badd_small_r (bmul x (g b)) x s) as [t _].
        exact (inhabits (inl (inl (existT _ b t)))).
      * destruct (badd_big_r (bmul x (g b)) x c) as [t _].
        exact (inhabits (inr (inl (existT _ b t)))).
    + left. exact (inhabits (inr (inr d))).
    + right. intros [[[[b _]|[]]|[[b _]|d]]]; apply N; constructor; [ left | left | right ]; assumption.
  - intros [[b s]|[]].
    exact (bdec_small (badd (bmul x (g b)) x) s (bdec_badd _ _ (Hg b (Hy1 b)) Hx)).
  - intros [[b c]|d] ξ Hξ.
    + exact (bdec_big (badd (bmul x (g b)) x) c ξ (bdec_badd _ _ (Hg b (Hy1 b)) Hx) Hξ).
    + apply Hh; auto.
Qed.

Lemma bexpΩ_inh y : inhabited (bsmall (bexpΩ y) + bbig (bexpΩ y)).
Proof. destruct y. exact (inhabits (inl (inl tt))). Qed.

Lemma bdec_embed ξ : complete ξ -> bdec (embed ξ).
Proof.
  induction ξ as [X k Hk]; intros [_ [Hi Hc]]. simpl.
  split; [ | split; [ intro a; apply Hk; auto | intros [] ] ].
  destruct Hi as [[x]|N]; [ left; exact (inhabits (inl x)) | right; intros [[x|[]]]; apply N; exact (inhabits x) ].
Qed.

Lemma bdec_Ω : bdec bOmega.
Proof. apply bdec_blimΩ, bdec_embed. Qed.

Lemma bdec_bexpΩ y : bdec y -> bdec (bexpΩ y).
Proof.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  simpl. split; [ left; exact (inhabits (inl (inl tt))) | split ].
  - intros [[]|[[b s]|[]]]; [ apply bdec_bzero | ].
    exact (bdec_small (bmul (bexpΩ (g b)) bOmega) s
             (bdec_bmul _ _ (bexpΩ_inh _) (Hg b (Hy1 b)) bdec_Ω)).
  - intros [[]|[[b c]|d]] ξ Hξ.
    + exact (bdec_big (bmul (bexpΩ (g b)) bOmega) c ξ
               (bdec_bmul _ _ (bexpΩ_inh _) (Hg b (Hy1 b)) bdec_Ω) Hξ).
    + apply Hh; auto.
Qed.

Lemma bdec_btower n : bdec (btower n).
Proof.
  induction n; [ exact (bdec_bsucc _ bdec_Ω) | exact (bdec_bexpΩ _ IHn) ].
Qed.

Lemma bdec_bεΩ1 : bdec bεΩ1.
Proof. simpl. split; [ left; exact (inhabits (inl 0%nat)) | split; [ apply bdec_btower | intros [] ] ]. Qed.

(** Canonical and decided. *)
Definition bcd (T:BOrd) : Prop := bcanon T /\ bdec T.

Lemma bcd_small x a : bcd x -> bcd (bsmallSz x a).
Proof. intros [H1 H2]. split; [ apply bcanon_small | apply bdec_small ]; auto. Qed.

Lemma bcd_big x c ξ : bcd x -> complete ξ -> bcd (bbigSz x c ξ).
Proof. intros [H1 H2] Hξ. split; [ apply bcanon_big | apply bdec_big ]; auto. Qed.

Lemma bcd_badd x y : bcd x -> bcd y -> bcd (badd x y).
Proof. intros [H1 H2] [H3 H4]. split; [ apply bcanon_badd | apply bdec_badd ]; auto. Qed.

Lemma bcd_bmul x y : bcd x -> bpos x -> bcd y -> bcd (bmul x y).
Proof.
  intros [H1 H2] Hp [H3 H4]. split; [ apply bcanon_bmul | apply bdec_bmul ]; auto.
  exact (bslt_inh _ _ Hp).
Qed.

Lemma bcd_bexpΩ y : bcd y -> bcd (bexpΩ y).
Proof. intros [H1 H2]. split; [ apply bcanon_bexpΩ | apply bdec_bexpΩ ]; auto. Qed.

Lemma bcd_embed ξ : complete ξ -> bcd (embed ξ).
Proof. intro H. split; [ apply bcanon_embed | apply bdec_embed ]; auto. Qed.

Lemma bcd_Ω : bcd bOmega.
Proof. split; [ apply bcanon_Ω | apply bdec_Ω ]. Qed.

Lemma bcd_btower n : bcd (btower n).
Proof. split; [ apply bcanon_btower | apply bdec_btower ]. Qed.

Lemma bcd_bεΩ1 : bcd bεΩ1.
Proof. split; [ apply bcanon_bεΩ1 | apply bdec_bεΩ1 ]. Qed.


(** ** Strict increase along a family *)

Lemma bphi_child_lt f (Hf : normal_function f) y b :
  bgood f y -> bphi f (bsmallSz y b) 0 < bphi f y 0.
Proof.
  intros Hgood.
  eapply ord_lt_le_trans; [ | apply (bphi_fix_small' f Hf y b 0 Hgood zero_complete) ].
  apply normal_increasing.
  - apply bphi_normal; auto. apply bgood_small; auto.
  - apply bphi_complete; auto using zero_complete.
  - apply bphi_nonzero; auto.
Qed.

Theorem bphi_strict f (Hf : normal_function f) :
  forall x y, bslt x y -> bgood f y -> bfam y -> bphi f x 0 < bphi f y 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros x y H.
  induction H as [x y b Hb | x y d n H IH | x y b H IH]; intros Hgood Hfam.
  - apply ord_le_lt_trans with (bphi f (bsmallSz y b) 0).
    { apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ Hfam b))); auto. }
    apply bphi_child_lt; auto.
  - eapply ord_lt_le_trans; [ apply IH | ].
    + apply bgood_big; auto using natOrdSize_complete.
    + apply bfam_big; auto.
    + eapply ord_le_trans; [ | apply (bphi_fix_big' f Hf y d 0 Hgood zero_complete) ].
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hfam d _))).
      apply (bfam_fam _ Hfam d).
      apply (fix_onePlus_finite f Hf).
      * apply bphi_complete; auto using zero_complete.
      * apply (bphi_fix_base' f Hf y 0 Hgood (inhabits (inr d)) zero_complete).
  - eapply ord_lt_trans; [ apply IH | apply bphi_child_lt; auto ].
    + apply bgood_small; auto.
    + apply bfam_small; auto.
Qed.

(** ** Continuity of the diagonal *)

Lemma bsub_inh x y : bsub x y -> inhabited (bsmall x + bbig x) -> inhabited (bsmall y + bbig y).
Proof.
  intros H [[a|c]].
  - destruct (bsub_small _ _ H a) as [b _]. exact (inhabits (inl b)).
  - destruct (bsub_big _ _ H c) as [d _]. exact (inhabits (inr d)).
Qed.

Theorem bphi_diag_cont f (Hf : normal_function f) (h : Ord -> BOrd) :
  (forall ξ, complete ξ -> bgood f (h ξ)) -> (forall ξ, bfam (h ξ)) ->
  (forall ξ ξ', ξ ≤ ξ' -> bsub (h ξ) (h ξ')) ->
  (forall A (g:A -> Ord) (a0:A), directed A g -> (forall a, complete (g a)) ->
     bsub (h (supOrd g)) (bsup (fun a => h (g a)))) ->
  scott_continuous (fun ξ => bphi f (h ξ) 0).
Proof.
  intros Hgood Hfam Hmono Hcont A g a0 Hdir Hc.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (Hg : forall a, bgood f (h (g a))) by (intro a; apply Hgood; auto).
  assert (Hzc : forall a, complete (bphi f (h (g a)) 0)).
  { intro a. apply bphi_complete; auto using zero_complete. }
  assert (Hzmono : forall a b, g a ≤ g b -> bphi f (h (g a)) 0 ≤ bphi f (h (g b)) 0).
  { intros a b Hab. apply (proj2 (bphi_mono_index f Hfm _ (Hfam _))). apply Hmono; auto. }
  assert (Hzdir : directed A (fun a => bphi f (h (g a)) 0)).
  { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
    exists a'. split; apply Hzmono; auto. }
  set (z := supOrd (fun a => bphi f (h (g a)) 0)).
  (* if some member has a component, z is a fixpoint of f *)
  assert (Hfz : forall a, inhabited (bsmall (h (g a)) + bbig (h (g a))) -> f z ≤ z).
  { intros a Ha.
    eapply ord_le_trans; [ apply (normal_continuous f Hf A _ a0 Hzdir Hzc) | ].
    apply sup_least. intro b.
    destruct (Hdir a b) as [b' [Hab' Hbb']].
    eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
    transitivity (f (bphi f (h (g b')) 0)); [ apply Hfm; auto | ].
    apply bphi_fix_base'; auto using zero_complete.
    apply bsub_inh with (h (g a)); auto. }
  transitivity (bphi f (bsup (fun a => h (g a))) 0).
  { apply (proj2 (bphi_mono_index f Hfm _ (bfam_bsup _ (fun a => Hfam (g a))))).
    apply Hcont; auto. }
  assert (HFam : forall k, normal_function
             (bphi_fam f (fun p : sigT (fun a => bsmall (h (g a))) => bsmallSz (h (g (projT1 p))) (projT2 p))
                          (fun p : sigT (fun a => bbig (h (g a))) => bbigSz (h (g (projT1 p))) (projT2 p)) k)).
  { intros [[a s]|[a c]]; simpl.
    - apply bphi_normal; auto. apply bgood_small; auto.
    - apply bgood_diag; auto. }
  apply (cfe_least f Hf _ _ HFam).
  - transitivity (bphi f (h (g a0)) 0); [ apply bphi_ge_f | apply (sup_le _ (fun a => bphi f (h (g a)) 0) a0) ].
  - apply limit_least. intros [].
  - intros [[a s]|[a c]]; simpl; split.
    + assert (HG : normal_function (bphi f (bsmallSz (h (g a)) s))).
      { apply bphi_normal; auto. apply bgood_small; auto. }
      eapply ord_le_trans; [ apply (normal_continuous _ HG A _ a0 Hzdir Hzc) | ].
      apply sup_least. intro b.
      destruct (Hdir a b) as [b' [Hab' Hbb']].
      destruct (bsub_small _ _ (Hmono _ _ Hab') s) as [s' Hs'].
      eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
      transitivity (bphi f (bsmallSz (h (g a)) s) (bphi f (h (g b')) 0)).
      { apply normal_monotone; auto. }
      transitivity (bphi f (bsmallSz (h (g b')) s') (bphi f (h (g b')) 0)).
      { apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ (Hfam _) s'))); auto. }
      apply bphi_fix_small'; auto using zero_complete.
    + apply (Hfz a). exact (inhabits (inl s)).
    + assert (HD : normal_function (fun ξ => bphi f (bbigSz (h (g a)) c ξ) 0)).
      { apply bgood_diag; auto. }
      eapply ord_le_trans; [ apply (normal_continuous _ HD A _ a0 Hzdir Hzc) | ].
      apply sup_least. intro b.
      destruct (Hdir a b) as [b' [Hab' Hbb']].
      destruct (bsub_big _ _ (Hmono _ _ Hab') c) as [c' Hc'].
      eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
      transitivity (bphi f (bbigSz (h (g a)) c (bphi f (h (g b')) 0)) 0).
      { apply normal_monotone with (f := fun ξ => bphi f (bbigSz (h (g a)) c ξ) 0); auto. }
      transitivity (bphi f (bbigSz (h (g b')) c' (bphi f (h (g b')) 0)) 0).
      { apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ (Hfam _) c' _))); auto. }
      apply bphi_fix_big'; auto using zero_complete.
    + apply (Hfz a). exact (inhabits (inr c)).
Qed.

(** ** Canonical, decided trees are good *)

Theorem bcanon_good f (Hf : normal_function f) : forall T, bcanon T -> bdec T -> bfam T /\ bgood f T.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros T HT HD. split; [ apply (bcanon_bfam T HT) | ].
  revert HT HD.
  induction T as [A g Hg C h Hh]; intros HT [D1 [D2 D3]].
  assert (HT' := HT). destruct HT' as [H1 [H2 [H3 [H4 H5]]]].
  assert (HF : forall c ξ, bfam (h c ξ)) by (intros c ξ; apply bcanon_bfam; auto).
  assert (HG : forall c ξ, complete ξ -> bgood f (h c ξ)) by (intros c ξ Hξ; apply Hh; auto).
  simpl. split; [ intro a; apply Hg; auto | split; [ exact HG | split; [ | split; [ | exact D1 ] ] ] ].
  - intro c. constructor.
    + intros x y Hxy.
      apply (proj2 (bphi_mono_index f Hfm (h c y) (HF c y))). apply H3; auto.
    + intros x y Hy Hxy.
      apply bphi_strict; [ exact Hf | apply H4; auto | apply HG; auto | apply HF ].
    + apply bphi_diag_cont;
        [ exact Hf | intros; apply HG; auto | intro; apply HF | intros ξ ξ' H; apply H3; auto
        | intros B k b0 Hdir Hk; apply (H5 c B k b0); auto ].
    + intros x Hx. apply bphi_complete; auto using zero_complete.
    + intro x. apply bphi_nonzero; auto.
  - intros c ξ Hξ Hpos. apply (bslt_inh (h c 0)). apply H4; auto.
Qed.


(** ** Normality of the canonical hierarchy *)

Corollary bcanon_normal f (Hf : normal_function f) T : bcd T -> normal_function (bphi f T).
Proof. intros [H1 H2]. apply bphi_normal; auto. apply (bcanon_good f Hf T H1 H2). Qed.

Corollary bphi_Ω_normal f (Hf : normal_function f) : normal_function (bphi f bOmega).
Proof. apply bcanon_normal; auto using bcd_Ω. Qed.

(** φ_{ε_{Ω+1}} is a normal function. *)
Theorem bphi_εΩ1_normal f : normal_function f -> normal_function (bphi f bεΩ1).
Proof. intro Hf. apply bcanon_normal; auto using bcd_bεΩ1. Qed.

(** The Bachmann–Howard ordinal, defined via the provably normal
    hierarchy @bphi@. *)
Definition BachmannHoward : Ord := bphi powOmega bεΩ1 0.

Lemma BachmannHoward_complete : complete BachmannHoward.
Proof.
  unfold BachmannHoward.
  apply normal_complete; auto using zero_complete.
  apply bphi_εΩ1_normal, powOmega_normal.
Qed.

(** Every canonical tree Ω^ζ·ξ, and Ω^Ω, gives a normal function. *)
Corollary bphi_canonical_normal f : normal_function f ->
  forall ξ ζ, complete ξ -> complete ζ ->
    normal_function (bphi f (bmul (bexpΩ (embed ζ)) (embed ξ))) /\
    normal_function (bphi f (bexpΩ bOmega)).
Proof.
  intros Hf ξ ζ Hξ Hζ. split; apply bcanon_normal; auto.
  - apply bcd_bmul; auto using bcd_embed, bpos_bexpΩ, bcd_bexpΩ.
  - apply bcd_bexpΩ, bcd_Ω.
Qed.

(** ** Calibration of @bphi@ against the Veblen hierarchy

Below Ω, @bphi@ is the Veblen hierarchy: @bphi f (embed β) = veblen f
β@.  The children of the ordinal β are the β_i, matching the family
{φ_{β_i}} whose common fixpoints @cfe@ enumerates; when β = 0 both
sides are f.  At Ω, @bphi f bOmega@ enumerates the fixpoints of
ξ ↦ φ(ξ,0), i.e., Γ. *)

Theorem bphi_embed f (Hf : normal_function f) :
  forall β, complete β -> forall y, complete y -> bphi f (embed β) y ≈ veblen f β y.
Proof.
  induction β as [X k Hk]; intro Hβ.
  assert (Hβ' := Hβ). destruct Hβ' as [_ [_ Hkc]].
  assert (HV : normal_function (veblen f (ord X k))) by (apply veblen_normal; auto).
  assert (HE : normal_function (bphi f (embed (ord X k)))).
  { apply bcanon_normal; auto. apply bcd_embed; auto. }
  assert (HF : forall i, normal_function (bphi_fam f (fun a => embed (k a)) (False_rect (Ord -> BOrd)) i)).
  { intros [i|[]]. simpl. apply bcanon_normal; auto. apply bcd_embed; auto. }
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (HVc : complete (veblen f (ord X k) (ord Y h))) by (apply normal_complete; auto).
  assert (HEc : complete (bphi f (embed (ord X k)) (ord Y h))) by (apply normal_complete; auto).
  assert (Hstart : limOrd (fun j => bphi f (embed (ord X k)) (ord Y h j)) ≤ bphi f (embed (ord X k)) (ord Y h)).
  { apply limit_least; intro j. apply normal_increasing; auto. apply (index_lt (ord Y h) j). }
  split.
  - change (cfe f (X + False) (bphi_fam f (fun a => embed (k a)) (False_rect (Ord -> BOrd))) (ord Y h)
            ≤ veblen f (ord X k) (ord Y h)).
    apply (cfe_least f Hf _ _ HF).
    + rewrite (veblen_unroll f (ord X k) (ord Y h)). apply lub_le1.
    + apply limit_least; intro j.
      eapply ord_le_lt_trans; [ apply (proj1 (Hy j (Hhc j))) | ].
      apply normal_increasing; auto. apply (index_lt (ord Y h) j).
    + intros [i|[]]. simpl. split.
      * transitivity (veblen f (k i) (veblen f (ord X k) (ord Y h))).
        { apply (Hk i (Hkc i)); auto. }
        apply (proj1 (veblen_fixpoints f Hf (k i) (ord X k) (ord Y h)
                        (Hkc i) Hβ Hyc (index_lt (ord X k) i))).
      * transitivity (veblen f 0 (veblen f (ord X k) (ord Y h))).
        { apply (proj2 (veblen_zero f _)). }
        apply (proj1 (veblen_fixpoints f Hf 0 (ord X k) (ord Y h) zero_complete Hβ Hyc
                        (ord_le_lt_trans _ _ _ (zero_least (k i)) (index_lt (ord X k) i)))).
  - rewrite (veblen_unroll f (ord X k) (ord Y h)).
    apply lub_least; [ apply bphi_ge_f | ].
    apply sup_least. intro i.
    apply fixOrd_least; [ apply (veblen_monotone f (normal_monotone f Hf) (k i)) | | ].
    + apply limit_least; intro j.
      eapply ord_le_lt_trans; [ apply (proj2 (Hy j (Hhc j))) | ].
      eapply ord_lt_le_trans; [ | apply Hstart ].
      rewrite ord_lt_unfold. exists j. reflexivity.
    + transitivity (bphi f (embed (k i)) (bphi f (embed (ord X k)) (ord Y h))).
      { apply (Hk i (Hkc i)); auto. }
      apply (cfe_fix_F f Hf _ _ HF (inl i)); auto.
Qed.

Theorem bphi_Ω f (Hf : normal_function f) :
  forall y, complete y -> bphi f bOmega y ≈ enum_fixpoints (fun ξ => veblen f ξ 0) y.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HD' : normal_function (fun ξ => veblen f ξ 0)) by (apply veblen_first_normal; auto).
  assert (HG : normal_function (enum_fixpoints (fun ξ => veblen f ξ 0))) by (apply enum_fixpoints_normal; auto).
  assert (Hgood := proj2 (bcanon_good f Hf _ bcanon_Ω bdec_Ω)).
  assert (HF : forall i, normal_function (bphi_fam f (False_rect BOrd) (fun _ : unit => embed) i)).
  { intros [[]|[]]. simpl. exact (bgood_diag f bOmega tt Hgood). }
  assert (HE : normal_function (bphi f bOmega)) by (apply bphi_Ω_normal; auto).
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (HGc : complete (enum_fixpoints (fun ξ => veblen f ξ 0) (ord Y h))) by (apply normal_complete; auto).
  assert (HEc : complete (bphi f bOmega (ord Y h))) by (apply normal_complete; auto).
  assert (HGfix := enum_are_fixpoints _ HD' (ord Y h) Hyc).
  split.
  - change (cfe f (False + unit) (bphi_fam f (False_rect BOrd) (fun _ : unit => embed)) (ord Y h)
            ≤ enum_fixpoints (fun ξ => veblen f ξ 0) (ord Y h)).
    set (G := enum_fixpoints (fun ξ => veblen f ξ 0) (ord Y h)) in *.
    assert (HfG : f G ≤ G).
    { transitivity (veblen f 0 (veblen f G 0)).
      { rewrite veblen_zero; auto. apply Hfm. apply (proj1 HGfix). }
      transitivity (veblen f G 0); [ | apply (proj2 HGfix) ].
      apply (proj1 (veblen_fixpoints f Hf 0 G 0 zero_complete HGc zero_complete
                      (normal_nonzero _ HG _))). }
    apply (cfe_least f Hf _ _ HF).
    + transitivity (f G); auto. apply Hfm. apply (normal_inflationary _ HG _ Hyc).
    + apply limit_least; intro j.
      eapply ord_le_lt_trans; [ apply (proj1 (Hy j (Hhc j))) | ].
      apply normal_increasing; auto. apply (index_lt (ord Y h) j).
    + intros [[]|[]]. simpl. split; [ | exact HfG ].
      transitivity (veblen f G 0); [ | apply (proj2 HGfix) ].
      apply (proj1 (bphi_embed f Hf G HGc 0 zero_complete)).
  - change (fixOrd (fun ξ => veblen f ξ 0)
                   (limOrd (fun j => enum_fixpoints (fun ξ => veblen f ξ 0) (h j)))
            ≤ bphi f bOmega (ord Y h)).
    apply fixOrd_least; [ intros; apply veblen_monotone_first; auto | | ].
    + apply limit_least; intro j.
      eapply ord_le_lt_trans; [ apply (proj2 (Hy j (Hhc j))) | ].
      apply normal_increasing; auto. apply (index_lt (ord Y h) j).
    + transitivity (bphi f (embed (bphi f bOmega (ord Y h))) 0).
      { apply (proj2 (bphi_embed f Hf _ HEc 0 zero_complete)). }
      exact (cfe_fix_F f Hf _ _ HF (inr tt) (ord Y h) Hyc).
Qed.

Corollary bphi_Ω_Γ : forall y, complete y -> bphi powOmega bOmega y ≈ Γ y.
Proof. apply bphi_Ω, powOmega_normal. Qed.

(** ** Structural directedness

A component of a node is described either by a small child x or by an
Ω-family h; its semantics is φ_x, respectively ξ ↦ φ_{h ξ}(0).  We give
structural conditions (@D0@) under which one component dominates
another, close them under chaining through canonical intermediate
components (@Dstar@), and show this implies semantic domination. *)

Inductive bdesc : Type :=
| DSmall : BOrd -> bdesc
| DFam : (Ord -> BOrd) -> bdesc.


Definition dcan (d:bdesc) : Prop :=
  match d with
  | DSmall x => bcd x
  | DFam h => bcd (blimΩ h)
  end.

(** x lies (non-strictly) below a descendant of y reached through small
    children and family members at arguments at most z.  If z is a
    common fixpoint of y's components, then φ_x(0) ≤ z. *)
Inductive bleZ (z:Ord) : BOrd -> BOrd -> Prop :=
| LZ_sub : forall x y, bsub x y -> bleZ z x y
| LZ_small : forall x y b, bleZ z x (bsmallSz y b) -> bleZ z x y
| LZ_big : forall x y d ζ, ζ ≤ z -> bleZ z x (bbigSz y d ζ) -> bleZ z x y.

Lemma bleZ_mono_r z x y y' : bleZ z x y -> bsub y y' -> bleZ z x y'.
Proof.
  intro H. revert y'.
  induction H as [x y H | x y b H IH | x y d ζ Hζ H IH]; intros y' Hy.
  - apply LZ_sub. eapply bsub_trans; eauto.
  - destruct (bsub_small _ _ Hy b) as [b' Hb'].
    apply (LZ_small _ _ _ b'). apply IH; auto.
  - destruct (bsub_big _ _ Hy d) as [d' Hd'].
    apply (LZ_big _ _ _ d' ζ Hζ). apply IH; apply Hd'.
Qed.

Lemma bleZ_shift x z a b : bleZ z a b -> bleZ z (badd x a) (badd x b).
Proof.
  intro H.
  induction H as [a b H | a b j H IH | a b d ζ Hζ H IH].
  - apply LZ_sub, bsub_badd_r; auto.
  - destruct (badd_small_r x b j) as [t Ht].
    apply (LZ_small _ _ _ t). rewrite Ht. exact IH.
  - destruct (badd_big_r x b d) as [t Ht].
    apply (LZ_big _ _ _ t ζ Hζ). rewrite Ht. exact IH.
Qed.

Lemma bleZ_mul x z a b : bleZ z a b -> bleZ z (bmul x a) (bmul x b).
Proof.
  intro H.
  induction H as [a b H | a b j H IH | a b d ζ Hζ H IH].
  - apply LZ_sub, bsub_bmul_r; auto.
  - eapply bleZ_mono_r; [ exact IH | ].
    eapply bsub_trans; [ apply bsub_le_badd | apply bsub_bmul_step ].
  - destruct (bmul_big_fam x b d) as [t Ht].
    apply (LZ_big _ _ _ t ζ Hζ). rewrite Ht. exact IH.
Qed.

Inductive D0 : bdesc -> bdesc -> Prop :=
| D0_ss_sub : forall x y, bsub x y -> D0 (DSmall x) (DSmall y)
| D0_ss_lt : forall x y, bslt x y -> D0 (DSmall x) (DSmall y)
| D0_sf : forall x h n, bslt x (h (natOrdSize n)) -> D0 (DSmall x) (DFam h)
| D0_fs : forall h y e, (forall ξ, bsub (h ξ) (bbigSz y e ξ)) -> D0 (DFam h) (DSmall y)
| D0_ff_pt : forall h1 h3, (forall ξ, bsub (h1 ξ) (h3 ξ)) -> D0 (DFam h1) (DFam h3)
| D0_ff_in : forall h1 h3 n e,
    (forall ξ, bsub (h1 ξ) (bbigSz (h3 (natOrdSize n)) e ξ)) -> D0 (DFam h1) (DFam h3)
| D0_ffZ : forall h1 h3,
    (forall z, (forall n, natOrdSize n ≤ z) -> bleZ z (h1 z) (h3 z)) -> D0 (DFam h1) (DFam h3).

Inductive Dstar : bdesc -> bdesc -> Prop :=
| Drefl : forall d, Dstar d d
| Dstep : forall d1 d2 d3, dcan d2 -> D0 d1 d2 -> Dstar d2 d3 -> Dstar d1 d3.

Lemma Dstar_trans d1 d2 d3 : Dstar d1 d2 -> Dstar d2 d3 -> Dstar d1 d3.
Proof.
  intro H. induction H as [d | d1 d2 d4 Hc H0 H IH]; auto.
  intro H'. apply Dstep with d2; auto.
Qed.

Lemma D0_star d1 d2 : dcan d2 -> D0 d1 d2 -> Dstar d1 d2.
Proof. intros Hc H. apply Dstep with d2; auto using Drefl. Qed.


(** ** Nesting

Bachmann's hierarchy takes least fixpoints of a node's components one
at a time, and agrees with the common-fixpoint enumerator only if the
components are nested.  The basic nesting fact is that a tree strictly
below y (in the sense of @bslt@) has a φ that fixes every common
fixpoint of f and y's components.  For the family case the point is
that a fixpoint z of a normal diagonal is an exact value,
z = φ_{h z}(0), and hence fixed by the components of h z. *)

Definition bfix f (y:BOrd) (z:Ord) : Prop :=
  f z ≤ z /\
  (forall a, bphi f (bsmallSz y a) z ≤ z) /\
  (forall c, bphi f (bbigSz y c z) 0 ≤ z).

Section nest0.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Let Hfm : forall x y, x ≤ y -> f x ≤ f y.
  Proof. apply normal_monotone; auto. Qed.

  Lemma bfix_bsub a b z : bsub a b -> bfam b -> bfix f b z -> bfix f a z.
  Proof.
    intros H Hb [H1 [H2 H3]]. split; [ auto | split ].
    - intro i. destruct (bsub_small _ _ H i) as [j Hj].
      transitivity (bphi f (bsmallSz b j) z); auto.
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ Hb j))); auto.
    - intro c. destruct (bsub_big _ _ H c) as [d Hd].
      transitivity (bphi f (bbigSz b d z) 0); auto.
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hb d z))); auto.
  Qed.

  (** The components of x fix every value w' ≥ z of φ_x that is ≤ z. *)
  Lemma bfix_at x z w : bgood f x -> bfam x -> complete w -> complete z ->
    z ≤ bphi f x w -> bphi f x w ≤ z -> f z ≤ z -> bfix f x z.
  Proof.
    intros Hx Hxf Hw Hz H1 H2 Hfz. split; [ exact Hfz | split ].
    - intro a.
      transitivity (bphi f (bsmallSz x a) (bphi f x w)).
      { apply normal_monotone; auto. apply bphi_normal; auto. apply bgood_small; auto. }
      transitivity (bphi f x w); auto. apply bphi_fix_small'; auto.
    - intro c.
      transitivity (bphi f (bbigSz x c (bphi f x w)) 0).
      { apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hxf c _))). apply bfam_fam; auto. }
      transitivity (bphi f x w); auto. apply bphi_fix_big'; auto.
  Qed.

  (** A fixpoint of φ_x is a common fixpoint of f and x's components. *)
  Lemma bfix_of_fix x z : bgood f x -> bfam x -> complete z -> bphi f x z ≤ z -> bfix f x z.
  Proof.
    intros Hx Hxf Hz Hfix.
    apply (bfix_at x z z); auto.
    - apply normal_inflationary; auto. apply bphi_normal; auto.
    - transitivity (bphi f x z); auto. apply bphi_ge_f.
  Qed.

  (** A fixpoint z of a normal diagonal is the exact value φ_{h z}(0),
      and h z has a component (z is positive), so z is a fixpoint of f. *)
  Lemma bfix_member y d z : bgood f y -> bfam y -> complete z ->
    bphi f (bbigSz y d z) 0 ≤ z -> bfix f (bbigSz y d z) z.
  Proof.
    intros Hy Hyf Hz Hle.
    assert (HD := bgood_diag f y d Hy).
    assert (Hhz : bgood f (bbigSz y d z)) by (apply bgood_big; auto).
    assert (Hzw : z ≤ bphi f (bbigSz y d z) 0) by (apply (normal_inflationary _ HD z Hz)).
    assert (Hpos : 0 < z) by (exact (ord_lt_le_trans _ _ _ (bphi_nonzero f Hf _ 0) Hle)).
    apply (bfix_at _ z 0); auto using zero_complete, bfam_big.
    transitivity (f (bphi f (bbigSz y d z) 0)); [ apply Hfm; auto | ].
    transitivity (bphi f (bbigSz y d z) 0); auto.
    apply (bphi_fix_base' f Hf _ 0 Hhz (bgood_pos f y d z Hy Hz Hpos) zero_complete).
  Qed.

  Lemma bphi_le_fix y z : bgood f y -> complete z -> bfix f y z -> bphi f y 0 ≤ z.
  Proof.
    destruct y as [A g C h]. intros Hg Hz [H1 [H2 H3]].
    apply (cfe_least f Hf _ (bphi_fam f g h) (bphi_fam_normal' f Hf A g C h Hg) 0 z).
    - transitivity (f z); auto. apply Hfm, zero_least.
    - apply limit_least. intros [].
    - intros [a|c]; simpl; auto.
  Qed.

  Theorem bnest : forall x y, bslt x y -> bgood f y -> bfam y ->
    forall z, complete z -> bfix f y z -> bphi f x z ≤ z.
  Proof.
    intros x y H.
    induction H as [x y j Hj | x y d n H IH | x y j H IH]; intros Hgood Hfam z Hz Hfix.
    - transitivity (bphi f (bsmallSz y j) z).
      + apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ Hfam j))); auto.
      + apply Hfix.
    - assert (Hm : bfix f (bbigSz y d z) z) by (apply bfix_member; auto; apply Hfix).
      apply IH; auto using bfam_big.
      + apply bgood_big; auto using natOrdSize_complete.
      + apply bfix_bsub with (bbigSz y d z); auto using bfam_big.
        apply bfam_fam; auto.
        apply fix_onePlus_finite with f; auto. apply Hfix.
    - apply IH; auto using bgood_small, bfam_small.
      apply bfix_of_fix; auto using bgood_small, bfam_small.
      apply Hfix.
  Qed.

  (** Soundness of z-relative reachability, stated up to @bsub@ of the
      target so that family members are only visited at z itself. *)
  Lemma bleZ_sound z x y : bleZ z x y ->
    forall y', bsub y y' -> bgood f y' -> bfam y' -> complete z -> bfix f y' z -> bphi f x 0 ≤ z.
  Proof.
    intro H.
    induction H as [x y H | x y b H IH | x y d ζ Hζ H IH]; intros y' Hy Hg Hyf Hz Hfix.
    - transitivity (bphi f y' 0).
      + apply (proj2 (bphi_mono_index f Hfm y' Hyf)). eapply bsub_trans; eauto.
      + apply bphi_le_fix; auto.
    - destruct (bsub_small _ _ Hy b) as [b' Hb'].
      apply (IH (bsmallSz y' b')); auto using bgood_small, bfam_small.
      apply bfix_of_fix; auto using bgood_small, bfam_small. apply Hfix.
    - destruct (bsub_big _ _ Hy d) as [d' Hd'].
      apply (IH (bbigSz y' d' z)); auto using bfam_big.
      + eapply bsub_trans; [ apply Hd' | apply bfam_fam; auto ].
      + apply bgood_big; auto.
      + apply bfix_member; auto. apply Hfix.
  Qed.

  Lemma bleZ_nest z D y x : bleZ z D y -> bslt x D ->
    forall y', bsub y y' -> bgood f y' -> bfam y' -> complete z -> bfix f y' z -> bphi f x z ≤ z.
  Proof.
    intro H. revert x.
    induction H as [D y H | D y b H IH | D y d ζ Hζ H IH]; intros x Hx y' Hy Hg Hyf Hz Hfix.
    - apply (bnest x y'); auto. apply bslt_bsub_r with D; auto. eapply bsub_trans; eauto.
    - destruct (bsub_small _ _ Hy b) as [b' Hb'].
      apply (IH x Hx (bsmallSz y' b')); auto using bgood_small, bfam_small.
      apply bfix_of_fix; auto using bgood_small, bfam_small. apply Hfix.
    - destruct (bsub_big _ _ Hy d) as [d' Hd'].
      apply (IH x Hx (bbigSz y' d' z)); auto using bfam_big.
      + eapply bsub_trans; [ apply Hd' | apply bfam_fam; auto ].
      + apply bgood_big; auto.
      + apply bfix_member; auto. apply Hfix.
  Qed.
End nest0.

(** ** Agreement of @bach@ and φ under directed domination *)

Definition bdom f {A C:Type} (g:A -> BOrd) (h:C -> Ord -> BOrd) (k1 k3:(A + C)%type) : Prop :=
  forall z, complete z -> bphi_fam f g h k3 z ≤ z -> bphi_fam f g h k1 z ≤ z.

Fixpoint bdirH f (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (forall a, bdirH f (g a)) /\
    (forall c ξ, complete ξ -> bdirH f (h c ξ)) /\
    (forall k1 k2, exists k3, bdom f g h k1 k3 /\ bdom f g h k2 k3)
  end.

(** Every fixpoint of a component is a fixpoint of the base. *)
Lemma bphi_fam_fix_f f (Hf : normal_function f) A g C h k z :
  bgood f (bnode A g C h) -> complete z -> bphi_fam f g h k z ≤ z -> f z ≤ z.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros Hgood Hz Hk.
  destruct k as [a|c]; simpl in Hk.
  - transitivity (bphi f (g a) z); auto. apply bphi_ge_f.
  - assert (HD := bgood_diag f (bnode A g C h) c Hgood).
    assert (Hhz : bgood f (h c z)) by (apply (bgood_big f (bnode A g C h) c z); auto).
    assert (Hzw : z ≤ bphi f (h c z) 0) by (apply (normal_inflationary _ HD z Hz)).
    assert (Hpos : 0 < z) by (exact (ord_lt_le_trans _ _ _ (bphi_nonzero f Hf _ 0) Hk)).
    transitivity (f (bphi f (h c z) 0)); [ apply Hfm; auto | ].
    transitivity (bphi f (h c z) 0); auto.
    apply (bphi_fix_base' f Hf _ 0 Hhz (bgood_pos f (bnode A g C h) c z Hgood Hz Hpos) zero_complete).
Qed.

Theorem bach_bphi f (Hf : normal_function f) :
  forall T, bgood f T -> bfam T -> bdirH f T -> BRep f T (bphi f T).
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction T as [A g Hg C h Hh]; intros Hgood Hfam Hdir.
  assert (Hgood' := Hgood). destruct Hgood' as [Hg1 [Hg2 [Hg3 [Hg4 Hdec]]]].
  assert (Hfam' := Hfam). destruct Hfam' as [Hf1 [Hf2 Hf3]].
  destruct Hdir as [Hd1 [Hd2 Hd3]].
  assert (HIa : forall a, BRep f (g a) (bphi f (g a))) by (intro; apply Hg; auto).
  assert (HIc : forall c ξ, complete ξ -> BRep f (h c ξ) (bphi f (h c ξ))) by (intros; apply Hh; auto).
  assert (HT : normal_function (bphi f (bnode A g C h))) by (apply bphi_normal; auto).
  assert (HF := bphi_fam_normal' f Hf A g C h Hgood).
  assert (Hmono := bmono_bcomp f Hfm _ (bfam_bmono f Hfm _ Hfam)).
  assert (Hca : forall a x, complete x -> bach f (g a) x ≈ bphi f (g a) x).
  { intros a x Hx. apply (HIa a); auto. }
  assert (Hcc : forall c x, complete x -> bach f (h c x) 0 ≈ bphi f (h c x) 0).
  { intros c x Hx. apply (HIc c x Hx); auto using zero_complete. }
  assert (Hclb : forall kk y, complete y ->
             bcomp f (bnode A g C h) kk (bphi f (bnode A g C h) y) ≤ bphi f (bnode A g C h) y).
  { intros [a|c] y Hy;
      assert (Hv : complete (bphi f (bnode A g C h) y)) by (apply normal_complete; auto).
    - change (bach f (g a) (bphi f (bnode A g C h) y) ≤ bphi f (bnode A g C h) y).
      transitivity (bphi f (g a) (bphi f (bnode A g C h) y)); [ apply (proj1 (Hca a _ Hv)) | ].
      apply bphi_fix_small; auto.
    - change (bach f (h c (bphi f (bnode A g C h) y)) 0 ≤ bphi f (bnode A g C h) y).
      transitivity (bphi f (h c (bphi f (bnode A g C h) y)) 0); [ apply (proj1 (Hcc c _ Hv)) | ].
      apply bphi_fix_big; auto. }
  split; [ exact HT | split; [ | exact Hclb ] ].
  induction y as [Y k Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hkc]].
  assert (Hs : limOrd (fun j => bach f (bnode A g C h) (ord Y k j)) ≈
               limOrd (fun j => bphi f (bnode A g C h) (ord Y k j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => bphi f (bnode A g C h) (ord Y k j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp; [ apply bphi_ge_f | ].
    intro kk.
    apply fixOrd_least; [ apply Hmono | | apply Hclb; auto ].
    eapply ord_le_trans; [ apply (proj1 Hs) | ].
    apply limit_least; intro j.
    apply normal_increasing; auto. apply (index_lt (ord Y k) j).
  - change (cfe f (A + C) (bphi_fam f g h) (ord Y k) ≤ bach f (bnode A g C h) (ord Y k)).
    destruct Hdec as [[k0]|Hn].
    2:{ eapply ord_le_trans; [ | apply f_le_bach ].
        rewrite cfe_unroll. apply sup_least. intros [p|]; simpl.
        - elim Hn. exact (inhabits (fst p)).
        - reflexivity. }
    set (s' := limOrd (fun j => bphi f (bnode A g C h) (ord Y k j))) in *.
    set (w := fun kk => fixOrd (bphi_fam f g h kk) s').
    assert (Hwc : forall kk, complete (w kk)).
    { intro kk. unfold w. apply normal_fix_complete; auto.
      - apply normal_inflationary; auto.
      - apply normal_monotone; auto.
      - apply normal_complete; auto. }
    assert (Hwfix : forall kk, bphi_fam f g h kk (w kk) ≤ w kk).
    { intro kk. apply (proj2 (normal_fixpoint _ (HF kk) s' Hsc)). }
    assert (DN : forall kk z, complete z -> bphi_fam f g h kk z ≤ z -> f z ≤ z).
    { intros kk z Hz Hk. apply (bphi_fam_fix_f f Hf A g C h kk z); auto. }
    assert (Hwmono : forall k1 k3, bdom f g h k1 k3 -> w k1 ≤ w k3).
    { intros k1 k3 D.
      apply fixOrd_least; [ apply normal_monotone; auto | apply fixOrd_above | ].
      apply D; [ apply Hwc | apply Hwfix ]. }
    assert (Hwdir : directed (A + C) w).
    { intros k1 k2. destruct (Hd3 k1 k2) as [k3 [D1 D2]].
      exists k3. split; apply Hwmono; auto. }
    assert (HwZ : forall kk, w kk ≤ bach f (bnode A g C h) (ord Y k)).
    { intros [a|c]; unfold w; simpl.
      - eapply ord_le_trans;
          [ | apply (bach_comp_le f (bnode A g C h) (ord Y k) (inl a)) ].
        apply (proj2 (fixOrd_eq_func_complete
                        (bach f (g a)) (bphi f (g a)) _ _
                        (Hca a) (Hmono (inl a))
                        (normal_monotone _ (HF (inl a))) (normal_complete _ (HF (inl a))) Hs Hsc)).
      - eapply ord_le_trans;
          [ | apply (bach_comp_le f (bnode A g C h) (ord Y k) (inr c)) ].
        apply (proj2 (fixOrd_eq_func_complete
                        (fun ξ => bach f (h c ξ) 0) (fun ξ => bphi f (h c ξ) 0) _ _
                        (Hcc c) (Hmono (inr c))
                        (normal_monotone _ (HF (inr c))) (normal_complete _ (HF (inr c))) Hs Hsc)). }
    transitivity (supOrd w); [ | apply sup_least; exact HwZ ].
    apply (cfe_least f Hf _ _ HF).
    + eapply ord_le_trans; [ | apply (sup_le _ w k0) ].
      transitivity (f (w k0)); [ | apply (DN k0); auto ].
      apply Hfm. eapply ord_le_trans; [ | apply fixOrd_above ].
      unfold s'. apply lim_le_mor. intro j. apply normal_inflationary; auto.
    + apply limit_least; intro j.
      eapply ord_lt_le_trans; [ | apply (sup_le _ w k0) ].
      eapply ord_lt_le_trans; [ | apply fixOrd_above ].
      unfold s'. rewrite ord_lt_unfold. exists j. reflexivity.
    + intro kk. split.
      * eapply ord_le_trans; [ apply (normal_continuous _ (HF kk) _ w k0 Hwdir Hwc) | ].
        apply sup_least. intro o.
        destruct (Hd3 o kk) as [o3 [D1 D2]].
        eapply ord_le_trans; [ | apply (sup_le _ w o3) ].
        transitivity (bphi_fam f g h kk (w o3)).
        { apply normal_monotone; auto. }
        apply (D2 (w o3) (Hwc o3) (Hwfix o3)).
      * eapply ord_le_trans; [ apply (normal_continuous f Hf _ w k0 Hwdir Hwc) | ].
        apply sup_ord_le_morphism. intro o. apply (DN o); auto.
Qed.


(** ** Soundness of structural domination for φ *)

Definition dsem f (d:bdesc) : Ord -> Ord :=
  match d with
  | DSmall x => bphi f x
  | DFam h => fun ξ => bphi f (h ξ) 0
  end.

Definition semdom f (d1 d3:bdesc) : Prop :=
  forall z, complete z -> dsem f d3 z ≤ z -> dsem f d1 z ≤ z.

Section domination0.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Let Hfm : forall x y, x ≤ y -> f x ≤ f y.
  Proof. apply normal_monotone; auto. Qed.

  Lemma dcan_good x : bcd x -> bfam x /\ bgood f x.
  Proof. intros [H1 H2]. apply bcanon_good; auto. Qed.

  Lemma D0_sound d1 d3 : dcan d1 -> dcan d3 -> D0 d1 d3 -> semdom f d1 d3.
  Proof.
    intros _ Hc3 H.
    destruct H as [x y H | x y H | x h n H | h y e H | h1 h3 H | h1 h3 n e H | h1 h3 H];
      simpl in Hc3; simpl; intros z Hz Hle.
    - destruct (dcan_good y Hc3) as [Hyf Hyg].
      transitivity (bphi f y z); auto.
      apply (proj2 (bphi_mono_index f Hfm y Hyf)); auto.
    - destruct (dcan_good y Hc3) as [Hyf Hyg].
      apply (bnest f Hf x y H Hyg Hyf z Hz).
      apply bfix_of_fix; auto.
    - destruct (dcan_good _ Hc3) as [Hyf Hyg].
      assert (Hfix : bfix f (h z) z) by (apply (bfix_member f Hf (blimΩ h) tt z); auto).
      apply (bnest f Hf x (h z)).
      + apply bslt_bsub_r with (h (natOrdSize n)); auto.
        apply (bfam_fam _ Hyf tt). apply fix_onePlus_finite with f; auto. apply Hfix.
      + apply (bgood_big f (blimΩ h) tt z); auto.
      + apply (bfam_big _ Hyf tt).
      + exact Hz.
      + exact Hfix.
    - destruct (dcan_good y Hc3) as [Hyf Hyg].
      assert (Hfix := bfix_of_fix f Hf y z Hyg Hyf Hz Hle).
      transitivity (bphi f (bbigSz y e z) 0); [ | apply Hfix ].
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hyf e z))); auto.
    - destruct (dcan_good _ Hc3) as [Hyf Hyg].
      transitivity (bphi f (h3 z) 0); auto.
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hyf tt z))); auto.
    - destruct (dcan_good _ Hc3) as [Hyf Hyg].
      assert (Hfix : bfix f (h3 z) z) by (apply (bfix_member f Hf (blimΩ h3) tt z); auto).
      assert (Hn : natOrdSize n ≤ z) by (apply fix_onePlus_finite with f; auto; apply Hfix).
      assert (Hfix' : bfix f (h3 (natOrdSize n)) z).
      { apply (bfix_bsub f Hf) with (h3 z); [ apply (bfam_fam _ Hyf tt); auto | apply (bfam_big _ Hyf tt) | exact Hfix ]. }
      transitivity (bphi f (bbigSz (h3 (natOrdSize n)) e z) 0); [ | apply Hfix' ].
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ (bfam_big _ Hyf tt _) e z))); auto.
    - destruct (dcan_good _ Hc3) as [Hyf Hyg].
      assert (Hfix : bfix f (h3 z) z) by (apply (bfix_member f Hf (blimΩ h3) tt z); auto).
      apply (bleZ_sound f Hf z (h1 z) (h3 z)) with (h3 z); auto using bsub_refl.
      + apply H. intro n. apply fix_onePlus_finite with f; auto. apply Hfix.
      + apply (bgood_big f (blimΩ h3) tt z); auto.
      + apply (bfam_big _ Hyf tt).
  Qed.

  Lemma Dstar_sound d1 d3 : dcan d1 -> dcan d3 -> Dstar d1 d3 -> semdom f d1 d3.
  Proof.
    intros Hc1 Hc3 H. revert Hc1.
    induction H as [d | d1 d2 d4 Hc2 H0 H IH]; intro Hc1.
    - intros z Hz Hle; auto.
    - intros z Hz Hle.
      apply (D0_sound d1 d2 Hc1 Hc2 H0 z Hz).
      apply IH; auto.
  Qed.
End domination0.

Definition ndesc (N:BOrd) (k:(bsmall N + bbig N)%type) : bdesc :=
  match k with
  | inl a => DSmall (bsmallSz N a)
  | inr c => DFam (bbigSz N c)
  end.

Definition sdir (N:BOrd) : Prop :=
  forall k1 k2, exists k3, Dstar (ndesc N k1) (ndesc N k3) /\ Dstar (ndesc N k2) (ndesc N k3).

Fixpoint bsdirH (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (forall a, bsdirH (g a)) /\
    (forall c ξ, complete ξ -> bsdirH (h c ξ)) /\
    sdir (bnode A g C h)
  end.

Lemma dcan_ndesc N k : bcd N -> dcan (ndesc N k).
Proof.
  destruct N as [A g C h]. intro HN.
  destruct k as [a|c]; simpl.
  - apply (bcd_small (bnode A g C h) a HN).
  - destruct HN as [[H1 [H2 [H3 [H4 H5]]]] [_ [_ Hd]]]. split.
    + repeat split; [ intros [] | intros _; apply H2 | intros _; apply H3
                    | intros _; apply H4 | intros _; apply H5 ].
    + apply bdec_blimΩ. intros ξ Hξ. apply Hd; auto.
Qed.


(** ** Structural directedness gives semantic directedness for φ *)

Theorem bsdirH_bdirH f (Hf : normal_function f) : forall T, bcd T -> bsdirH T -> bdirH f T.
Proof.
  induction T as [A g Hg C h Hh]; intros HT [Hs1 [Hs2 Hs3]].
  split; [ intro a; apply Hg; auto; apply (bcd_small (bnode A g C h) a HT)
         | split; [ intros c ξ Hξ; apply Hh; auto; apply (bcd_big (bnode A g C h) c ξ HT Hξ) | ] ].
  intros k1 k2. destruct (Hs3 k1 k2) as [k3 [D1 D2]].
  assert (S1 := Dstar_sound f Hf _ _ (dcan_ndesc (bnode A g C h) k1 HT) (dcan_ndesc (bnode A g C h) k3 HT) D1).
  assert (S2 := Dstar_sound f Hf _ _ (dcan_ndesc (bnode A g C h) k2 HT) (dcan_ndesc (bnode A g C h) k3 HT) D2).
  exists k3. split; intros z Hz Hle.
  - destruct k1; destruct k3; apply S1; auto.
  - destruct k2; destruct k3; apply S2; auto.
Qed.

(** On canonical, decided, structurally directed trees, Bachmann's φ
    (one component at a time) represents @bphi@. *)
Corollary bach_bphi_canon f (Hf : normal_function f) T :
  bcd T -> bsdirH T -> BRep f T (bphi f T).
Proof.
  intros HT Hd.
  destruct (dcan_good f Hf T HT) as [Hfam Hgood].
  apply bach_bphi; auto. apply bsdirH_bdirH; auto.
Qed.


(** *** First instances *)

Lemma bsdirH_embed : forall ξ, complete ξ -> bsdirH (embed ξ).
Proof.
  induction ξ as [X k Hk]; intros [Hdir [_ Hkc]].
  simpl. split; [ intro a; apply Hk; auto | split; [ intros [] | ] ].
  intros [a1|[]] [a2|[]].
  destruct (Hdir a1 a2) as [a3 [H1 H2]].
  exists (inl a3). split; apply D0_star; simpl; auto using bcd_embed;
    apply D0_ss_sub, bsub_embed; auto.
Qed.

Lemma bsdirH_Ω : bsdirH bOmega.
Proof.
  simpl. split; [ intros [] | split; [ intros _ ξ Hξ; apply bsdirH_embed; auto | ] ].
  intros [[]|[]] [[]|[]]. exists (inr tt). split; apply Drefl.
Qed.

(** *** Addition *)

Definition dshift (x:BOrd) (d:bdesc) : bdesc :=
  match d with
  | DSmall t => DSmall (badd x t)
  | DFam h => DFam (fun ξ => badd x (h ξ))
  end.

Lemma D0_shift x d1 d2 : D0 d1 d2 -> D0 (dshift x d1) (dshift x d2).
Proof.
  intro H.
  destruct H as [t y H | t y H | t h n H | h y e H | h1 h3 H | h1 h3 n e H | h1 h3 H]; simpl.
  - apply D0_ss_sub, bsub_badd_r; auto.
  - apply D0_ss_lt, bslt_badd_r; auto.
  - apply (D0_sf _ _ n). apply bslt_badd_r; auto.
  - destruct (badd_big_r x y e) as [e' He'].
    apply (D0_fs _ _ e'). intro ξ. rewrite He'. apply bsub_badd_r; auto.
  - apply D0_ff_pt. intro ξ. apply bsub_badd_r; auto.
  - destruct (badd_big_r x (h3 (natOrdSize n)) e) as [e' He'].
    apply (D0_ff_in _ _ n e'). intro ξ.
    change (bsub (badd x (h1 ξ)) (bbigSz (badd x (h3 (natOrdSize n))) e' ξ)).
    rewrite He'. apply bsub_badd_r; auto.
  - apply D0_ffZ. intros z Hz. apply bleZ_shift; auto.
Qed.

Lemma dcan_shift x d : bcd x -> dcan d -> dcan (dshift x d).
Proof.
  intro Hx. destruct d as [t|h]; simpl.
  - intro Ht. apply bcd_badd; auto.
  - destruct Hx as [Hx Hxd].
    intros [[_ [H2 [H3 [H4 H5]]]] Hd]. split; [ repeat split | ].
    + intros [].
    + intros _ ξ. apply bcanon_badd; auto. apply (H2 tt).
    + intros _ ξ ξ' Hle. apply bsub_badd_r. apply (H3 tt); auto.
    + intros _ ξ ξ' Hc Hlt. apply bslt_badd_r. apply (H4 tt); auto.
    + intros _ B k b0 Hdir Hk.
      eapply bsub_trans; [ apply bsub_badd_r, (H5 tt B k b0); auto | ].
      apply bsub_badd_bsup; auto.
    + apply bdec_blimΩ. intros ξ Hξ. apply bdec_badd; auto. apply (bdec_blimΩ_inv h Hd); auto.
Qed.

Lemma Dstar_shift x d1 d2 : bcd x -> Dstar d1 d2 -> Dstar (dshift x d1) (dshift x d2).
Proof.
  intros Hx H.
  induction H as [d | d1 d2 d3 Hc H0 H IH].
  - apply Drefl.
  - apply Dstep with (dshift x d2); auto.
    + apply dcan_shift; auto.
    + apply D0_shift; auto.
Qed.

Lemma blub_desc_cases x z k :
  (exists kx, ndesc (blub x z) k = ndesc x kx) \/ (exists kz, ndesc (blub x z) k = ndesc z kz).
Proof.
  destruct x as [A g C h]; destruct z as [B g' D h'].
  destruct k as [[a|b]|[c|d]];
    [ left; exists (inl a) | right; exists (inl b) | left; exists (inr c) | right; exists (inr d) ];
    reflexivity.
Qed.

Lemma blub_desc_l x z kx : exists k, ndesc (blub x z) k = ndesc x kx.
Proof.
  destruct x as [A g C h]; destruct z as [B g' D h'].
  destruct kx as [a|c]; [ exists (inl (inl a)) | exists (inr (inl c)) ]; reflexivity.
Qed.

Lemma blub_desc_r x z kz : exists k, ndesc (blub x z) k = ndesc z kz.
Proof.
  destruct x as [A g C h]; destruct z as [B g' D h'].
  destruct kz as [b|d]; [ exists (inl (inr b)) | exists (inr (inr d)) ]; reflexivity.
Qed.

(** A merge is directed if both parts are, and every component of the
    left part is dominated by every component of the right part. *)
Lemma sdir_blub x z : sdir x -> sdir z ->
  (forall kx kz, Dstar (ndesc x kx) (ndesc z kz)) -> sdir (blub x z).
Proof.
  intros Hx Hz Hcross k1 k2.
  destruct (blub_desc_cases x z k1) as [[x1 E1]|[z1 E1]];
    destruct (blub_desc_cases x z k2) as [[x2 E2]|[z2 E2]]; rewrite E1, E2.
  - destruct (Hx x1 x2) as [x3 [H1 H2]].
    destruct (blub_desc_l x z x3) as [k3 E3]. exists k3. rewrite E3. auto.
  - destruct (blub_desc_r x z z2) as [k3 E3]. exists k3. rewrite E3. split; auto using Drefl.
  - destruct (blub_desc_r x z z1) as [k3 E3]. exists k3. rewrite E3. split; auto using Drefl.
  - destruct (Hz z1 z2) as [z3 [H1 H2]].
    destruct (blub_desc_r x z z3) as [k3 E3]. exists k3. rewrite E3. auto.
Qed.

Lemma bsdirH_blub x z : bsdirH x -> bsdirH z -> sdir (blub x z) -> bsdirH (blub x z).
Proof.
  destruct x as [A g C h]; destruct z as [B g' D h'].
  intros [Hx1 [Hx2 _]] [Hz1 [Hz2 _]] Hs.
  split; [ intros [a|b]; auto | split; [ intros [c|d] ξ Hξ; auto | exact Hs ] ].
Qed.

Lemma sdir_baddR x y : bcd x -> sdir y -> sdir (baddR x y).
Proof.
  intros Hx Hy k1 k2.
  destruct (Hy k1 k2) as [k3 [H1 H2]].
  exists k3. split.
  - destruct k1; destruct k3; exact (Dstar_shift x _ _ Hx H1).
  - destruct k2; destruct k3; exact (Dstar_shift x _ _ Hx H2).
Qed.

Lemma badd_cross x y kx kz : bcd x -> bcd y -> Dstar (ndesc x kx) (ndesc (baddR x y) kz).
Proof.
  intros Hx Hy.
  apply D0_star.
  - destruct kz as [b|d].
    + exact (dcan_shift x (ndesc y (inl b)) Hx (dcan_ndesc y (inl b) Hy)).
    + exact (dcan_shift x (ndesc y (inr d)) Hx (dcan_ndesc y (inr d) Hy)).
  - destruct x as [A g C h]; destruct y as [B g' D h'].
    destruct kx as [a|c]; destruct kz as [b|d]; simpl.
    + apply D0_ss_lt. eapply bslt_bsub_r;
        [ apply (bslt_small (g a) (bnode A g C h) a (bsub_refl _)) | apply bsub_le_badd ].
    + apply (D0_sf _ _ 0). eapply bslt_bsub_r;
        [ apply (bslt_small (g a) (bnode A g C h) a (bsub_refl _)) | apply bsub_le_badd ].
    + destruct (badd_big_l (bnode A g C h) (g' b) c) as [e He].
      apply (D0_fs _ _ e). intro ξ. rewrite He. apply bsub_refl.
    + destruct (badd_big_l (bnode A g C h) (h' d (natOrdSize 0)) c) as [e He].
      apply (D0_ff_in _ _ 0 e). intro ξ.
      change (bsub (h c ξ) (bbigSz (badd (bnode A g C h) (h' d (natOrdSize 0))) e ξ)).
      rewrite He. apply bsub_refl.
Qed.

Theorem bsdirH_badd x y : bcd x -> bsdirH x -> bcd y -> bsdirH y -> bsdirH (badd x y).
Proof.
  intros Hxc Hxd.
  induction y as [B g' Hg' D h' Hh']; intros Hyc Hyd.
  assert (Hyd' := Hyd). destruct Hyd' as [Hy1 [Hy2 Hy3]].
  rewrite (badd_eq x (bnode B g' D h')).
  assert (HR : bsdirH (baddR x (bnode B g' D h'))).
  { split; [ intro b; apply Hg'; auto; apply (bcd_small (bnode B g' D h') b Hyc)
           | split; [ intros d ξ Hξ; apply Hh'; auto; apply (bcd_big (bnode B g' D h') d ξ Hyc Hξ) | ] ].
    apply sdir_baddR; auto. }
  apply bsdirH_blub; auto.
  apply sdir_blub.
  - destruct x as [A g C h]. apply Hxd.
  - apply sdir_baddR; auto.
  - intros kx kz. apply badd_cross; auto.
Qed.

(** *** Covering *)

(** Every component of T is dominated by some component of U. *)
Definition Cov (T U:BOrd) : Prop := forall k, exists k', Dstar (ndesc T k) (ndesc U k').

Lemma cov_trans T U V : Cov T U -> Cov U V -> Cov T V.
Proof.
  intros H1 H2 k. destruct (H1 k) as [k' H']. destruct (H2 k') as [k'' H''].
  exists k''. eapply Dstar_trans; eauto.
Qed.

Lemma cov_bsub T U : bsub T U -> bcd U -> Cov T U.
Proof.
  intros H HU [a|c].
  - destruct (bsub_small _ _ H a) as [a' Ha'].
    exists (inl a'). apply D0_star; [ apply (dcan_ndesc U (inl a') HU) | apply D0_ss_sub; auto ].
  - destruct (bsub_big _ _ H c) as [c' Hc'].
    exists (inr c'). apply D0_star; [ apply (dcan_ndesc U (inr c') HU) | apply D0_ff_pt; auto ].
Qed.

(** The components of a small child are dominated by the child itself. *)
Lemma cov_small_child U j : bcd U ->
  forall k, Dstar (ndesc (bsmallSz U j) k) (ndesc U (inl j)).
Proof.
  intros HU [a|c]; apply D0_star; try apply (dcan_ndesc U (inl j) HU); simpl.
  - apply D0_ss_lt. apply (bslt_small _ _ a). apply bsub_refl.
  - apply (D0_fs _ _ c). intro ξ. apply bsub_refl.
Qed.

(** The components of a family member are dominated by the family. *)
Lemma cov_member F n : dcan (DFam F) ->
  forall k, Dstar (ndesc (F (natOrdSize n)) k) (DFam F).
Proof.
  intros HF [a|c]; apply D0_star; auto; simpl.
  - apply (D0_sf _ _ n). apply (bslt_small _ _ a). apply bsub_refl.
  - apply (D0_ff_in _ _ n c). intro ξ. apply bsub_refl.
Qed.

Lemma cov_member_eq U t n V : bcd U -> bbigSz U t (natOrdSize n) = V -> Cov V U.
Proof.
  intros HU E. subst V. intro k. exists (inr t).
  apply (cov_member (bbigSz U t) n (dcan_ndesc U (inr t) HU)).
Qed.

Lemma cov_bmul_step x t u : bcd x -> bpos x -> bcd u -> bslt t u ->
  Cov (badd (bmul x t) x) (bmul x u).
Proof.
  intros Hx Hpos Hu H. revert Hu.
  induction H as [t u j Hj | t u d n H IH | t u j H IH]; intros Hu.
  - apply cov_bsub; [ | apply bcd_bmul; auto ].
    eapply bsub_trans; [ apply bsub_badd_l, bsub_bmul_r, Hj | apply bsub_bmul_step ].
  - destruct (bmul_big_fam x u d) as [t' Ht'].
    assert (Hmc : bcd (bmul x u)) by (apply bcd_bmul; auto).
    eapply cov_trans; [ apply IH; apply bcd_big; auto using natOrdSize_complete | ].
    apply (cov_member_eq (bmul x u) t' n); auto.
  - eapply cov_trans; [ apply IH; apply bcd_small; auto | ].
    apply cov_bsub; [ | apply bcd_bmul; auto ].
    eapply bsub_trans; [ apply bsub_le_badd | apply bsub_bmul_step ].
Qed.

(** *** Multiplication *)

Lemma bsdirH_sdir T : bsdirH T -> sdir T.
Proof. destruct T; simpl; tauto. Qed.

Lemma bsdirH_small T a : bsdirH T -> bsdirH (bsmallSz T a).
Proof. destruct T; simpl; intuition. Qed.

Lemma bsdirH_big T c ξ : bsdirH T -> complete ξ -> bsdirH (bbigSz T c ξ).
Proof. destruct T; simpl; intuition. Qed.

Lemma dcan_mul x h : bcd x -> bpos x -> dcan (DFam h) -> dcan (DFam (fun ξ => bmul x (h ξ))).
Proof.
  intros [Hx Hxd] Hp [Hc Hd]. split; [ destruct Hc as [_ [H2 [H3 [H4 H5]]]]; repeat split | ].
  - intros [].
  - intros _ ξ. apply bcanon_bmul; auto. apply (H2 tt).
  - intros _ ξ ξ' Hle. apply bsub_bmul_r. apply (H3 tt); auto.
  - intros _ ξ ξ' Hc Hlt. apply bslt_bmul_r; auto. apply (H4 tt); auto.
  - intros _ B k b0 Hdir Hk.
    eapply bsub_trans; [ apply bsub_bmul_r, (H5 tt B k b0); auto | apply bsub_bmul_bsup ].
  - apply bdec_blimΩ. intros ξ Hξ. apply bdec_bmul; auto.
    + exact (bslt_inh _ _ Hp).
    + apply (bdec_blimΩ_inv h Hd); auto.
Qed.

(** The components of x·y contributed by a component of y: all the
    components of x·t + x for a small child t, or the single family
    ξ ↦ x·h ξ for a family h. *)
Definition mimg (x:BOrd) (d c:bdesc) : Prop :=
  match d with
  | DSmall t => exists k, c = ndesc (badd (bmul x t) x) k
  | DFam h => c = DFam (fun ξ => bmul x (h ξ))
  end.

Lemma mimg_D0 x d1 d3 : bcd x -> bpos x -> dcan d1 -> dcan d3 -> D0 d1 d3 ->
  forall c, mimg x d1 c -> exists c', mimg x d3 c' /\ Dstar c c'.
Proof.
  intros Hx Hp Hc1 Hc3 H.
  destruct H as [t u H | t u H | t h n H | h u e H | h1 h3 H | h1 h3 n e H | h1 h3 H];
    simpl in *; intros c Hc.
  - destruct Hc as [k ->].
    destruct (cov_bsub (badd (bmul x t) x) (badd (bmul x u) x)
                (bsub_badd_l _ _ (bsub_bmul_r x t u H) x)
                (bcd_badd _ _ (bcd_bmul x u Hx Hp Hc3) Hx) k) as [k' Hk'].
    exists (ndesc (badd (bmul x u) x) k'). split; [ exists k'; reflexivity | exact Hk' ].
  - destruct Hc as [k ->].
    assert (Hcov : Cov (badd (bmul x t) x) (badd (bmul x u) x)).
    { eapply cov_trans; [ apply (cov_bmul_step x t u Hx Hp Hc3 H) | ].
      apply cov_bsub; [ apply bsub_le_badd | apply bcd_badd; auto; apply bcd_bmul; auto ]. }
    destruct (Hcov k) as [k' Hk'].
    exists (ndesc (badd (bmul x u) x) k'). split; [ exists k'; reflexivity | exact Hk' ].
  - destruct Hc as [k ->].
    assert (Hhn : bcd (h (natOrdSize n))).
    { exact (bcd_big (blimΩ h) tt (natOrdSize n) Hc3 (natOrdSize_complete n)). }
    destruct (cov_bmul_step x t (h (natOrdSize n)) Hx Hp Hhn H k) as [k'' Hk''].
    exists (DFam (fun ξ => bmul x (h ξ))). split; [ reflexivity | ].
    eapply Dstar_trans; [ exact Hk'' | ].
    apply (cov_member (fun ξ => bmul x (h ξ)) n (dcan_mul x h Hx Hp Hc3)).
  - subst c.
    destruct (bmul_big_fam x u e) as [t' Ht'].
    destruct (badd_big_l (bmul x u) x t') as [e'' He''].
    exists (ndesc (badd (bmul x u) x) (inr e'')). split; [ exists (inr e''); reflexivity | ].
    apply D0_star.
    + apply dcan_ndesc. apply bcd_badd; auto. apply bcd_bmul; auto.
    + simpl. apply D0_ff_pt. intro ξ. rewrite He'', Ht'. apply bsub_bmul_r; auto.
  - subst c. exists (DFam (fun ξ => bmul x (h3 ξ))). split; [ reflexivity | ].
    apply D0_star; [ apply dcan_mul; auto | ].
    apply D0_ff_pt. intro ξ. apply bsub_bmul_r; auto.
  - subst c. exists (DFam (fun ξ => bmul x (h3 ξ))). split; [ reflexivity | ].
    apply D0_star; [ apply dcan_mul; auto | ].
    destruct (bmul_big_fam x (h3 (natOrdSize n)) e) as [e' He'].
    apply (D0_ff_in _ _ n e'). intro ξ.
    change (bsub (bmul x (h1 ξ)) (bbigSz (bmul x (h3 (natOrdSize n))) e' ξ)).
    rewrite He'. apply bsub_bmul_r; auto.
  - subst c. exists (DFam (fun ξ => bmul x (h3 ξ))). split; [ reflexivity | ].
    apply D0_star; [ apply dcan_mul; auto | ].
    apply D0_ffZ. intros z Hz. apply bleZ_mul; auto.
Qed.

Lemma mimg_Dstar x d1 d3 : bcd x -> bpos x -> dcan d1 -> dcan d3 -> Dstar d1 d3 ->
  forall c, mimg x d1 c -> exists c', mimg x d3 c' /\ Dstar c c'.
Proof.
  intros Hx Hp Hc1 Hc3 H. revert Hc1.
  induction H as [d | d1 d2 d4 Hc2 H0 H IH]; intros Hc1 c Hc.
  - exists c. split; auto using Drefl.
  - destruct (mimg_D0 x d1 d2 Hx Hp Hc1 Hc2 H0 c Hc) as [c' [Hc' E']].
    destruct (IH Hc3 Hc2 c' Hc') as [c'' [Hc'' E'']].
    exists c''. split; auto. eapply Dstar_trans; eauto.
Qed.

Lemma bmul_desc_cases x y k : exists yk, mimg x (ndesc y yk) (ndesc (bmul x y) k).
Proof.
  destruct y as [B g' D h'].
  destruct k as [[[b s]|[]]|[[b c]|d]].
  - exists (inl b). simpl. exists (inl s). reflexivity.
  - exists (inl b). simpl. exists (inr c). reflexivity.
  - exists (inr d). reflexivity.
Qed.

Lemma bmul_desc_back x y yk c : mimg x (ndesc y yk) c -> exists k, ndesc (bmul x y) k = c.
Proof.
  destruct y as [B g' D h']. destruct yk as [b|d]; simpl; intro Hc.
  - destruct Hc as [[s|c'] ->].
    + exists (inl (inl (existT _ b s))). reflexivity.
    + exists (inr (inl (existT _ b c'))). reflexivity.
  - subst c. exists (inr (inr d)). reflexivity.
Qed.

Lemma sdir_bmul x y : bcd x -> bpos x -> bcd y -> sdir y ->
  (forall b, sdir (badd (bmul x (bsmallSz y b)) x)) -> sdir (bmul x y).
Proof.
  intros Hx Hp Hyc Hy Hpieces k1 k2.
  destruct (bmul_desc_cases x y k1) as [y1 M1].
  destruct (bmul_desc_cases x y k2) as [y2 M2].
  destruct (Hy y1 y2) as [y3 [D1 D2]].
  destruct (mimg_Dstar x _ _ Hx Hp (dcan_ndesc y y1 Hyc) (dcan_ndesc y y3 Hyc) D1 _ M1) as [c1 [M1' E1]].
  destruct (mimg_Dstar x _ _ Hx Hp (dcan_ndesc y y2 Hyc) (dcan_ndesc y y3 Hyc) D2 _ M2) as [c2 [M2' E2]].
  assert (Hc3 : exists c3, mimg x (ndesc y y3) c3 /\ Dstar c1 c3 /\ Dstar c2 c3).
  { destruct y3 as [b3|d3]; simpl in M1', M2' |- *.
    - destruct M1' as [s1 ->]. destruct M2' as [s2 ->].
      destruct (Hpieces b3 s1 s2) as [s3 [F1 F2]].
      exists (ndesc (badd (bmul x (bsmallSz y b3)) x) s3). split; [ exists s3; reflexivity | auto ].
    - subst c1 c2. exists (DFam (fun ξ => bmul x (bbigSz y d3 ξ))). split; auto using Drefl. }
  destruct Hc3 as [c3 [M3 [F1 F2]]].
  destruct (bmul_desc_back x y y3 c3 M3) as [k3 E3].
  exists k3. rewrite E3. split; eapply Dstar_trans; eauto.
Qed.

Theorem bsdirH_bmul x y : bcd x -> bpos x -> bsdirH x -> bcd y -> bsdirH y -> bsdirH (bmul x y).
Proof.
  intros Hx Hp Hxd.
  induction y as [B g' Hg' D h' Hh']; intros Hyc Hyd.
  assert (Hyc1 : forall b, bcd (g' b)) by (intro b; apply (bcd_small (bnode B g' D h') b Hyc)).
  assert (Hyc2 : forall d ξ, complete ξ -> bcd (h' d ξ))
    by (intros d ξ Hξ; apply (bcd_big (bnode B g' D h') d ξ Hyc Hξ)).
  assert (Hyd' := Hyd). destruct Hyd' as [Hy1 [Hy2 Hy3]].
  assert (Hpieces : forall b, bsdirH (badd (bmul x (g' b)) x)).
  { intro b. apply bsdirH_badd; auto. apply bcd_bmul; auto. }
  assert (Hsd : sdir (bmul x (bnode B g' D h'))).
  { apply sdir_bmul; auto. intro b. apply bsdirH_sdir, Hpieces. }
  split; [ | split; [ | exact Hsd ] ].
  - intros [[b s]|[]]. exact (bsdirH_small _ s (Hpieces b)).
  - intros [[b c]|d] ξ Hξ.
    + exact (bsdirH_big _ c ξ (Hpieces b) Hξ).
    + apply Hh'; auto.
Qed.

(** *** Exponentiation *)

Lemma bsub_absorb c w : bsub w (badd c w).
Proof.
  induction w as [B g Hg D h Hh].
  apply bsub_intro.
  - intro b. destruct (badd_small_r c (bnode B g D h) b) as [t Ht].
    exists t. rewrite Ht. apply Hg.
  - intro d. destruct (badd_big_r c (bnode B g D h) d) as [t Ht].
    exists t. intro ξ. rewrite Ht. apply Hh.
Qed.

Lemma inf_pos z : (forall n, natOrdSize n ≤ z) -> 0 < z.
Proof.
  intro H. apply ord_lt_le_trans with 1; [ apply succ_lt | apply (H 1%nat) ].
Qed.

(** P ⊑ P·z for every positive z. *)
Lemma bsub_P_Pz P z : 0 < z -> bsub P (bmul P (embed z)).
Proof.
  destruct z as [Z k]. intro Hz.
  rewrite ord_lt_unfold in Hz. destruct Hz as [c _].
  eapply bsub_trans; [ apply (bsub_absorb (bmul P (embed (k c))) P) | ].
  apply (bsub_bmul_step P (embed (ord Z k)) c).
Qed.

Definition PF (P:BOrd) : Ord -> BOrd := fun ξ => bmul P (embed ξ).

Lemma bexpΩ_fam_s y j : exists t, forall ξ, bbigSz (bexpΩ y) t ξ = bmul (bexpΩ (bsmallSz y j)) (embed ξ).
Proof. apply (bexpΩ_big_s y j (inr tt)). Qed.

(** If a ⊏ b then, at every infinite z, Ω^a·z lies below a descendant
    of Ω^b reached through arguments at most z. *)
Lemma bleZ_exp_lt a b : bslt a b -> forall z, (forall n, natOrdSize n ≤ z) ->
  bleZ z (bmul (bexpΩ a) (embed z)) (bexpΩ b).
Proof.
  intro H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH]; intros z Hz.
  - destruct (bexpΩ_fam_s b j) as [t Ht].
    apply (LZ_big _ _ _ t z (ord_le_refl z)). rewrite Ht.
    apply LZ_sub. apply bsub_bmul_l, bsub_bexpΩ; auto.
  - destruct (bexpΩ_big_b b d) as [t Ht].
    apply (LZ_big _ _ _ t (natOrdSize n) (Hz n)). rewrite Ht. auto.
  - destruct (bexpΩ_fam_s b j) as [t Ht].
    apply (LZ_big _ _ _ t 1 (Hz 1%nat)). rewrite Ht.
    eapply bleZ_mono_r; [ apply IH; auto | apply (proj2 (bsub_bmul_one _)) ].
Qed.

Lemma bleZ_exp z a b : (forall n, natOrdSize n ≤ z) -> bleZ z a b -> bleZ z (bexpΩ a) (bexpΩ b).
Proof.
  intros Hz H.
  induction H as [a b H | a b j H IH | a b d ζ Hζ H IH].
  - apply LZ_sub, bsub_bexpΩ; auto.
  - destruct (bexpΩ_fam_s b j) as [t Ht].
    apply (LZ_big _ _ _ t 1 (Hz 1%nat)). rewrite Ht.
    eapply bleZ_mono_r; [ exact IH | apply (proj2 (bsub_bmul_one _)) ].
  - destruct (bexpΩ_big_b b d) as [t Ht].
    apply (LZ_big _ _ _ t ζ Hζ). rewrite Ht. exact IH.
Qed.

Definition emap (d:bdesc) : bdesc :=
  match d with
  | DSmall t => DFam (PF (bexpΩ t))
  | DFam h => DFam (fun ξ => bexpΩ (h ξ))
  end.

Lemma dcan_emap d : dcan d -> dcan (emap d).
Proof.
  destruct d as [t|h]; simpl; intro Hd.
  - assert (HM : bcd (bmul (bexpΩ t) bOmega)).
    { apply bcd_bmul; auto using bcd_bexpΩ, bpos_bexpΩ, bcd_Ω. }
    exact (dcan_ndesc (bmul (bexpΩ t) bOmega) (inr (inr tt)) HM).
  - assert (HE : bcd (bexpΩ (blimΩ h))) by (apply bcd_bexpΩ; auto).
    exact (dcan_ndesc (bexpΩ (blimΩ h)) (inr (inr (inr tt))) HE).
Qed.

Lemma dcan_fam_mono h : dcan (DFam h) -> forall ξ ξ', ξ ≤ ξ' -> bsub (h ξ) (h ξ').
Proof. intros [Hc _]. simpl in Hc. destruct Hc as [_ [_ [H _]]]. apply (H tt). Qed.

Lemma emap_D0 d1 d3 : dcan d1 -> dcan d3 -> D0 d1 d3 -> Dstar (emap d1) (emap d3).
Proof.
  intros Hc1 Hc3 H.
  apply D0_star; [ apply dcan_emap; auto | ].
  destruct H as [t u H | t u H | t h n H | h u e H | h1 h3 H | h1 h3 n e H | h1 h3 H]; simpl.
  - apply D0_ff_pt. intro ξ. apply bsub_bmul_l, bsub_bexpΩ; auto.
  - apply D0_ffZ. intros z Hz.
    eapply bleZ_mono_r; [ apply (bleZ_exp_lt t u H z Hz) | ].
    apply bsub_P_Pz, inf_pos; auto.
  - apply D0_ffZ. intros z Hz.
    apply bleZ_exp_lt; auto.
    apply bslt_bsub_r with (h (natOrdSize n)); auto.
    apply (dcan_fam_mono h Hc3); auto.
  - apply D0_ffZ. intros z Hz.
    destruct (bexpΩ_big_b u e) as [t Ht].
    eapply bleZ_mono_r; [ | apply bsub_P_Pz, inf_pos; auto ].
    apply (LZ_big _ _ _ t z (ord_le_refl z)). rewrite Ht.
    apply LZ_sub, bsub_bexpΩ; auto.
  - apply D0_ff_pt. intro ξ. apply bsub_bexpΩ; auto.
  - apply D0_ffZ. intros z Hz.
    destruct (bexpΩ_big_b (h3 (natOrdSize n)) e) as [t Ht].
    eapply bleZ_mono_r; [ | apply bsub_bexpΩ, (dcan_fam_mono h3 Hc3); apply (Hz n) ].
    apply (LZ_big _ _ _ t z (ord_le_refl z)). rewrite Ht.
    apply LZ_sub, bsub_bexpΩ; auto.
  - apply D0_ffZ. intros z Hz. apply bleZ_exp; auto.
Qed.

Lemma emap_Dstar d1 d3 : dcan d1 -> dcan d3 -> Dstar d1 d3 -> Dstar (emap d1) (emap d3).
Proof.
  intros Hc1 Hc3 H. revert Hc1.
  induction H as [d | d1 d2 d4 Hc2 H0 H IH]; intro Hc1.
  - apply Drefl.
  - apply Dstar_trans with (emap d2); [ apply (emap_D0 d1 d2 Hc1 Hc2 H0) | apply (IH Hc3 Hc2) ].
Qed.

Lemma bexpΩ_desc_cases y k :
  ndesc (bexpΩ y) k = DSmall bzero \/ exists yk, ndesc (bexpΩ y) k = emap (ndesc y yk).
Proof.
  destruct y as [B g' D h'].
  destruct k as [[[]|[[b [[[] _]|[]]]|[]]]|[[]|[[b [[[] _]|[]]]|d]]].
  - left. reflexivity.
  - right. exists (inl b). reflexivity.
  - right. exists (inr d). reflexivity.
Qed.

Lemma bexpΩ_desc_back y yk : exists k, ndesc (bexpΩ y) k = emap (ndesc y yk).
Proof.
  destruct y as [B g' D h']. destruct yk as [b|d].
  - exists (inr (inr (inl (existT _ b (inr tt))))). reflexivity.
  - exists (inr (inr (inr d))). reflexivity.
Qed.

Lemma bzero_dom_emap d : dcan d -> Dstar (DSmall bzero) (emap d).
Proof.
  intro Hd. apply D0_star; [ apply dcan_emap; auto | ].
  destruct d as [t|h]; simpl.
  - apply (D0_sf _ _ 1).
    apply bslt_bsub_r with (bexpΩ t); [ apply bpos_bexpΩ | ].
    apply (proj2 (bsub_bmul_one _)).
  - apply (D0_sf _ _ 0). apply bpos_bexpΩ.
Qed.

Lemma sdir_bexpΩ y : bcd y -> sdir y -> sdir (bexpΩ y).
Proof.
  intros Hyc Hy k1 k2.
  destruct (bexpΩ_desc_cases y k1) as [E1|[y1 E1]];
    destruct (bexpΩ_desc_cases y k2) as [E2|[y2 E2]]; rewrite E1, E2.
  - exists k1. rewrite E1. split; apply Drefl.
  - destruct (bexpΩ_desc_back y y2) as [k3 E3]. exists k3. rewrite E3.
    split; [ apply bzero_dom_emap, dcan_ndesc; auto | apply Drefl ].
  - destruct (bexpΩ_desc_back y y1) as [k3 E3]. exists k3. rewrite E3.
    split; [ apply Drefl | apply bzero_dom_emap, dcan_ndesc; auto ].
  - destruct (Hy y1 y2) as [y3 [D1 D2]].
    destruct (bexpΩ_desc_back y y3) as [k3 E3]. exists k3. rewrite E3.
    split; apply emap_Dstar; auto using dcan_ndesc.
Qed.

Lemma bsdirH_bzero : bsdirH bzero.
Proof. simpl. split; [ intros [] | split; [ intros [] | intros [[]|[]] ] ]. Qed.

Theorem bsdirH_bexpΩ y : bcd y -> bsdirH y -> bsdirH (bexpΩ y).
Proof.
  induction y as [B g' Hg' D h' Hh']; intros Hyc Hyd.
  assert (Hyc1 : forall b, bcd (g' b)) by (intro b; apply (bcd_small (bnode B g' D h') b Hyc)).
  assert (Hyc2 : forall d ξ, complete ξ -> bcd (h' d ξ))
    by (intros d ξ Hξ; apply (bcd_big (bnode B g' D h') d ξ Hyc Hξ)).
  assert (Hyd' := Hyd). destruct Hyd' as [Hy1 [Hy2 Hy3]].
  assert (Hsd : sdir (bexpΩ (bnode B g' D h'))) by (apply sdir_bexpΩ; auto).
  split; [ | split; [ | exact Hsd ] ].
  - intros [[]|[[b [[[] _]|[]]]|[]]]. exact bsdirH_bzero.
  - intros [[]|[[b [[[] _]|[]]]|d]] ξ Hξ.
    + change (bsdirH (bmul (bexpΩ (g' b)) (embed ξ))).
      apply bsdirH_bmul; auto using bcd_bexpΩ, bpos_bexpΩ, bcd_embed, bsdirH_embed.
    + change (bsdirH (bexpΩ (h' d ξ))). apply Hh'; auto.
Qed.

(** *** The tower below ε_{Ω+1} *)

Lemma bsdirH_bsucc x : bsdirH x -> bsdirH (bsucc x).
Proof.
  intro Hx. simpl. split; [ intros _; exact Hx | split; [ intros [] | ] ].
  intros [[]|[]] [[]|[]]. exists (inl tt). split; apply Drefl.
Qed.

Lemma bsdirH_btower n : bsdirH (btower n).
Proof.
  induction n.
  - change (bsdirH (bsucc bOmega)). apply bsdirH_bsucc, bsdirH_Ω.
  - change (bsdirH (bexpΩ (btower n))). apply bsdirH_bexpΩ; auto using bcd_btower.
Qed.


Theorem bach_bphi_tower f (Hf : normal_function f) n : BRep f (btower n) (bphi f (btower n)).
Proof. apply bach_bphi_canon; auto using bcd_btower, bsdirH_btower. Qed.


(** ** The top: ε_{Ω+1}

The components of @bεΩ1@ are the towers.  Each is dominated by the
next: tower n lies strictly below a tree D that is reachable from
tower (n+1) through arguments at most z, for every infinite z.  This
is a z-relative variant of @bslt@, and it implies domination by
@bnest@ once the fixpoint property is carried down the path. *)

Lemma bleZ_trans z a b c : bleZ z a b -> bleZ z b c -> bleZ z a c.
Proof.
  intros H1 H2. revert a H1.
  induction H2 as [b c H | b c j H IH | b c d ζ Hζ H IH]; intros a H1.
  - eapply bleZ_mono_r; eauto.
  - apply (LZ_small _ _ _ j). auto.
  - apply (LZ_big _ _ _ d ζ Hζ). auto.
Qed.


(** *** The base case: Ω+1 *)

Lemma embed_le_mul P ζ : (exists t, bsmallSz P t = bzero) -> bsub (embed ζ) (bmul P (embed ζ)).
Proof.
  intros [t0 Ht0].
  induction ζ as [X k Hk].
  apply bsub_intro.
  - intro i.
    destruct (badd_small_r (bmul P (embed (k i))) P t0) as [s Hs].
    destruct (bmul_small_r P (embed (ord X k)) i s) as [t Ht].
    exists t. rewrite Ht.
    change (bsub (embed (k i)) (bsmallSz (badd (bmul P (embed (k i))) P) s)).
    rewrite Hs, Ht0.
    eapply bsub_trans; [ apply Hk | apply bsub_le_badd ].
  - intros [].
Qed.

Lemma Ω_le_exp w : 0 < w -> bsub bOmega (bexpΩ (embed w)).
Proof.
  destruct w as [W m]. intro Hw.
  rewrite ord_lt_unfold in Hw. destruct Hw as [c _].
  apply bsub_intro.
  - intros [].
  - intros [].
    destruct (bexpΩ_fam_s (embed (ord W m)) c) as [t Ht].
    exists t. intro ξ. rewrite Ht.
    change (bsub (embed ξ) (bmul (bexpΩ (embed (m c))) (embed ξ))).
    apply embed_le_mul, bexpΩ_small_zero.
Qed.

(** P·k lies strictly below P·(k+1) when P has the small child 0. *)
Lemma bslt_mul_succ P k : (exists t, bsmallSz P t = bzero) ->
  bslt (bmul P (embed k)) (bmul P (embed (succOrd k))).
Proof.
  intros [t0 Ht0].
  destruct (badd_small_r (bmul P (embed k)) P t0) as [s Hs].
  destruct (bmul_small_r P (embed (succOrd k)) tt s) as [t Ht].
  apply (bslt_small _ _ t). rewrite Ht.
  change (bsub (bmul P (embed k)) (bsmallSz (badd (bmul P (embed k)) P) s)).
  rewrite Hs, Ht0. apply bsub_le_badd.
Qed.

Lemma bsucc_Ω_le P : bsub bOmega P -> (exists t, bsmallSz P t = bzero) ->
  bsub (bsucc bOmega) (bmul P (embed 2)).
Proof.
  intros HP [t0 Ht0].
  destruct (badd_small_r (bmul P (embed 1)) P t0) as [s Hs].
  destruct (bmul_small_r P (embed 2) tt s) as [t Ht].
  apply bsub_intro.
  - intros []. exists t. rewrite Ht.
    change (bsub bOmega (bsmallSz (badd (bmul P (embed 1)) P) s)).
    rewrite Hs, Ht0.
    eapply bsub_trans; [ exact HP | ].
    eapply bsub_trans; [ apply (proj2 (bsub_bmul_one P)) | apply bsub_le_badd ].
  - intros [].
Qed.

Lemma tower_base z : (forall n, natOrdSize n ≤ z) ->
  exists D, bslt (bsucc bOmega) D /\ bleZ z D (bexpΩ (bsucc bOmega)).
Proof.
  intro Hz.
  assert (H2 : 1 < z) by (apply ord_lt_le_trans with 2; [ apply succ_lt | apply (Hz 2%nat) ]).
  destruct z as [Z k].
  rewrite ord_lt_unfold in H2. destruct H2 as [c Hc].
  assert (Hc0 : 0 < k c) by (apply ord_lt_le_trans with 1; [ apply succ_lt | exact Hc ]).
  exists (bexpΩ (embed (ord Z k))). split.
  - destruct (bexpΩ_fam_s (embed (ord Z k)) c) as [t Ht].
    apply (bslt_big _ _ t 3). rewrite Ht.
    change (bslt (bsucc bOmega) (bmul (bexpΩ (embed (k c))) (embed (succOrd 2)))).
    apply bslt_bsub_l with (bmul (bexpΩ (embed (k c))) (embed 2)).
    + apply bsucc_Ω_le; [ apply Ω_le_exp; auto | apply bexpΩ_small_zero ].
    + apply bslt_mul_succ, bexpΩ_small_zero.
  - destruct (bexpΩ_fam_s (bsucc bOmega) tt) as [t Ht].
    apply (LZ_big _ _ _ t 1 (Hz 1%nat)). rewrite Ht.
    change (bleZ (ord Z k) (bexpΩ (embed (ord Z k))) (bmul (bexpΩ bOmega) (embed 1))).
    eapply bleZ_mono_r; [ | apply (proj2 (bsub_bmul_one _)) ].
    destruct (bexpΩ_big_b bOmega tt) as [t' Ht'].
    apply (LZ_big _ _ _ t' (ord Z k) (ord_le_refl _)). rewrite Ht'.
    apply LZ_sub, bsub_refl.
Qed.

(** *** The inductive step, and domination along the tower *)

Lemma tower_rel n : forall z, (forall m, natOrdSize m ≤ z) ->
  exists D, bslt (btower n) D /\ bleZ z D (btower (S n)).
Proof.
  induction n as [|n IH]; intros z Hz.
  - apply tower_base; auto.
  - destruct (IH z Hz) as [D [H1 H2]].
    exists (bexpΩ D). split.
    + apply bslt_bexpΩ; auto.
    + change (bleZ z (bexpΩ D) (bexpΩ (btower (S n)))). apply bleZ_exp; auto.
Qed.


(** *** Domination along the tower, and ε_{Ω+1} *)

Lemma tower_dom f (Hf : normal_function f) n z :
  complete z -> bphi f (btower (S n)) z ≤ z -> bphi f (btower n) z ≤ z.
Proof.
  intros Hz Hle.
  destruct (dcan_good f Hf _ (bcd_btower (S n))) as [Hfam Hgood].
  assert (Hfix : bfix f (btower (S n)) z) by (apply bfix_of_fix; auto).
  assert (Hinf : forall m, natOrdSize m ≤ z).
  { intro m. apply fix_onePlus_finite with f; auto. apply Hfix. }
  destruct (tower_rel n z Hinf) as [D [H1 H2]].
  apply (bleZ_nest f Hf z D (btower (S n)) (btower n) H2 H1 (btower (S n))); auto using bsub_refl.
Qed.

Lemma tower_dom_le f (Hf : normal_function f) n m :
  (n <= m)%nat -> forall z, complete z -> bphi f (btower m) z ≤ z -> bphi f (btower n) z ≤ z.
Proof.
  intro H. induction H as [|m H IH]; intros z Hz Hle; auto.
  apply IH; auto. apply tower_dom; auto.
Qed.

Lemma bdirH_εΩ1 f (Hf : normal_function f) : bdirH f bεΩ1.
Proof.
  simpl. split; [ | split ].
  - intro n. apply bsdirH_bdirH; auto using bcd_btower, bsdirH_btower.
  - intros [].
  - intros [n1|[]] [n2|[]].
    exists (inl (Nat.max n1 n2)). split; intros z Hz Hle; simpl in *.
    + apply (tower_dom_le f Hf n1 (Nat.max n1 n2)); auto. apply PeanoNat.Nat.le_max_l.
    + apply (tower_dom_le f Hf n2 (Nat.max n1 n2)); auto. apply PeanoNat.Nat.le_max_r.
Qed.

Theorem bach_bphi_εΩ1 f (Hf : normal_function f) : BRep f bεΩ1 (bphi f bεΩ1).
Proof.
  destruct (dcan_good f Hf _ bcd_bεΩ1) as [Hfam Hgood].
  apply bach_bphi; auto. apply bdirH_εΩ1; auto.
Qed.

(** ** Certification of the Bachmann–Howard ordinal

Bachmann's φ (one component at a time), at the index ε_{Ω+1},
represents the provably normal hierarchy @bphi@ there.  In particular
the Bachmann–Howard ordinal as defined in @BachmannDefs@ is
@BachmannHoward@. *)
Corollary bach_BachmannHoward : BHO ≈ BachmannHoward.
Proof.
  apply (bach_bphi_εΩ1 powOmega powOmega_normal). apply zero_complete.
Qed.
