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

Open Scope ord_scope.

(** * Normality of Bachmann's hierarchy, proved directly

In @BachmannDefs@ the hierarchy is calibrated against known normal
functions (Veblen, Schütte's columns), which takes us as far as the
Large Veblen Ordinal.  Beyond that there is nothing to calibrate
against, so here we prove normality of φ directly.

The proof splits in two.

 (A) A generic construction, independent of index trees.  Given a base
     normal function f and an arbitrary family of normal functions
     F_i, let E enumerate the common fixpoints of f and all the F_i.
     We take least fixpoints of finite compositions F_{i_1} ∘ … ∘
     F_{i_n} ∘ f, rather than of the F_i individually: the
     compositions form a directed family (any two are dominated by
     their concatenation), so E is normal with no further hypotheses
     on the F_i.

 (B) The Bachmann-specific content.  A node of an index tree takes
     least fixpoints of its components one at a time, and its value
     is a common fixpoint only when the components are suitably
     nested.  The remaining task is to show, by induction over the
     canonical trees, that φ_T agrees with the enumerator E built from
     T's components.
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

  Lemma comps_monotone L : forall x y, x ≤ y -> comps L x ≤ comps L y.
  Proof. apply normal_monotone, comps_normal. Qed.

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

  Fixpoint cfe (y:Ord) : Ord :=
    match y with
    | ord Y h => supOrd (fun L => fixOrd (comps L) (ord Y (fun j => cfe (h j))))
    end.

  Lemma cfe_unroll (y:Ord) :
    cfe y = supOrd (fun L => fixOrd (comps L) (limOrd (fun j => cfe (y j)))).
  Proof. destruct y; reflexivity. Qed.

  Global Opaque cfe.

  Lemma cfe_monotone : forall x y, x ≤ y -> cfe x ≤ cfe y.
  Proof.
    intros x y; revert x.
    induction y as [Y h Hy]; intros [X g] Hxy.
    rewrite (cfe_unroll (ord X g)), (cfe_unroll (ord Y h)).
    apply sup_ord_le_morphism; intro L.
    apply fixOrd_monotone; [ apply comps_monotone | ].
    apply limit_least; intro i.
    destruct (ord_le_subord _ _ Hxy i) as [j Hj].
    apply ord_le_lt_trans with (cfe (h j)); [ apply Hy; auto | ].
    rewrite ord_lt_unfold. exists j. reflexivity.
  Qed.

  Lemma cfe_start_le (y:Ord) L :
    limOrd (fun j => cfe (y j)) ≤ fixOrd (comps L) (limOrd (fun j => cfe (y j))).
  Proof. apply fixOrd_above. Qed.

  Lemma cfe_ge_fix (y:Ord) L :
    fixOrd (comps L) (limOrd (fun j => cfe (y j))) ≤ cfe y.
  Proof.
    rewrite (cfe_unroll y).
    apply (sup_le _ (fun L => fixOrd (comps L) (limOrd (fun j => cfe (y j)))) L).
  Qed.

  Lemma cfe_complete : forall y, complete y -> complete (cfe y).
  Proof.
    induction y as [Y h Hy]; intro Hyc.
    assert (Hyc' := Hyc). destruct Hyc' as [Hdir [Hinh Hhc]].
    assert (Hs : complete (limOrd (fun j => cfe (ord Y h j)))).
    { apply lim_complete.
      - intro j. apply Hy; auto.
      - intros j1 j2. destruct (Hdir j1 j2) as [j' [H1 H2]].
        exists j'. split; apply cfe_monotone; auto.
      - exact Hinh. }
    rewrite cfe_unroll.
    apply sup_complete.
    - intro L. apply normal_fix_complete; auto.
      + apply normal_inflationary, comps_normal.
      + apply comps_monotone.
      + apply comps_complete.
    - intros L1 L2. exists (L1 ++ L2).
      split; apply fixOrd_monotone_func''; auto.
      + intros. apply comps_app_le_l; auto.
      + apply comps_complete.
      + apply comps_monotone.
      + intros. apply comps_app_le_r; auto.
      + apply comps_complete.
      + apply comps_monotone.
    - left. exists []. unfold fixOrd.
      eapply ord_lt_le_trans; [ | apply (sup_le _ _ 1%nat) ].
      simpl. apply normal_nonzero; auto.
  Qed.

  Lemma cfe_nonzero (y:Ord) : 0 < cfe y.
  Proof.
    eapply ord_lt_le_trans; [ | apply (cfe_ge_fix y []) ].
    unfold fixOrd.
    eapply ord_lt_le_trans; [ | apply (sup_le _ _ 1%nat) ].
    simpl. apply normal_nonzero; auto.
  Qed.

  Lemma cfe_increasing : forall x y, complete y -> x < y -> cfe x < cfe y.
  Proof.
    intros x [Y h] Hyc Hxy.
    rewrite ord_lt_unfold in Hxy. destruct Hxy as [j Hj].
    apply ord_le_lt_trans with (cfe (h j)); [ apply cfe_monotone; auto | ].
    eapply ord_lt_le_trans; [ | apply (cfe_ge_fix (ord Y h) []) ].
    eapply ord_lt_le_trans; [ | apply cfe_start_le ].
    rewrite ord_lt_unfold. exists j. reflexivity.
  Qed.

  (** The least fixpoints of the compositions, at a complete start,
      are fixed by f and by every F_i. *)
  Lemma comps_fix_closed L s : complete s ->
    f (fixOrd (comps L) s) ≤ fixOrd (comps L) s /\
    forall i, F i (fixOrd (comps L) s) ≤ fixOrd (comps (i :: L)) s.
  Proof.
    intro Hs.
    assert (HcL := comps_normal L).
    split.
    - transitivity (comps L (fixOrd (comps L) s)).
      + apply (comps_app_le_l [] L). apply normal_fix_complete; auto.
        * apply normal_inflationary; auto.
        * apply normal_monotone; auto.
        * apply normal_complete; auto.
      + apply (proj2 (normal_fixpoint _ HcL s Hs)).
    - intro i.
      assert (Hz : complete (fixOrd (comps (i :: L)) s)).
      { apply normal_fix_complete; auto using comps_normal.
        - apply normal_inflationary, comps_normal.
        - apply comps_monotone.
        - apply comps_complete. }
      transitivity (F i (fixOrd (comps (i :: L)) s)).
      + apply normal_monotone; auto.
        apply fixOrd_monotone_func''; auto.
        * intros x Hx. simpl. apply normal_inflationary; auto. apply comps_complete; auto.
        * apply comps_complete.
        * apply comps_monotone.
      + transitivity (comps (i :: L) (fixOrd (comps (i :: L)) s)).
        * simpl. apply normal_monotone; auto.
          apply normal_inflationary; auto using comps_normal.
        * apply (proj2 (normal_fixpoint _ (comps_normal (i :: L)) s Hs)).
  Qed.
  Arguments comps_fix_closed : clear implicits.

  Lemma cfe_start_complete (y:Ord) : complete y -> complete (limOrd (fun j => cfe (y j))).
  Proof.
    destruct y as [Y h]. intro Hyc.
    assert (Hyc' := Hyc). destruct Hyc' as [Hdir [Hinh Hhc]].
    apply lim_complete.
    - intro j. apply cfe_complete; auto.
    - intros j1 j2. destruct (Hdir j1 j2) as [j' [H1 H2]].
      exists j'. split; apply cfe_monotone; auto.
    - exact Hinh.
  Qed.

  Lemma comps_fix_complete L s : complete s -> complete (fixOrd (comps L) s).
  Proof.
    intro Hs. apply normal_fix_complete; auto.
    - apply normal_inflationary, comps_normal.
    - apply comps_monotone.
    - apply comps_complete.
  Qed.

  Lemma comps_fix_directed s : complete s -> directed (list I) (fun L => fixOrd (comps L) s).
  Proof.
    intros Hs L1 L2. exists (L1 ++ L2).
    split; apply fixOrd_monotone_func''; auto.
    - intros. apply comps_app_le_l; auto.
    - apply comps_complete.
    - apply comps_monotone.
    - intros. apply comps_app_le_r; auto.
    - apply comps_complete.
    - apply comps_monotone.
  Qed.

  (** Every value of the enumerator is a common fixpoint. *)
  Lemma cfe_fix_f y : complete y -> f (cfe y) ≤ cfe y.
  Proof.
    intro Hy.
    assert (Hs := cfe_start_complete y Hy).
    rewrite cfe_unroll.
    eapply ord_le_trans;
      [ apply (normal_continuous f Hf (list I) _ [] (comps_fix_directed _ Hs)
                                 (fun L => comps_fix_complete L _ Hs)) | ].
    apply sup_ord_le_morphism. intro L.
    apply (comps_fix_closed L _ Hs).
  Qed.

  Lemma cfe_fix_F i y : complete y -> F i (cfe y) ≤ cfe y.
  Proof.
    intro Hy.
    assert (Hs := cfe_start_complete y Hy).
    rewrite cfe_unroll.
    eapply ord_le_trans;
      [ apply (normal_continuous (F i) (HF i) (list I) _ [] (comps_fix_directed _ Hs)
                                 (fun L => comps_fix_complete L _ Hs)) | ].
    apply sup_least. intro L.
    eapply ord_le_trans; [ apply (comps_fix_closed L _ Hs) | ].
    apply (sup_le _ (fun L => fixOrd (comps L) (limOrd (fun j => cfe (y j)))) (i :: L)).
  Qed.

  (** ... and the least one above the previous values. *)
  Lemma cfe_least (y z:Ord) :
    limOrd (fun j => cfe (y j)) ≤ z -> f z ≤ z -> (forall i, F i z ≤ z) -> cfe y ≤ z.
  Proof.
    intros Hs H1 H2.
    rewrite cfe_unroll.
    apply sup_least. intro L.
    apply fixOrd_least; auto.
    - apply comps_monotone.
    - apply comps_closed; auto.
  Qed.

  Lemma cfe_continuous : scott_continuous cfe.
  Proof.
    intros A g a0 Hdir Hc.
    assert (Hdir' : directed A (fun a => cfe (g a))).
    { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
      exists a'. split; apply cfe_monotone; auto. }
    assert (Hc' : forall a, complete (cfe (g a))) by (intro; apply cfe_complete; auto).
    apply cfe_least.
    - apply limit_least. intros [a c].
      eapply ord_lt_le_trans; [ | apply (sup_le _ (fun a => cfe (g a)) a) ].
      apply cfe_increasing; [ apply Hc | apply (index_lt (g a) c) ].
    - eapply ord_le_trans; [ apply (normal_continuous f Hf A _ a0 Hdir' Hc') | ].
      apply sup_ord_le_morphism. intro a. apply cfe_fix_f; auto.
    - intro i.
      eapply ord_le_trans; [ apply (normal_continuous (F i) (HF i) A _ a0 Hdir' Hc') | ].
      apply sup_ord_le_morphism. intro a. apply cfe_fix_F; auto.
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

End common_fixpoints.

(** ** (B) A hierarchy that is normal by construction

We interpret each node of an index tree by the common-fixpoint
enumerator of its components, following the same structural
recursion as @bach@: a small child contributes its own function, and
an Ω-family contributes its diagonal ξ ↦ φ_{h ξ}(0).  By (A), the
result is normal at every node whose Ω-families have normal
diagonals.  That side condition is the constructive form of
Bachmann's requirement that fundamental sequences be continuous.

Note that @cfe@ always includes the base f among the functions whose
common fixpoints it enumerates; consequently @bphi@ of a leaf is the
enumeration of the fixpoints of f, and in general @bphi T@ corresponds
to Bachmann's φ_{1+T} rather than φ_T.  Avoiding this shift would
require deciding whether a node has any components at all, which is
not available constructively for arbitrary index types.  The shift is
harmless: 1+α = α for every infinite index, so φ_Ω, φ_{Ω^Ω}, the
Bachmann–Howard ordinal, etc., are unaffected.

What remains is to show that the canonical trees satisfy @bgood@, and
that on them @bphi@ agrees with @bach@ (the nesting property). *)

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

  (** Every Ω-family, at every depth, has a normal diagonal. *)
  Fixpoint bgood (T:BOrd) : Prop :=
    match T with
    | bnode A g C h =>
      (forall a, bgood (g a)) /\
      (forall c ξ, bgood (h c ξ)) /\
      (forall c, normal_function (fun ξ => bphi (h c ξ) 0))
    end.

  Hypothesis Hf : normal_function f.

  Theorem bphi_normal : forall T, bgood T -> normal_function (bphi T).
  Proof.
    induction T as [A g Hg C h Hh]; simpl; intros [H1 [H2 H3]].
    apply cfe_normal; auto.
    intros [a|c]; [ apply Hg; auto | apply H3 ].
  Qed.

  (** At a good node, every component fixes every value. *)
  Definition bphi_fam {A C:Type} (g:A -> BOrd) (h:C -> Ord -> BOrd) (k:(A + C)%type) : Ord -> Ord :=
    match k with
    | inl a => bphi (g a)
    | inr c => fun ξ => bphi (h c ξ) 0
    end.

  Lemma bphi_fam_normal A g C h :
    bgood (bnode A g C h) -> forall k, normal_function (@bphi_fam A C g h k).
  Proof.
    simpl; intros [H1 [H2 H3]] [a|c]; simpl; [ apply bphi_normal; auto | apply H3 ].
  Qed.

  Lemma bphi_fix_small A g C h a y :
    bgood (bnode A g C h) -> complete y ->
    bphi (g a) (bphi (bnode A g C h) y) ≤ bphi (bnode A g C h) y.
  Proof.
    intros HT Hy.
    exact (cfe_fix_F f Hf (A + C) (bphi_fam g h) (bphi_fam_normal A g C h HT) (inl a) y Hy).
  Qed.

  Lemma bphi_fix_big A g C h c y :
    bgood (bnode A g C h) -> complete y ->
    bphi (h c (bphi (bnode A g C h) y)) 0 ≤ bphi (bnode A g C h) y.
  Proof.
    intros HT Hy.
    exact (cfe_fix_F f Hf (A + C) (bphi_fam g h) (bphi_fam_normal A g C h HT) (inr c) y Hy).
  Qed.

  Lemma bphi_fix_base A g C h y :
    bgood (bnode A g C h) -> complete y ->
    f (bphi (bnode A g C h) y) ≤ bphi (bnode A g C h) y.
  Proof.
    intros HT Hy.
    exact (cfe_fix_f f Hf (A + C) (bphi_fam g h) (bphi_fam_normal A g C h HT) y Hy).
  Qed.

End bphi.

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

Lemma cfe_monotone_gen f I F :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall i x y, x ≤ y -> F i x ≤ F i y) ->
  forall x y, x ≤ y -> cfe f I F x ≤ cfe f I F y.
Proof.
  intros Hf HF x y; revert x.
  induction y as [Y h Hy]; intros [X g] Hxy.
  rewrite (cfe_unroll f I F (ord X g)), (cfe_unroll f I F (ord Y h)).
  apply sup_ord_le_morphism; intro L.
  apply fixOrd_monotone; [ apply comps_monotone_gen; auto | ].
  apply limit_least; intro i.
  destruct (ord_le_subord _ _ Hxy i) as [j Hj].
  apply ord_le_lt_trans with (cfe f I F (h j)); [ apply Hy; auto | ].
  rewrite ord_lt_unfold. exists j. reflexivity.
Qed.

(** If every member of F is dominated by a member of F', the
    enumerator for F lies below the one for F'. *)
Lemma cfe_mono_family f I J F F' :
  (forall x y, x ≤ y -> f x ≤ f y) ->
  (forall j x y, x ≤ y -> F' j x ≤ F' j y) ->
  (forall i, exists j, forall x, F i x ≤ F' j x) ->
  forall y, cfe f I F y ≤ cfe f J F' y.
Proof.
  intros Hf HF' Hfam y.
  induction y as [Y h Hy].
  rewrite (cfe_unroll f I F (ord Y h)), (cfe_unroll f J F' (ord Y h)).
  apply sup_least; intro L.
  destruct (comps_mono_family f I J F F' HF' Hfam L) as [L' HL'].
  eapply ord_le_trans;
    [ | apply (sup_le _ (fun L => fixOrd (comps f J F' L) (limOrd (fun j => cfe f J F' (ord Y h j)))) L') ].
  transitivity (fixOrd (comps f J F' L') (limOrd (fun j => cfe f I F (ord Y h j)))).
  - apply fixOrd_monotone_func; auto.
    apply comps_monotone_gen; auto.
  - apply fixOrd_monotone; [ apply comps_monotone_gen; auto | ].
    apply lim_le_mor; intro j. apply Hy.
Qed.

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
    (recursively) strictly below a member of one of y's Ω-families at
    a finite argument. *)
Inductive bslt : BOrd -> BOrd -> Prop :=
| bslt_small : forall x y b, bsub x (bsmallSz y b) -> bslt x y
| bslt_big : forall x y d n, bslt x (bbigSz y d (natOrdSize n)) -> bslt x y.

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

Lemma bgood_bfam_small f x a : bgood f x -> bgood f (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bgood_big f x c ξ : bgood f x -> bgood f (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Theorem bphi_strict f (Hf : normal_function f) :
  forall x y, bslt x y -> bgood f y -> bfam y -> bphi f x 0 < bphi f y 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros x y H.
  induction H as [x y b Hb | x y d n H IH]; intros Hgood Hfam.
  - destruct y as [A g C h]. simpl in Hb.
    assert (Hz : complete (bphi f (bnode A g C h) 0)).
    { apply normal_complete; auto using zero_complete. apply bphi_normal; auto. }
    apply ord_le_lt_trans with (bphi f (g b) 0).
    { apply (proj2 (bphi_mono_index f Hfm (g b) (bfam_small _ Hfam b))); auto. }
    eapply ord_lt_le_trans; [ | apply (bphi_fix_small f Hf A g C h b 0 Hgood zero_complete) ].
    apply normal_increasing; auto.
    + apply bphi_normal; auto. apply (bgood_bfam_small f (bnode A g C h) b Hgood).
    + apply normal_nonzero. apply bphi_normal; auto.
  - destruct y as [A g C h].
    assert (Hz : complete (bphi f (bnode A g C h) 0)).
    { apply normal_complete; auto using zero_complete. apply bphi_normal; auto. }
    eapply ord_lt_le_trans; [ apply IH | ].
    + apply (bgood_big f (bnode A g C h) d (natOrdSize n) Hgood).
    + apply (bfam_big _ Hfam d (natOrdSize n)).
    + eapply ord_le_trans; [ | apply (bphi_fix_big f Hf A g C h d 0 Hgood zero_complete) ].
      change (bphi f (h d (natOrdSize n)) 0 ≤ bphi f (h d (bphi f (bnode A g C h) 0)) 0).
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hfam d _))).
      apply (bfam_fam _ Hfam d).
      apply fix_onePlus_finite with f; auto.
      apply bphi_fix_base; auto using zero_complete.
Qed.

(** ** Continuity of the diagonal *)

Section fix_lemmas.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.

  Lemma bphi_fix_small' T a y :
    bgood f T -> complete y -> bphi f (bsmallSz T a) (bphi f T y) ≤ bphi f T y.
  Proof. destruct T as [A g C h]. apply bphi_fix_small; auto. Qed.

  Lemma bphi_fix_big' T c y :
    bgood f T -> complete y -> bphi f (bbigSz T c (bphi f T y)) 0 ≤ bphi f T y.
  Proof. destruct T as [A g C h]. apply bphi_fix_big; auto. Qed.

  Lemma bphi_fix_base' T y : bgood f T -> complete y -> f (bphi f T y) ≤ bphi f T y.
  Proof. destruct T as [A g C h]. apply bphi_fix_base; auto. Qed.

  Lemma bgood_diag_normal T c : bgood f T -> normal_function (fun ξ => bphi f (bbigSz T c ξ) 0).
  Proof. destruct T as [A g C h]; simpl; intuition. Qed.
End fix_lemmas.

(** If h is a @bsub@-monotone family of good trees and h at a supremum
    lies below the merge of the h at the approximants, then the
    diagonal ξ ↦ φ_{h ξ}(0) is continuous. *)
Theorem bphi_diag_cont f (Hf : normal_function f) (h : Ord -> BOrd) :
  (forall ξ, bgood f (h ξ)) -> (forall ξ, bfam (h ξ)) ->
  (forall ξ ξ', ξ ≤ ξ' -> bsub (h ξ) (h ξ')) ->
  (forall A (g:A -> Ord) (a0:A), directed A g -> (forall a, complete (g a)) ->
     bsub (h (supOrd g)) (bsup (fun a => h (g a)))) ->
  scott_continuous (fun ξ => bphi f (h ξ) 0).
Proof.
  intros Hgood Hfam Hmono Hcont A g a0 Hdir Hc.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (Hzc : forall a, complete (bphi f (h (g a)) 0)).
  { intro a. apply normal_complete; auto using zero_complete. apply bphi_normal; auto. }
  assert (Hzmono : forall a b, g a ≤ g b -> bphi f (h (g a)) 0 ≤ bphi f (h (g b)) 0).
  { intros a b Hab. apply (proj2 (bphi_mono_index f Hfm _ (Hfam _))). apply Hmono; auto. }
  assert (Hzdir : directed A (fun a => bphi f (h (g a)) 0)).
  { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
    exists a'. split; apply Hzmono; auto. }
  transitivity (bphi f (bsup (fun a => h (g a))) 0).
  { apply (proj2 (bphi_mono_index f Hfm _ (bfam_bsup _ (fun a => Hfam (g a))))).
    apply Hcont; auto. }
  assert (HFam : forall k, normal_function
             (bphi_fam f (fun p : sigT (fun a => bsmall (h (g a))) => bsmallSz (h (g (projT1 p))) (projT2 p))
                         (fun p : sigT (fun a => bbig (h (g a))) => bbigSz (h (g (projT1 p))) (projT2 p)) k)).
  { intros [[a s]|[a c]]; simpl.
    - apply bphi_normal; auto. apply bgood_bfam_small; auto.
    - apply bgood_diag_normal; auto. }
  apply (cfe_least f Hf _ _ HFam).
  - apply limit_least. intros [].
  - eapply ord_le_trans; [ apply (normal_continuous f Hf A _ a0 Hzdir Hzc) | ].
    apply sup_ord_le_morphism. intro a. apply bphi_fix_base'; auto using zero_complete.
  - intros [[a s]|[a c]]; simpl.
    + assert (HG : normal_function (bphi f (bsmallSz (h (g a)) s))).
      { apply bphi_normal; auto. apply bgood_bfam_small; auto. }
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
    + assert (HD : normal_function (fun ξ => bphi f (bbigSz (h (g a)) c ξ) 0)).
      { apply bgood_diag_normal; auto. }
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
Qed.

(** ** Structural conditions on Ω-families that make a tree good *)

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

Theorem bcanon_good f (Hf : normal_function f) : forall T, bcanon T -> bfam T /\ bgood f T.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction T as [A g Hg C h Hh]; intros [H1 [H2 [H3 [H4 H5]]]].
  assert (HA : forall a, bfam (g a) /\ bgood f (g a)) by (intro a; apply Hg; auto).
  assert (HC : forall c ξ, bfam (h c ξ) /\ bgood f (h c ξ)) by (intros c ξ; apply Hh; auto).
  split.
  - simpl. split; [ intro a; apply HA | split; [ intros c ξ; apply HC | exact H3 ] ].
  - simpl. split; [ intro a; apply HA | split; [ intros c ξ; apply HC | ] ].
    intro c. constructor.
    + intros x y Hxy.
      apply (proj2 (bphi_mono_index f Hfm (h c y) (proj1 (HC c y)))). apply H3; auto.
    + intros x y Hy Hxy.
      apply bphi_strict; [ exact Hf | apply H4; auto | apply HC | apply HC ].
    + apply bphi_diag_cont;
        [ exact Hf | intro; apply HC | intro; apply HC | intros ξ ξ' H; apply H3; auto
        | intros B k b0 Hdir Hk; apply (H5 c B k b0); auto ].
    + intros x _. apply normal_complete; [ apply bphi_normal; auto; apply HC | apply zero_complete ].
    + intro x. apply normal_nonzero. apply bphi_normal; auto. apply HC.
Qed.

Corollary bcanon_normal f (Hf : normal_function f) T : bcanon T -> normal_function (bphi f T).
Proof.
  intro HT. apply bphi_normal; auto. apply bcanon_good; auto.
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

Corollary bphi_Ω_normal f (Hf : normal_function f) : normal_function (bphi f bOmega).
Proof. apply bcanon_normal; auto using bcanon_Ω. Qed.

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
  intros H1 H2. induction H2 as [a b j Hj | a b d n H IH].
  - apply (bslt_small _ _ j). eapply bsub_trans; eauto.
  - apply (bslt_big _ _ d n). auto.
Qed.

Lemma bslt_bsub_r a b b' : bslt a b -> bsub b b' -> bslt a b'.
Proof.
  intro H. revert b'.
  induction H as [a b j Hj | a b d n H IH]; intros b' Hb.
  - destruct (bsub_small _ _ Hb j) as [j' Hj'].
    apply (bslt_small _ _ j'). eapply bsub_trans; eauto.
  - destruct (bsub_big _ _ Hb d) as [d' Hd'].
    apply (bslt_big _ _ d' n). apply IH. apply Hd'.
Qed.

Definition bpos (z:BOrd) : Prop := bslt bzero z.

(** w lies strictly below w + z whenever z is strictly above something. *)
Lemma bslt_badd_pos w : forall x z, bslt x z -> bslt w (badd w z).
Proof.
  intros x z H.
  induction H as [x z j Hj | x z d n H IH].
  - destruct (badd_small_r w z j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_le_badd.
  - destruct (badd_big_r w z d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
Qed.

Lemma bslt_badd_r x : forall a b, bslt a b -> bslt (badd x a) (badd x b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH].
  - destruct (badd_small_r x b j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_badd_r; auto.
  - destruct (badd_big_r x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
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
  induction H as [a b j Hj | a b d n H IH].
  - eapply bslt_bsub_l; [ apply bsub_bmul_r, Hj | ].
    eapply bslt_bsub_r; [ | apply bsub_bmul_step ].
    apply (bslt_badd_pos _ bzero x Hx).
  - destruct (bmul_big_fam x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
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

Lemma bslt_bexpΩ : forall a b, bslt a b -> bslt (bexpΩ a) (bexpΩ b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH].
  - eapply bslt_bsub_l; [ apply bsub_bexpΩ, Hj | ].
    destruct (bexpΩ_big_s b j (inr tt)) as [t Ht].
    apply (bslt_big _ _ t 2). rewrite Ht.
    change (bslt (bexpΩ (bsmallSz b j)) (bmul (bexpΩ (bsmallSz b j)) (embed 2))).
    apply bslt_two, bpos_bexpΩ.
  - destruct (bexpΩ_big_b b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
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

(** ** The Bachmann–Howard ordinal *)

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

(** φ_{ε_{Ω+1}} is a normal function. *)
Theorem bphi_εΩ1_normal f : normal_function f -> normal_function (bphi f bεΩ1).
Proof.
  intro Hf. apply bcanon_normal; auto using bcanon_bεΩ1.
Qed.

(** The Bachmann–Howard ordinal, defined via the provably normal
    hierarchy @bphi@ (recall that @bphi T@ corresponds to φ_{1+T}, and
    1 + ε_{Ω+1} = ε_{Ω+1}). *)
Definition BachmannHoward : Ord := bphi powOmega bεΩ1 0.

Lemma BachmannHoward_complete : complete BachmannHoward.
Proof.
  unfold BachmannHoward.
  apply normal_complete; auto using zero_complete.
  apply bphi_εΩ1_normal, powOmega_normal.
Qed.

(** Every canonical tree up to ε_{Ω+1} gives a normal function. *)
Corollary bphi_canonical_normal f : normal_function f ->
  forall ξ ζ, normal_function (bphi f (bmul (bexpΩ (embed ζ)) (embed ξ))) /\
              normal_function (bphi f (bexpΩ bOmega)).
Proof.
  intros Hf ξ ζ. split; apply bcanon_normal; auto.
  - apply bcanon_bmul; auto using bcanon_embed, bpos_bexpΩ.
    apply bcanon_bexpΩ, bcanon_embed.
  - apply bcanon_bexpΩ, bcanon_Ω.
Qed.
