Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.
Import ListNotations.
Open Scope list.
Require Import Lia.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.

Open Scope ord_scope.

Lemma onePlus_complete x : complete x -> complete (1 + x).
Proof.
  intros; apply addOrd_complete; auto.
  apply succ_complete; apply zero_complete.
Qed.


Lemma onePlus_normal : normal_function (addOrd 1).
Proof.
  constructor.
  - intros; apply addOrd_monotone; auto with ord.
  - intros; apply addOrd_increasing; auto.
  - red; intros; apply addOrd_continuous; auto.
  - intros; apply addOrd_complete; auto.
    apply succ_complete. apply zero_complete.
  - intros.
    rewrite <- addOrd_le1.
    apply succ_lt.
Qed.

Lemma veblen_onePlus_complete a x :
  complete a -> complete x -> complete (veblen (addOrd 1) a x).
Proof.
  intros; apply veblen_complete; auto.
  apply onePlus_normal.
  apply onePlus_complete.
Qed.

Lemma onePlus_nonzero : forall x, 0 < 1+x.
Proof.
  intros.
  rewrite <- addOrd_le1. apply succ_lt.
Qed.

Theorem onePlus_least f :
  (forall x y, x < y -> f x < f y) ->
  (forall x, 0 < f x) ->
  forall x, 1+x <= f x.
Proof.
  intros.
  induction x using ordinal_induction.
  rewrite addOrd_unfold.
  apply lub_least.
  apply succ_least; auto.
  apply sup_least. intro i.
  apply succ_least.
  rewrite (H1 (x i)).
  apply H; auto.
  apply index_lt.
  apply index_lt.
Qed.

Theorem onePlus_least_normal f :
    normal_function f ->
    forall x, complete x -> 1+x <= f x.
Proof.
  intros.
  induction x using ordinal_induction.
  rewrite addOrd_unfold.
  apply lub_least.
  apply succ_least.
  apply normal_nonzero; auto.
  apply sup_least. intro i.
  apply succ_least.
  rewrite (H1 (x i)).
  apply normal_increasing; auto.
  apply index_lt.
  apply index_lt.
  apply complete_subord. auto.
Qed.

Lemma onePlus_finite : forall n, natOrdSize n < 1 + natOrdSize n.
Proof.
  induction n; simpl.
  rewrite addOrd_zero_r.
  apply succ_lt.
  rewrite addOrd_succ.
  apply succ_trans.
  apply succ_least.
  auto.
Qed.

Lemma onePlus_veblen f x y :
  normal_function f ->
  x > 0 ->
  complete x ->
  complete y ->
  1 + veblen f x y ≈ veblen f x y.
Proof.
  split; intros.
  - rewrite <- (veblen_fixpoints f H 0 x y) at 2; auto.
    rewrite veblen_zero.
    apply onePlus_least_normal; auto.
    apply veblen_complete; auto.
    apply normal_complete; auto.
    apply zero_complete.
  - apply addOrd_le2.
Qed.

Lemma finite_veblen f x y n :
  normal_function f ->
  x > 0 ->
  complete x ->
  complete y ->
  natOrdSize n + veblen f x y ≈ veblen f x y.
Proof.
  intros. induction n; simpl.
  - rewrite addOrd_zero_l. reflexivity.
  - transitivity
      ((natOrdSize (1+n)%nat + veblen f x y)).
    rewrite natOrdSize_add.
    simpl.
    rewrite addOrd_succ. rewrite addOrd_zero_r.
    reflexivity.
    rewrite natOrdSize_add.
    rewrite <- addOrd_assoc.
    simpl.
    rewrite onePlus_veblen; auto.
Qed.

Lemma finite_veblen_lt f x y n :
  normal_function f ->
  x > 0 ->
  complete x ->
  complete y ->
  natOrdSize n < veblen f x y.
Proof.
  intros.
  apply ord_lt_le_trans with (natOrdSize n + 1).
  rewrite addOrd_succ.
  apply succ_trans. apply addOrd_zero_r.
  rewrite <- (finite_veblen f x y n); auto.
  apply addOrd_monotone; auto with ord.
  apply succ_least. apply veblen_nonzero; auto.
Qed.

Lemma finite_veblen_le f x y n :
  normal_function f ->
  x > 0 ->
  complete x ->
  complete y ->
  natOrdSize n <= veblen f x y.
Proof.
  intros.
  rewrite <- (finite_veblen f x y n); auto.
  apply addOrd_le1.
Qed.


Theorem veblen_onePlus :
  forall a x, complete a -> complete x -> veblen (addOrd 1) a x ≈ expOrd ω a + x.
Proof.
  induction a as [A f Ha]. induction x as [X g Hx].
  split.
  - rewrite veblen_unroll.
    apply lub_least.
    + apply addOrd_monotone; auto with ord.
      apply succ_least.
      apply expOrd_nonzero.
    + unfold boundedSup.
      apply sup_least; intro i.
      apply fixOrd_least.
      * intros; apply veblen_monotone; auto.
        intros; apply addOrd_monotone; auto with ord.
      * rewrite ord_le_unfold. simpl ordSize. intro a.
        simpl in a. rewrite Hx; auto.
        apply addOrd_increasing.
        apply (index_lt (ord X g) a).
        apply H0.
      * rewrite (Ha i).
        rewrite addOrd_assoc.
        apply addOrd_monotone; auto with ord.
        apply expOrd_add_collapse; auto.
        apply (index_lt (ord A f)).
        apply H.
        apply addOrd_complete; auto.
        apply expOrd_complete; auto.
        apply (index_lt _ 0%nat).
        apply omega_complete.

  - unfold addOrd at 1.
    rewrite foldOrd_unfold.
    apply lub_least.
    + rewrite expOrd_unfold.
      apply lub_least.
      { apply succ_least.
        apply veblen_nonzero.
        apply onePlus_normal. }
      apply sup_least; intro i.
      rewrite veblen_unroll.
      rewrite <- lub_le2.
      unfold boundedSup.
      rewrite <- (sup_le _ _ i).
      unfold fixOrd.
      rewrite mulOrd_unfold.
      apply sup_least; intro n.
      rewrite <- (sup_le _ _ (S n)).
      transitivity (expOrd ω (f i) * (S n : ω)).
      simpl.
      rewrite mulOrd_succ.
      reflexivity.
      generalize (S n). clear n.
      induction n.
      * simpl. rewrite mulOrd_zero_r. auto with ord.
      * simpl.
        rewrite mulOrd_succ.
        etransitivity.
        2: { apply veblen_monotone.
             intros; apply addOrd_monotone; auto with ord.
             apply IHn. }
        rewrite Ha.
        ** clear.
           unfold sz. simpl ordSize.
           induction n; simpl natOrdSize.
           rewrite mulOrd_zero_r.
           rewrite addOrd_zero_l.
           rewrite addOrd_zero_r.
           reflexivity.
           rewrite mulOrd_succ.
           rewrite addOrd_assoc.
           rewrite IHn.
           reflexivity.
        ** apply H.
        ** apply mulOrd_complete.
           apply expOrd_complete.
           apply (index_lt _ 0%nat).
           apply omega_complete.
           apply H.
           apply natOrdSize_complete.

    + apply sup_least; intro i. simpl ordSize.
      transitivity (succOrd (expOrd ω (ord A f) + g i)).
      reflexivity.
      rewrite <- Hx; auto.
      apply succ_least.
      apply veblen_increasing; auto with ord.
      apply onePlus_normal.
      apply H0.
Qed.

Lemma veblen_fixpoint_zero f a x :
  normal_function f ->
  0 < a ->
  complete a ->
  complete x ->
  f (veblen f a x) <= veblen f a x.
Proof.
  intros.
  transitivity (veblen f 0 (veblen f a x)).
  rewrite veblen_zero. reflexivity.
  apply veblen_fixpoints; auto.
  apply zero_complete.
Qed.

Lemma veblen_monotone_full f g a x b y :
  (forall x y, x <= y -> g x <= g y) ->
  (forall x, f x <= g x) ->
  a <= b ->
  x <= y ->
  veblen f a x <= veblen g b y.
Proof.
  revert y a x.
  induction b as [b Hb] using ordinal_induction.
  induction y as [y Hy] using ordinal_induction.

  intros.
  rewrite (veblen_unroll f a x).
  rewrite (veblen_unroll g b y).
  apply lub_least.
  - rewrite <- lub_le1.
    transitivity (g x); auto.
  - destruct a as [A r]. simpl.
    apply sup_least; intro ai.
    rewrite <- lub_le2.
    destruct b as [B s]; simpl.
    destruct (ord_le_subord (ord A r) (ord B s) H1 ai) as [bi ?].
    rewrite <- (sup_le _ _ bi).
    unfold fixOrd. apply sup_ord_le_morphism.
    intro m.
    induction m; simpl.
    + rewrite ord_le_unfold; simpl; intro xi.
      destruct (ord_le_subord x y H2 xi) as [yi ?].
      rewrite ord_lt_unfold. simpl. exists yi.
      apply Hy; auto with ord.
    + apply Hb; auto with ord.
Qed.


Lemma veblen_monotone_func f g :
  normal_function f ->
  normal_function g ->
  (forall i, complete i -> f i <= g i) ->
  forall a x, complete a -> complete x ->
    veblen f a x <= veblen g a x.
Proof.
  intros Hf Hg H.
  induction a as [A h Ha].
  induction x as [X k Hx].
  intros.
  do 2 rewrite veblen_unroll.
  apply lub_least.
  - rewrite <- lub_le1. apply H; auto.
  - simpl.
    apply sup_least; intro i.
    rewrite <- lub_le2.
    rewrite <- (sup_le _ _ i).
    unfold fixOrd.
    apply sup_least; intro n.
    rewrite <- (sup_le _ _ n).
    transitivity (iter_f (veblen g (h i)) (limOrd (fun x0 : X => veblen f (ord A h) (k x0))) n).
    { induction n; simpl iter_f.
      reflexivity.
      transitivity
        (veblen g (h i)
                (iter_f (veblen f (h i)) (limOrd (fun x : X => veblen f (ord A h) (k x))) n)).
      apply (Ha i). apply H0.
      apply iter_f_complete.
      apply lim_complete; auto.
      intros; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply H1.
      { red; intros. destruct (complete_directed (ord X k) H1 a1 a2) as [a' [??]].
        exists a'; split.
        apply veblen_monotone; auto.
        apply normal_monotone; auto.
        apply veblen_monotone; auto.
        apply normal_monotone; auto. }
      apply H1.
      intros; apply veblen_complete; auto.
      apply normal_complete; auto.
      apply H0.
      apply veblen_monotone; auto.
      apply normal_monotone; auto. }

    apply iter_f_monotone.
    intros; apply veblen_monotone; auto.
    apply normal_monotone; auto.
    rewrite ord_le_unfold; intro q. simpl.
    rewrite ord_lt_unfold; exists q; simpl.
    apply Hx; auto.
    apply H1.
Qed.

Add Parametric Morphism : (veblen (addOrd 1))
    with signature ord_le ==> ord_le ==> ord_le
      as veblen_onePlus_le_mor.
Proof.
  intros.
  apply veblen_le_mor; auto.
  intros; apply addOrd_monotone; auto with ord.
Qed.

Add Parametric Morphism : (veblen (addOrd 1))
    with signature ord_eq ==> ord_eq ==> ord_eq
      as veblen_onePlus_eq_mor.
Proof.
  intros.
  apply veblen_eq_mor; auto.
  intros; apply addOrd_monotone; auto with ord.
Qed.

Add Parametric Morphism : (veblen (expOrd ω))
    with signature ord_le ==> ord_le ==> ord_le
      as veblen_expOmega_le_mor.
Proof.
  intros.
  apply veblen_le_mor; auto.
  apply expOrd_monotone; auto.
Qed.

Add Parametric Morphism : (veblen (expOrd ω))
    with signature ord_eq ==> ord_eq ==> ord_eq
      as veblen_expOmega_eq_mor.
Proof.
  intros.
  apply veblen_eq_mor; auto.
  apply expOrd_monotone; auto.
Qed.


Local Hint Unfold powOmega : core.
Local Hint Resolve veblen_complete
        onePlus_normal powOmega_normal expOrd_complete addOrd_complete
        omega_complete succ_complete zero_complete
        normal_monotone normal_complete omega_gt0 omega_gt1 : core.


Lemma veblen_additively_closed a b :
  complete a -> complete b ->
  additively_closed (veblen (expOrd ω) a b).
Proof.
  intros. red. intros x y Hx Hy.
  destruct (complete_zeroDec a) as [Ha|Ha]; auto.
  - assert (veblen (expOrd ω) a b ≈ expOrd ω b).
    { split.
      transitivity (veblen (expOrd ω) 0 b).
      apply veblen_monotone_first; auto.
      rewrite veblen_zero. reflexivity.
      rewrite veblen_unroll.
      apply lub_le1. }
    rewrite H1 in Hx, Hy.
    rewrite H1.
    apply expOmega_additively_closed; auto.
  - assert (veblen (expOrd ω) a b ≈ expOrd ω (veblen (expOrd ω) a b)).
    { rewrite <- (veblen_fixpoints _ powOmega_normal 0) at 1; auto.
      rewrite veblen_zero.  reflexivity. }
    rewrite H1 in Hx, Hy.
    rewrite H1.
    apply expOmega_additively_closed; auto.
Qed.

Lemma Γ_additively_closed a :
  complete a -> additively_closed (Γ a).
Proof.
  red; intros.
  rewrite Γ_fixpoints; auto.
  rewrite Γ_fixpoints in H0, H1; auto.
  apply veblen_additively_closed; auto.
  apply normal_complete; auto.
  apply Γ_normal.
Qed.

Lemma veblen_collapse f (Hf:normal_function f) :
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b <= c ->
    veblen f c 0 <= c ->
    veblen f a b <= c.
Proof.
  intros.
  transitivity (veblen f c 0); auto.
  rewrite <- (veblen_fixpoints f Hf a c 0); auto.
  apply veblen_monotone; auto.
  rewrite H3.
  apply (normal_inflationary (fun i => veblen f i 0)); auto.
  apply veblen_first_normal; auto.
Qed.

Lemma veblen_collapse' f (Hf:normal_function f) :
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b < c ->
    veblen f c 0 <= c ->
    veblen f a b < c.
Proof.
  intros.
  apply ord_lt_le_trans with (veblen f c 0); auto.
  rewrite <- (veblen_fixpoints f Hf a c 0); auto.
  apply veblen_increasing; auto.
  apply ord_lt_le_trans with c; auto.
  apply (normal_inflationary (fun i => veblen f i 0)); auto.
  apply veblen_first_normal; auto.
Qed.

Lemma veblen_subterm1 f (Hf:normal_function f) :
  forall a a' b,
    complete a ->
    complete a' ->
    complete b ->
    0 < b ->
    a <= a' ->
    a < veblen f a' b.
Proof.
  intros.
  apply ord_le_lt_trans with (veblen f a' 0).
  transitivity (veblen f a 0).
  apply (normal_inflationary (fun i => veblen f i 0)); auto.
  apply veblen_first_normal; auto.
  apply veblen_monotone_first; auto.
  apply veblen_increasing; auto.
Qed.

Lemma veblen_shrink_lemma f (Hf:normal_function f) :
  forall a b,
    complete a ->
    complete b ->
    a < veblen f a 0 ->
    b < veblen f b 0 ->
    veblen f a b < veblen f (veblen f a b) 0.
Proof.
  intros.
  apply ord_lt_le_trans with
      (veblen f a (veblen f (veblen f a b) 0)).
  - apply veblen_increasing; auto.
    apply ord_lt_le_trans with (veblen f b 0); auto.
    apply veblen_monotone_first; auto.
    apply veblen_inflationary; auto.
  - apply veblen_fixpoints; auto.
    apply ord_lt_le_trans with (veblen f a 0); auto.
    apply veblen_monotone; auto with ord.
Qed.

Lemma veblen_subterm_zero f (Hf:normal_function f) :
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b < veblen f c 0 ->
    veblen f a b < veblen f c 0.
Proof.
  intros.
  apply ord_lt_le_trans with (veblen f a (veblen f c 0)).
  apply veblen_increasing; auto.
  apply veblen_fixpoints; auto.
Qed.

Lemma veblen_subterm1_zero_nest f (Hf:normal_function f) :
  forall a b c,
    complete a ->
    complete b ->
    complete c ->
    a < c ->
    b < c ->
    veblen f a b < veblen f c 0.
Proof.
  intros.
  apply veblen_subterm_zero; auto.
  apply ord_lt_le_trans with c; auto.
  apply (normal_inflationary (fun i => veblen f i 0)); auto.
  apply veblen_first_normal; auto.
Qed.

Lemma veblen_increasing' f (Hf:normal_function f) :
  forall a b c d,
    complete a ->
    complete d ->
    a <= b ->
    c < d ->
    veblen f a c < veblen f b d.
Proof.
  intros.
  apply ord_lt_le_trans with (veblen f a d).
  apply veblen_increasing; auto.
  apply veblen_monotone_first; auto.
Qed.

Lemma ordering_correct_normal:
  forall f x y o,
    normal_function f ->
    complete x ->
    complete y ->
    ordering_correct o x y ->
    ordering_correct o (f x) (f y).
Proof.
  intros. destruct o; simpl in *.
  apply normal_increasing; auto.
  destruct H2; split; apply normal_monotone; auto with ord.
  apply normal_increasing; auto.
Qed.

Lemma veblen_compare_correct f (Hf:normal_function f) :
  forall oab oxy oxVby oVaxy a b x y,
    complete a ->
    complete b ->
    complete x ->
    complete y ->
    ordering_correct oab a b ->
    ordering_correct oxy x y ->
    ordering_correct oxVby x (veblen f b y) ->
    ordering_correct oVaxy (veblen f a x) y ->
    ordering_correct
      (match oab with
      | LT => oxVby
      | EQ => oxy
      | GT => oVaxy
      end) (veblen f a x) (veblen f b y) .
Proof.
  do 8 intro. intros Ha Hb Hx Hy Hoab Hoxy HoxVby HVaxy.
  destruct oab; simpl in *.
  - destruct oxVby; simpl in *.
    + apply ord_lt_le_trans with (veblen f a (veblen f b y)).
      apply veblen_increasing; auto.
      apply veblen_fixpoints; auto.
    + transitivity (veblen f a (veblen f b y)).
      { split; (apply veblen_monotone; [ intros; apply normal_monotone; auto with ord | apply HoxVby ]). }
      apply veblen_fixpoints; auto.
    + apply ord_lt_le_trans with x; auto.
      apply veblen_inflationary; auto.
  - destruct oxy; simpl in *.
    + apply ord_lt_le_trans with (veblen f a y).
      apply veblen_increasing; auto.
      apply veblen_monotone_first; auto.
      apply Hoab.
    + transitivity (veblen f a y).
      split; apply veblen_monotone; auto; apply Hoxy.
      split; apply veblen_monotone_first; auto; apply Hoab.
    + apply ord_le_lt_trans with (veblen f a y).
      apply veblen_monotone_first; auto. apply Hoab.
      apply veblen_increasing; auto.
  - destruct oVaxy; simpl in *.
    + apply ord_lt_le_trans with y; auto.
      apply veblen_inflationary; auto.
    + symmetry.
      transitivity (veblen f b (veblen f a x)).
      split; apply veblen_monotone; auto; apply HVaxy.
      apply veblen_fixpoints; auto.
    + apply ord_lt_le_trans with (veblen f b (veblen f a x)).
      apply veblen_increasing; auto.
      apply veblen_fixpoints; auto.
Qed.



Lemma compose_normal f g :
  normal_function f ->
  normal_function g ->
  normal_function (fun x => f (g x)).
Proof.
  intros. constructor.
  - intros; do 2 (apply normal_monotone; auto).
  - intros. apply normal_increasing; auto.
    apply normal_increasing; auto.
  - hnf; intros A h a Hd Hc.
    transitivity (f (supOrd (fun i => g (h i)))).
    apply normal_monotone; auto.
    apply normal_continuous; auto.
    apply normal_continuous; auto.
    hnf; intros.
    destruct (Hd a1 a2) as [a' [??]].
    exists a'.
    split; apply normal_monotone; auto.
  - intros. apply normal_complete; auto.
  - intros; apply normal_nonzero; auto.
Qed.

Lemma veblen_first_onePlus_normal f :
  normal_function f ->
  normal_function (fun i => veblen f (1+i) 0).
Proof.
  intros.
  apply (compose_normal (fun i => veblen f i 0) (fun i => 1+i)).
  apply veblen_first_normal; auto.
  apply onePlus_normal; auto.
Qed.

Lemma veblen_func_onePlus_lemma f :
  normal_function f ->
  forall a x b y,
    complete a ->
    complete x ->
    complete b ->
    complete y ->
    0 < b ->
    a <= b -> x <= y ->
    veblen (fun i => f (1+i)) a x <= veblen f b y.
Proof.
  intros Hf.
  induction a as [a Hind_a] using ordinal_induction.
  induction x as [x Hind_x] using ordinal_induction.
  intros b y Ha Hx Hb Hy Hb0 Hab Hxy.
  rewrite veblen_unroll at 1.
  apply lub_least.
  - rewrite <- (veblen_fixpoints _ Hf 0); auto.
    rewrite veblen_zero.
    apply normal_monotone; auto.
    rewrite <- onePlus_veblen; auto.
    apply addOrd_monotone; auto with ord.
    rewrite Hxy. apply veblen_inflationary; auto.
  - destruct a as [A fa]; simpl; apply sup_least; intros i.
    apply fixOrd_least; auto with ord.
    + intros; apply veblen_monotone; auto.
    + rewrite ord_le_unfold; simpl; intro ix.
      rewrite (Hind_x (x ix) (index_lt x ix) b (x ix)); auto with ord.
      apply veblen_increasing; auto.
      apply ord_lt_le_trans with x; auto with ord.
      apply complete_subord; auto.
      apply complete_subord; auto.
    + destruct (complete_zeroDec (fa i)); auto.
      * apply Ha.
      * transitivity (veblen (fun i0 : Ord => f (1 + i0)) 0 (veblen f b y)).
        apply veblen_monotone_first; auto with ord.
        rewrite <- (veblen_fixpoints _ Hf 0 b y) at 2; auto.
        rewrite veblen_zero.
        rewrite veblen_zero.
        apply normal_monotone; auto.
        apply onePlus_veblen; auto.
      * rewrite <- (veblen_fixpoints _ Hf (fa i) b y) at 2; auto.
        apply (Hind_a (fa i) (index_lt (ord A fa) i) (veblen f b y) (fa i) (veblen f b y)); auto with ord.
        apply Ha.
        apply Ha.
        apply Ha.
        apply ord_lt_le_trans with (ord A fa); auto with ord.
Qed.

Lemma veblen_func_onePlus f :
  normal_function f ->
  forall a x,
    complete a ->
    complete x ->
    0 < a ->
    veblen (fun i => f (1+i)) a x ≈ veblen f a x.
Proof.
  intros; split.
  apply veblen_func_onePlus_lemma; auto with ord.
  apply veblen_monotone_func; auto.
  apply (compose_normal f (fun i => 1+i)); auto.
  intros; apply normal_monotone; auto.
  apply addOrd_le2.
Qed.


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Lemma veblen_decompose (EM:excluded_middle) f (Hf:normal_function f) :
  forall x
    (Hlim : limitOrdinal x),
    x < veblen f x 0 ->
    f x ≤ x ->
    exists a b, x ≈ veblen f a b /\ 0 < a /\ a < x /\ b < x.
Proof.
  intros x Hlim Hx1 Hx2.

  set (P a := a > 0 /\ exists b, b < x /\ x <= veblen f a b).
  destruct (classical.ord_well_ordered EM P x) as [a [[Ha0 Ha] Hleast]]; auto.
  { red. split. rewrite <- Hx2. apply normal_nonzero; auto.
    exists 0. split; auto with ord. rewrite <- Hx2. apply normal_nonzero; auto. }
  destruct Ha as [b0 Hb0].

  set (Q b := b < x /\ x <= veblen f a b).
  destruct (classical.ord_well_ordered EM Q b0) as [b [[Hb Hab] Hbleast]]; auto.
  unfold P in *.
  unfold Q in *.

  assert (Hle : veblen f a b ≤ x).
  { rewrite veblen_unroll.
    apply lub_least.
    - rewrite <- Hx2.
      apply normal_monotone; auto with ord.
    - apply sup_least. intro i.
      apply normal_fix_least; auto.
      + apply veblen_normal; auto.
        apply classical.ord_complete; auto.
      + apply classical.ord_complete; auto.
      + rewrite ord_le_unfold; simpl; intros.
        destruct (classical.order_total EM x (veblen f a (b a0))) as [H|H]; auto.
        elim (ord_lt_irreflexive b).
        apply ord_le_lt_trans with (b a0); auto with ord.
        apply Hbleast; split; auto with ord.
        apply ord_lt_trans with b; auto with ord.
      + destruct (classical.order_total EM i 0) as [Hi0|Hi0].
        { apply ord_le_trans with (veblen f 0 x).
          apply veblen_monotone_first; auto.
          rewrite veblen_zero. auto. }
        transitivity (veblen f i (boundedSup x (fun i => i))).
        { apply veblen_monotone; auto.
          apply limit_boundedSup; auto. }
        transitivity (supOrd (fun q => veblen f i (x q))).
        { destruct x as [X g]; simpl.
          rewrite ord_lt_unfold in Hb. destruct Hb.
          apply veblen_continuous; auto.
          apply classical.ord_complete; auto.
          apply classical.ord_directed; auto.
          intros; apply classical.ord_complete; auto. }
        apply sup_least; intro q.
        destruct (classical.order_total EM (veblen f i (x q)) x) as [H|H]; auto.
        elim (ord_lt_irreflexive a).
        apply ord_le_lt_trans with i; auto with ord.
        apply Hleast; split; eauto with ord.
  }

  assert (Hax : a < x).
  { destruct (classical.order_total EM x a); auto. exfalso.
    elim (ord_lt_irreflexive x).
    apply ord_lt_le_trans with (veblen f x 0); [ exact Hx1 | ].
    transitivity (veblen f a 0).
    apply veblen_monotone_first; auto.
    rewrite <- Hle.
    apply veblen_monotone; auto with ord.
  }

  exists a, b; intuition.
  split; auto.
Qed.
