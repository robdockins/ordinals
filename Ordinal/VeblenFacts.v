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


Lemma onePlus_finite_succ m : 
  1 + natOrdSize m ≈ succOrd (natOrdSize m).
Proof.
  induction m; simpl.
  rewrite addOrd_zero_r. auto with ord.
  rewrite addOrd_succ.
  rewrite IHm.
  reflexivity.
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
      destruct (complete_zeroDec (ord A f)); auto.
      * eapply ord_le_lt_trans.
        apply veblen_monotone_first.
        intros; apply addOrd_monotone; auto with ord.
        apply H1.
        eapply ord_lt_le_trans.
        apply veblen_increasing0.
        apply onePlus_normal. apply H0.
        apply (index_lt (ord X g) i).
        apply veblen_monotone_first; auto with ord.
        intros; apply addOrd_monotone; auto with ord.
      * apply veblen_increasing_nonzero; auto.
        apply onePlus_normal.
        apply (index_lt (ord X g) i).
      * apply H0.
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

Lemma veblen_subterm1_nonzero f (Hf:normal_function f) :
  forall a b,
    complete a ->
    complete b ->
    0 < b ->
    a < veblen f a b.
Proof.
  intros.
  apply ord_le_lt_trans with (veblen f a 0).
  apply (normal_inflationary (fun i => veblen f i 0)); auto.
  apply veblen_first_normal; auto.
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


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Lemma veblen_decompose (EM:excluded_middle) f (Hf:normal_function f) :
  forall x
    (Hlim : limitOrdinal x),
    x < veblen f x 0 ->
    f x ≤ x ->
    exists a b, x ≈ veblen f a b /\ 0 < a /\ a < x /\ b < x.
Proof.
  induction x as [x Hx] using ordinal_induction; intros Hlim Hx1 Hx2.
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
  { destruct (classical.order_total EM (veblen f a b) x) as [H|H]; auto.
    exfalso.
    rewrite veblen_unroll in H.
    apply lub_lt in H.
    destruct H.
    - apply (ord_lt_irreflexive x).
      apply ord_lt_le_trans with (f b); auto.
      transitivity (f x); auto.
      apply normal_monotone; auto.
      intuition.

    - case_eq a; intros A g Hg.
      rewrite Hg in H. simpl in H.
      apply sup_lt in H.
      destruct H as [i H].

      unfold fixOrd in H.
      apply sup_lt in H.
      destruct H as [n ?].
      apply (ord_lt_irreflexive x).
      eapply ord_lt_le_trans. apply H.
      clear H.
      induction n; simpl.
      * rewrite ord_le_unfold; simpl; intro q.
        destruct (classical.order_total EM x (veblen f (ord A g) (b q))) as [H|H]; auto. exfalso.
        rewrite <- Hg in H.
        assert (Hbq : b <= b q).
        { apply Hbleast; split; auto.
          transitivity b; auto with ord. }
        elim (ord_lt_irreflexive b).
        rewrite Hbq at 1.
        apply index_lt.

      * transitivity (veblen f (g i) x).
        apply veblen_monotone; auto.

        clear n IHn.
        destruct (classical.order_total EM (veblen f (g i) x) x) as [H|H]; auto. exfalso.
        assert (Hai : a <= g i).
        { apply Hleast.
          split.
          - destruct (classical.order_total EM (g i) 0); auto.
            elim (ord_lt_irreflexive x).
            apply ord_lt_le_trans with (veblen f (g i) x); auto.
            transitivity (veblen f 0 x).
            apply veblen_monotone_first; auto.
            rewrite veblen_zero; auto.
          - assert (Hxsup1 : x ≈ supOrd (fun i => x i)).
            { destruct x as [X h].
              apply ascending_sup_lim.
              destruct Hlim; auto.
            }
            assert (Hxsup2 : veblen f (g i) x ≤ veblen f (g i) (supOrd (fun i : x => x i))).
            { apply veblen_monotone; auto. apply Hxsup1. }
            assert (Hxsup3 : veblen f (g i) (supOrd (fun j : x => x j)) <=
                    supOrd (fun j => veblen f (g i) (x j))).
            { assert (Hx0 : x > 0).
              { rewrite <- Hx2. apply normal_nonzero; auto. }
              rewrite ord_lt_unfold in Hx0. destruct Hx0; auto.
              apply veblen_continuous; auto.
              apply classical.ord_complete; auto.
              apply classical.ord_directed; auto.
              intros; apply classical.ord_complete; auto. }
            rewrite Hxsup2 in H.
            rewrite Hxsup3 in H.
            apply sup_lt in H.
            destruct H as [j Hj].
            exists (x j); split; auto with ord. }
        apply (ord_lt_irreflexive a).
        rewrite Hai at 1.
        rewrite Hg.
        apply (index_lt (ord A g) i). }

  assert (Hax : a < x).
  { destruct (classical.order_total EM x a); auto. exfalso.
    elim (ord_lt_irreflexive x).
    apply ord_lt_le_trans with (veblen f x 0); auto.
    transitivity (veblen f a 0).
    apply veblen_monotone_first; auto.
    rewrite <- Hle.
    apply veblen_monotone; auto with ord.
  }

  exists a, b; intuition.
  split; auto.
Qed.
