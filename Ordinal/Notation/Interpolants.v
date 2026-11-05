From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.

From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Open Scope ord_scope.

Local Set Implicit Arguments.

(** * Interpolants

  An ordinal [z] has interpolants in a notation system [f : A -> Ord]
  (with well-formedness predicate [P]) when everything below [z] is
  bounded by a notation below [z] which itself has interpolants.  With
  excluded middle, interpolants for every notation are equivalent to
  every ordinal below a notation being denoted by a notation
  ([has_interpolants_has_enough_notations]); without it they are a
  constructive substitute, and are preserved by the usual ways of
  building notation systems: sums, fixpoints and Veblen hierarchies.

  The only fact needed about the notation system is that notations
  denote complete ordinals ([f_complete]). *)

Section interpolants.
  Variable A: Type.
  Variable f: A -> Ord.
  Variable P: A -> Prop.
  Hypothesis f_complete: forall a, complete (f a).

  Fixpoint has_interpolants_rec (z:Ord) (H:Acc ord_lt z) : Prop :=
    match H with
    | Acc_intro _ H' =>
        forall (i:Ord), i < z -> exists (y:A) (Hlt: f y < z), P y /\ i <= f y /\ has_interpolants_rec (H' _ Hlt)
    end.

  Lemma has_interpolants_rec_H_irrelevant : forall z H1 H2,
      @has_interpolants_rec z H1 -> @has_interpolants_rec z H2.
  Proof.
    induction z as [z Hindz] using ordinal_induction; simpl; intros H1 H2 H.
    destruct H1; destruct H2; simpl in *; intros i Hi.
    destruct (H i) as [y [Hy1 [Hy2 Hy3]]]; auto.
    exists y, Hy1; intuition.
    eapply Hindz; eauto.
  Qed.

  Lemma has_interpolants_rec_eq_mor : forall x y H1 H2,
      x ≈ y -> @has_interpolants_rec x H1 -> @has_interpolants_rec y H2.
  Proof.
    induction x as [x Hind] using ordinal_induction. intros y H1 H2 Hxy.
    destruct H1; destruct H2. simpl.
    intros Hx i Hi.
    destruct (Hx i) as [z [Hz1 [Hz2 [Hz3 Hz4]]]].
    rewrite Hxy. auto.
    exists z; intuition.
    assert (Hzy: f z < y).
    { generalize Hz1. rewrite Hxy. auto. }
    exists Hzy.
    intuition.
    eapply Hind; eauto with ord.
  Qed.

  Definition has_interpolants (z:Ord) : Prop := has_interpolants_rec (ord_lt_wf z).

  Lemma has_interpolants_unfold (z:Ord) :
    has_interpolants z <-> (forall (i:Ord), i < z -> exists y:A, P y /\ i <= f y /\ f y < z /\ has_interpolants (f y)).
  Proof.
    unfold has_interpolants; intuition.
    - destruct (ord_lt_wf z); simpl in *.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y; intuition.
      eapply has_interpolants_rec_H_irrelevant; eauto.
    - destruct (ord_lt_wf z); simpl in *; intros.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y, Hy3; intuition.
      eapply has_interpolants_rec_H_irrelevant; eauto.
  Qed.


  Global Add Parametric Morphism : has_interpolants with signature
    ord_eq ==> iff as has_interpolants_eq_mor.
  Proof.
    intros.
    unfold has_interpolants; split; apply has_interpolants_rec_eq_mor; auto with ord.
    symmetry. auto.
  Qed.

  Definition has_all_interpolants :=
    forall (a:A), P a -> has_interpolants (f a).

  Definition has_enough_notations :=
    forall (a:A) (x:Ord), P a -> x <= f a -> exists b, P b /\ f b ≈ x.

  Lemma has_enough_notations_has_all_interpolants:
    has_enough_notations -> has_all_interpolants.
  Proof.
    intros H a. induction a as [a Hinda] using (size_induction (ord A f)). intro Ha.
    rewrite has_interpolants_unfold. intros i Hi.
    destruct (H a i) as [x [Hx1 Hx2]]; auto with ord.
    exists x; intuition.
    apply Hx2. rewrite Hx2. auto.
    apply Hinda; auto.
    rewrite Hx2. auto.
  Qed.

  Lemma has_interpolants_has_enough_notations:
    excluded_middle ->
    has_all_interpolants ->
    has_enough_notations.
  Proof.
    intros EM Hinterp a i Ha Hi.

    set (Q:= fun o => exists v:A, P v /\ i <= f v /\ o ≈ f v).
    assert (HP: exists o, Q o).
    { subst Q. exists (f a), a; intuition auto with ord. }
    destruct HP as [o0 Ho0].
    destruct (classical.ord_well_ordered EM Q o0) as [z [Hz1 Hz2]]; auto.
    destruct Hz1 as [v [Hv1[Hv2 Hv3]]].
    exists v; split; auto. split; auto.
    destruct (classical.order_total EM (f v) i); auto.
    specialize (Hinterp v Hv1).
    rewrite has_interpolants_unfold in Hinterp.
    destruct Hinterp with i as [q [Hq1 [Hq2 [Hq3 _]]]]; auto.
    assert (HQq: Q (f q)).
    { hnf. exists q. intuition auto with ord. }
    apply Hz2 in HQq.
    elim (ord_lt_irreflexive z).
    rewrite HQq at 1.
    rewrite Hv3.
    auto.
  Qed.

  Lemma has_interpolants_lub: forall p q,
      has_interpolants p ->
      has_interpolants q ->
      has_interpolants (p ⊔ q).
  Proof.
    intros p q Hp Hq.
    rewrite has_interpolants_unfold in *.
    intros i Hi.
    apply lub_lt in Hi.
    destruct Hi; auto.
    - destruct (Hp i) as [y ?]; auto.
      exists y; intuition auto with ord.
      rewrite <- lub_le1. auto.
    - destruct (Hq i) as [y ?]; auto.
      exists y; intuition auto with ord.
      rewrite <- lub_le2. auto.
  Qed.

  Lemma has_interpolants_sup: forall B g,
      (forall b:B, has_interpolants (g b)) ->
      has_interpolants (supOrd g).
  Proof.
    intros B g Hg.
    rewrite has_interpolants_unfold.
    intros i Hi. apply sup_lt in Hi.
    destruct Hi as [b Hi].
    generalize (Hg b).
    rewrite has_interpolants_unfold.
    intro Hb.
    destruct (Hb i Hi) as [y ?].
    exists y; intuition.
    rewrite <- (sup_le _ _ b); auto.
  Qed.

  Lemma has_interpolants_add: forall add,
      reflects A f P (ORD ==> ORD ==> ORD) addOrd add ->
      forall p q,
        P p ->
        has_interpolants (f p) ->
        has_interpolants q ->
        has_interpolants (f p + q).
  Proof.
    intros add Hadd.
    induction q as [q IHq] using ordinal_induction.
    intros Hp1 Hp2 Hq.
    rewrite addOrd_unfold.
    apply has_interpolants_lub; auto.

    rewrite has_interpolants_unfold.
    simpl; intros i Hi.
    apply sup_lt in Hi.
    destruct Hi as [q' Hi].
    rewrite ord_lt_unfold in Hi. destruct Hi as [[] Hi]. simpl in Hi.
    rewrite has_interpolants_unfold in Hq.
    destruct (Hq q') as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
    exists (add p y).
    destruct Hadd with (f p) p (f y) y as [Hadd1 Hadd2]; intuition auto with ord.
    - rewrite <- Hadd1.
      rewrite Hi.
      apply addOrd_monotone; auto with ord.
    - rewrite <- Hadd1.
      rewrite ord_lt_unfold in Hy3.
      destruct Hy3 as [q'' Hy3].
      rewrite <- (sup_le _ _ q'').
      apply succ_trans.
      apply addOrd_monotone; auto with ord.
    - rewrite <- Hadd1.
      apply IHq; auto with ord.
  Qed.

  Section fix_interpolants.
    Variable g: Ord -> Ord.
    Hypothesis Hg1: forall b, complete b -> complete (g b).
    Hypothesis Hg2: forall b, complete b -> has_interpolants b -> has_interpolants (g b).

    Lemma iter_has_interpolants:
      forall m b,
        complete b ->
        has_interpolants b ->
        has_interpolants (iter_f g b m).
    Proof.
      induction m; simpl; auto with ord.
      intros b Hb1 Hb2.
      apply Hg2.
      apply iter_f_complete; auto.
      apply IHm; auto.
    Qed.

    Lemma fix_has_interpolants:
      forall b,
        complete b ->
        has_interpolants b ->
        has_interpolants (fixOrd g b).
    Proof.
      intros b Hb1 Hb2.
      rewrite has_interpolants_unfold. intros i Hi.
      unfold fixOrd in Hi.
      apply sup_lt in Hi.
      destruct Hi as [m Hi].
      generalize (iter_has_interpolants m b Hb1 Hb2).
      rewrite has_interpolants_unfold. intro H.
      destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
      exists y; intuition.
      unfold fixOrd.
      rewrite <- (sup_le _ _ m).
      auto.
    Qed.

    Hypothesis Hg3: forall x y, x <= y -> g x <= g y.
    Hypothesis Hg4: forall x, complete x -> x <= g x.

    Variable enum_gr: A -> A.
    Hypothesis Hgr: reflects A f P (ORD ==> ORD) (enum_fixpoints g) enum_gr.

    Lemma enum_fix_has_interpolants:
      forall b,
        complete b ->
        has_interpolants b ->
        has_interpolants (enum_fixpoints g b).
    Proof.
      induction b as [b Hindb] using ordinal_induction.
      intros Hb1 Hb2.
      destruct b as [B fb]; simpl.
      apply fix_has_interpolants; auto with ord.
      { apply lim_complete.
        - intros. apply enum_fixpoints_complete; auto with ord.
          apply Hb1.
        - apply (directed_monotone (ord B fb)); auto with ord.
          intros; apply enum_fixpoints_monotone; auto with ord.
        - apply Hb1. }
      rewrite has_interpolants_unfold. intros i Hi.
      rewrite ord_lt_unfold in Hi.
      destruct Hi as [b Hi]; simpl in *.
      rewrite has_interpolants_unfold in Hb2.
      destruct (Hb2 (fb b)) as [br [Hbr1 [Hbr2 [Hbr3 Hbr4]]]]; auto with ord.

      exists (enum_gr br).
      destruct (@Hgr (f br) br) as [??]; [ split; auto with ord | ].
      repeat split; auto.
      - rewrite <- H.
        rewrite Hi.
        apply enum_fixpoints_monotone; auto with ord.
      - rewrite ord_lt_unfold. simpl.
        rewrite ord_lt_unfold in Hbr3.
        destruct Hbr3 as [b' Hbr3].
        exists b'. rewrite <- H.
        apply enum_fixpoints_monotone; auto with ord.
      - rewrite <- H.
        apply Hindb; auto with ord.
    Qed.        
  End fix_interpolants.

  Section onePlus_interpolants.
    Variable zr: A.
    Hypothesis Hzr: reflects A f P ORD 0 zr.

    Variable pr: A -> A.
    Hypothesis Hpr: reflects A f P (ORD ==> ORD) (addOrd 1) pr.

    Lemma onePlus_interpolants:
      forall b, has_interpolants b -> has_interpolants (1+b).
    Proof.
      induction b as [b Hindb] using ordinal_induction. intro Hb.
      rewrite has_interpolants_unfold. intros i Hi.
      rewrite addOrd_unfold in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - rewrite ord_lt_unfold in Hi.
        destruct Hi as [[] Hi]; simpl in *.
        exists zr. destruct Hzr; intuition.
        rewrite Hi; auto with ord.
        rewrite <- H1.
        rewrite <- addOrd_le1.
        auto with ord.
        rewrite has_interpolants_unfold.
        intros i' Hi'.
        rewrite <- H in Hi'.
        rewrite ord_lt_unfold in Hi'.
        destruct Hi' as [[] _].
      - apply sup_lt in Hi.
        destruct Hi as [j Hi].
        rewrite ord_lt_unfold in Hi.
        destruct Hi as [[]  Hi]. simpl in Hi.
        rewrite has_interpolants_unfold in Hb.
        destruct (Hb j) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
        exists (pr y).
        destruct Hpr with (f y) y as [Hpr1 Hpr2]; intuition auto with ord.
        rewrite <- Hpr1.
        rewrite Hi.
        apply addOrd_monotone; auto with ord.
        rewrite <- Hpr1.
        apply addOrd_increasing; auto with ord.
        rewrite <- Hpr1.
        apply Hindb; auto.
    Qed.

  End onePlus_interpolants.

  Section veblen_interpolants.
    Variable g: Ord -> Ord.

    Hypothesis Hg1: normal_function g.
    Hypothesis Hg2: forall b, complete b -> has_interpolants b -> has_interpolants (g b).

    Variable gr : A -> A.
    Hypothesis Hg_reflects: reflects A f P (ORD ==> ORD) g gr.

    Variable vr : A -> A -> A.
    Hypothesis Hvr_reflects: reflects A f P (ORD ==> ORD ==> ORD) (veblen g) vr.

    Lemma veblen_interpolants:
      forall a b,
        P a ->
        has_interpolants (f a) ->
        complete b ->
        has_interpolants b ->
        has_interpolants (veblen g (f a) b).
    Proof.
      induction a as [a Hinda] using (size_induction (ord A f)).
      induction b as [b Hindb] using ordinal_induction.
      intros Ha1 Ha2 Hb1 Hb2. rewrite has_interpolants_unfold. intros i Hi.
      rewrite veblen_unroll in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - specialize (Hg2 b Hb1 Hb2).
        rewrite has_interpolants_unfold in Hg2.
        destruct Hg2 with i as [y [Hy1 [Hy2 Hy3]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        auto.
      - case_eq (f a). intros AA fa HA.
        rewrite HA in Hi. simpl in Hi.
        apply sup_lt in Hi.
        destruct Hi as [j Hi].
        set (b' := limOrd (fun x : b => veblen g (ord AA fa) (b x))).
        assert (Hb' : has_interpolants b').
        { unfold b'. rewrite has_interpolants_unfold.
          intros i0 Hi0.
          rewrite ord_lt_unfold in Hi0. simpl in Hi0.
          destruct Hi0 as [k Hi0].
          rewrite has_interpolants_unfold in Hb2.
          destruct (Hb2 (b k)) as [q [Hq1 [Hq2 [Hq3 Hq4]]]]; auto with ord.
          exists (vr a q).
          destruct Hvr_reflects with (f a) a (f q) q as [Hvr1 Hvr2]; intuition auto with ord.
          rewrite <- Hvr1.
          rewrite Hi0.
          rewrite <- HA.
          apply veblen_monotone; auto with ord.
          rewrite ord_lt_unfold; simpl.
          rewrite ord_lt_unfold in Hq3.
          destruct Hq3 as [k' Hq3].
          exists k'.
          rewrite <- HA.
          rewrite <- Hvr1.
          apply veblen_monotone; auto with ord.
          rewrite <- Hvr1.
          apply Hindb; auto.
 }
        rewrite has_interpolants_unfold in Ha2.
        destruct Ha2 with (i:=fa j) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto with ord.
        rewrite HA. auto with ord.
        assert (Hi' : i < fixOrd (veblen g (f y)) b').
        { eapply ord_lt_le_trans; [ apply Hi |].
          apply fixOrd_monotone_func.
          intros.
          apply veblen_monotone_first; auto with ord.
          intros; apply veblen_monotone; auto with ord. }

        assert (Hfix: has_interpolants (fixOrd (veblen g (f y)) b')).
        { apply fix_has_interpolants; auto.
          + intros. apply normal_complete; auto.
            apply veblen_normal; auto.
          + unfold b'.
            apply lim_complete.
            intros.
            apply veblen_complete; auto.
            apply normal_complete; auto.
            rewrite <- HA.
            apply f_complete.
            apply complete_subord; auto.
            apply directed_monotone; auto.
            intros. apply veblen_monotone; auto with ord.
            destruct b. apply Hb1. }
        rewrite has_interpolants_unfold in Hfix.
        destruct (Hfix i) as [z [Hz1 [Hz2 [Hz3 Hz4]]]]; auto.
        exists z; intuition.
        eapply ord_lt_le_trans; [ apply Hz3 | ].
        rewrite veblen_unroll.
        rewrite <- lub_le2.
        simpl.
        rewrite HA in Hy3.
        rewrite ord_lt_unfold in Hy3.
        destruct Hy3 as [zq Hy3].
        rewrite <- (sup_le AA _ zq).
        apply fixOrd_monotone_func.
        intros. apply veblen_monotone_first; auto with ord.
        intros. apply veblen_monotone; auto with ord.
    Qed.

    Lemma veblen_interpolants_first:
      forall a,
        complete a ->
        has_interpolants a ->
        has_interpolants (veblen g a 0).
    Proof.
      induction a as [a Hinda] using ordinal_induction.
      intros Ha1 Ha2.
      rewrite has_interpolants_unfold. intros i Hi.
      rewrite veblen_unroll in Hi.
      apply lub_lt in Hi.
      destruct Hi as [Hi|Hi].
      - assert (has_interpolants (g 0)).
        { apply Hg2; auto with ord.
          rewrite has_interpolants_unfold.
          intros j Hj. rewrite ord_lt_unfold in Hj.
          destruct Hj as [[] _]. }
        rewrite has_interpolants_unfold in H.
        destruct (H i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll. rewrite <- lub_le1. auto.
      - case_eq a. intros AA fa HA.
        rewrite HA in Hi. simpl in Hi.
        apply sup_lt in Hi.
        destruct Hi as [j Hi].
        rewrite HA in Ha2.
        rewrite has_interpolants_unfold in Ha2.
        destruct (Ha2 (fa j)) as [k [Hk1 [Hk2 [Hk3 Hk4]]]]; auto with ord.
        assert (Hi' : i < fixOrd (veblen g (f k)) 0).
        { eapply ord_lt_le_trans; [ apply Hi |].
          etransitivity; [ apply fixOrd_monotone | apply fixOrd_monotone_func ].
          intros; apply veblen_monotone; auto with ord.
          rewrite ord_le_unfold; simpl; intros [].
          intros; apply veblen_monotone_first; auto with ord.
          intros; apply veblen_monotone; auto with ord. }

        assert (Hfix: has_interpolants (fixOrd (veblen g (f k)) 0)).
        { apply fix_has_interpolants; auto with ord.
          + intros. apply veblen_interpolants; auto.
          + rewrite has_interpolants_unfold.
            intros l Hl.
            rewrite ord_lt_unfold in Hl. destruct Hl as [[] _]. }
        rewrite has_interpolants_unfold in Hfix.
        destruct (Hfix i) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; auto.
        exists y; intuition.
        rewrite veblen_unroll.
        rewrite <- lub_le2.
        simpl.
        rewrite ord_lt_unfold in Hk3.
        destruct Hk3 as [q Hq]. simpl in Hq.
        rewrite <- (sup_le _ _ q).
        eapply ord_lt_le_trans; [ apply Hy3 |].
        etransitivity; [ apply fixOrd_monotone | apply fixOrd_monotone_func ].
        intros; apply veblen_monotone; auto with ord.
        rewrite ord_le_unfold; simpl; intros [].
        intros; apply veblen_monotone_first; auto with ord.
        intros; apply veblen_monotone; auto with ord.
    Qed.

  End veblen_interpolants.

End interpolants.
