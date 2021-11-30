Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import ClassicalFacts.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Classical.

Record normal_function (f:Ord -> Ord) :=
  NormalFunction
  { normal_monotone   : forall x y, x ≤ y -> f x ≤ f y
  ; normal_increasing : forall x y, x < y -> f x < f y
  ; normal_continuous : strongly_continuous f
  }.

Lemma normal_inflationary (f:Ord -> Ord) :
  normal_function f ->
  forall x, x <= f x.
Proof.
  intro H. apply increasing_inflationary. apply normal_increasing. auto.
Qed.

(** * Fixpoints of normal functions *)
Section normal_fixpoints.
  Variable f : Ord -> Ord.

  Definition iter_f (base:Ord) : nat -> Ord :=
    fix iter_f (n:nat) : Ord :=
      match n with
      | 0 => base
      | S n' => f (iter_f n')
      end.

  Definition normal_fix (base:Ord) : Ord := supOrd (iter_f base).

  Lemma normal_fix_monotone :
     (forall x y, x <= y -> f x <= f y) ->
     forall x y, x <= y -> normal_fix x <= normal_fix y.
  Proof.
    unfold normal_fix; intros.
    apply sup_least. intro n.
    eapply ord_le_trans with (iter_f y n); [ | apply sup_le ].
    induction n; simpl; auto.
  Qed.

  Lemma normal_fix_continuous :
     (forall x y, x <= y -> f x <= f y) ->
    strongly_continuous f ->
    strongly_continuous normal_fix.
  Proof.
    red; simpl; intros Hf1 Hf2 A g a0.
    unfold normal_fix at 1.
    apply sup_least. intro i.
    apply ord_le_trans with (supOrd (fun a => iter_f (g a) i)).
    - induction i.
      + simpl.
        reflexivity.
      + simpl.
        eapply ord_le_trans.
        * apply Hf1. apply IHi.
        * apply Hf2; auto.
    - apply sup_least. intro a.
      rewrite <- (sup_le _ _ a).
      unfold normal_fix.
      apply sup_le.
  Qed.

  Hypothesis Hnormal : normal_function f.

  Lemma normal_prefixpoint : forall base, f (normal_fix base) ≤ normal_fix base.
  Proof.
    intros.
    apply ord_le_trans with (supOrd (fun i => f (iter_f base i))).
    - apply (normal_continuous _ Hnormal nat (iter_f base) 0%nat).
    - apply sup_least. intro i.
      unfold normal_fix.
      apply (sup_le _ (iter_f base) (S i)).
  Qed.

  Lemma normal_fixpoint : forall base, normal_fix base ≈ f (normal_fix base).
  Proof.
    intros; split.
    - apply normal_inflationary; auto.
    - apply normal_prefixpoint.
  Qed.

  Lemma normal_fix_above : forall base, base ≤ normal_fix base.
  Proof.
    intros.
    unfold normal_fix.
    apply (sup_le _ (iter_f base) 0%nat).
  Qed.

  Lemma normal_fix_least : forall base z, base ≤ z -> f z ≤ z -> normal_fix base ≤ z.
  Proof.
    intros.
    unfold normal_fix.
    apply sup_least.
    intro i; induction i; simpl; auto.
    apply ord_le_trans with (f z); auto.
    apply normal_monotone; auto.
  Qed.

  Lemma normal_lub x y :
    f (x ⊔ y) ≤ f x ⊔ f y.
  Proof.
    apply ord_le_trans with (f (supOrd (fun b:bool => if b then x else y))).
    - apply normal_monotone; auto.
      apply lub_least.
      + apply (sup_le bool (fun b => if b then x else y) true).
      + apply (sup_le bool (fun b => if b then x else y) false).
    - eapply ord_le_trans; [ apply normal_continuous; auto; exact false |].
      apply sup_least.
      intros [|]; [ apply lub_le1 | apply lub_le2 ].
  Qed.
End normal_fixpoints.

Add Parametric Morphism f (Hf:normal_function f) : (normal_fix f)
  with signature ord_le ++> ord_le as normal_fix_le_mor.
Proof.
  apply normal_fix_monotone; auto.
  apply normal_monotone; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (normal_fix f)
  with signature ord_eq ==> ord_eq as normal_fix_eq_mor.
Proof.
  unfold ord_eq; intuition; apply normal_fix_monotone; auto;
      apply normal_monotone; auto.
Qed.

Lemma iter_f_monotone_func g h n :
  (forall x, g x ≤ h x) ->
  (forall x y, x ≤ y -> h x ≤ h y) ->
  forall x, iter_f g x n ≤ iter_f h x n.
Proof.
  intros Hg Hh.
  induction n; intros; simpl.
  - reflexivity.
  - etransitivity.
    apply Hg.
    apply Hh.
    auto.
Qed.


Definition powOmega (x:Ord) : Ord := expOrd ω x.

Lemma omega_gt1 : 1 < ω.
Proof.
  rewrite ord_lt_unfold.
  exists 1%nat. simpl.
  apply ord_le_refl.
Qed.

Lemma powOmega_increasing : forall x y, x < y -> powOmega x < powOmega y.
Proof.
  intros.
  apply expOrd_increasing; auto.
  apply omega_gt1.
Qed.

Lemma powOmega_normal : normal_function powOmega.
Proof.
  apply NormalFunction.
  + apply expOrd_monotone.
  + apply powOmega_increasing.
  + red; intros A f a0; apply (expOrd_continuous ω omega_gt1 A f a0).
Qed.


Definition enum_fixpoints (f:Ord -> Ord) : Ord -> Ord :=
  fix rec (x:Ord) : Ord :=
  match x with
  | ord B g => normal_fix f (ord B (fun b => rec (g b)))
  end.

Lemma enum_are_fixpoints f :
  normal_function f ->
  forall x, enum_fixpoints f x ≈ f (enum_fixpoints f x).
Proof.
  intros.
  destruct x; simpl.
  apply normal_fixpoint; auto.
Qed.

Lemma enum_fixpoints_zero f :
  normal_function f ->
  enum_fixpoints f zeroOrd ≈ normal_fix f zeroOrd.
Proof.
  simpl.
  split; apply normal_fix_monotone; auto.
  - apply normal_monotone; auto.
  - rewrite ord_le_unfold; simpl; intuition.
  - apply normal_monotone; auto.
  - rewrite ord_le_unfold; simpl; intuition.
Qed.

Lemma enum_fixpoints_succ f x :
  enum_fixpoints f (succOrd x) ≈ normal_fix f (succOrd (enum_fixpoints f x)).
Proof.
  simpl; intros. reflexivity.
Qed.

Lemma enum_fixpoints_monotone_both f :
  normal_function f ->
  (forall x y,
      (x ≤ y -> enum_fixpoints f x ≤ enum_fixpoints f y) /\
      (x < y -> enum_fixpoints f x < enum_fixpoints f y)).
Proof.
  intros Hf x.
  induction x as [B g Hx].
  induction y as [C h Hy].
  simpl; intuition.
  - apply normal_fix_least; auto.
    rewrite ord_le_unfold; simpl; intros.
    rewrite ord_le_unfold in H.
    specialize (H a). simpl in H.
    apply (Hx a (ord C h)); auto.
    apply normal_prefixpoint; auto.
  - rewrite ord_lt_unfold in H.
    destruct H as [i ?].
    simpl in H.
    apply Hy in H.
    simpl in H.
    eapply ord_lt_le_trans; [| apply normal_fix_above ].
    rewrite ord_lt_unfold. exists i. simpl.
    auto.
Qed.

Lemma enum_fixpoints_increasing f :
  normal_function f ->
  (forall x y, x < y -> enum_fixpoints f x < enum_fixpoints f y).
Proof.
  intros; apply enum_fixpoints_monotone_both; auto.
Qed.

Lemma enum_fixpoints_monotone f :
  normal_function f ->
  (forall x y, x ≤ y -> enum_fixpoints f x ≤ enum_fixpoints f y).
Proof.
  intros; apply enum_fixpoints_monotone_both; auto.
Qed.

Lemma enum_fixpoints_cont f :
  normal_function f ->
  strongly_continuous (enum_fixpoints f).
Proof.
  repeat intro.
  simpl.
  apply normal_fix_least; auto.
  rewrite ord_le_unfold.
  simpl.
  intros [a i]. simpl.
  rewrite <- (sup_le _ _ a).
  apply enum_fixpoints_increasing; auto with ord.
  rewrite (normal_continuous f H A (fun i => enum_fixpoints f (f0 i)) a0).
  apply sup_least. simpl; intros.
  rewrite <- enum_are_fixpoints; auto.
  rewrite <- (sup_le _ _ a).
  auto with ord.
Qed.

Lemma enum_fixpoints_normal f :
  normal_function f ->
  normal_function (enum_fixpoints f).
Proof.
  intros; constructor.
  - apply enum_fixpoints_monotone; auto.
  - apply enum_fixpoints_increasing; auto.
  - apply enum_fixpoints_cont; auto.
Qed.

Lemma enum_least f :
  normal_function f ->
  forall (x z:Ord),
    f z ≤ z ->
    (forall x', x' < x -> enum_fixpoints f x' < z) ->
    enum_fixpoints f x ≤ z.
Proof.
  intro Hf.
  induction x as [B g Hx]. simpl; intros.
  apply normal_fix_least; auto.
  rewrite ord_le_unfold; simpl; intros.
  apply H0.
  apply limit_lt.
Qed.

Lemma enum_fixpoints_func_mono f g
      (Hf: normal_function f)
      (Hg: normal_function g) :
  (forall x, f x ≤ g x) ->
  (forall x, enum_fixpoints f x ≤ enum_fixpoints g x).
Proof.
  intros.
  induction x as [A q Hx]; simpl.
  apply normal_fix_least; auto.
  - rewrite ord_le_unfold. simpl; intro a.
    rewrite <- (normal_fix_above).
    rewrite ord_lt_unfold. simpl. exists a.
    auto.
  - rewrite H.
    apply normal_prefixpoint; auto.
Qed.

Lemma enum_fixpoints_strictly_inflationary f :
  normal_function f ->
  forall x, x < f x -> x < enum_fixpoints f x.
Proof.
  intros.
  apply ord_lt_le_trans with (f x); auto.
  rewrite enum_are_fixpoints; auto.
  apply normal_monotone; auto.
  apply normal_inflationary. apply enum_fixpoints_normal; auto.
Qed.


Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_le ++> ord_le  as enum_fixpoint_le_mor.
Proof.
  apply enum_fixpoints_monotone; auto.
Qed.

Add Parametric Morphism f (Hf:normal_function f) : (enum_fixpoints f)
  with signature ord_eq ==> ord_eq  as enum_fixpoint_eq_mor.
Proof.
  unfold ord_eq; intuition; apply enum_fixpoints_monotone; auto.
Qed.

Definition ε (x:Ord) := enum_fixpoints powOmega x.

Lemma epsilon_fixpoint x : ε x ≈ expOrd ω (ε x).
Proof.
  intros. unfold ε. apply enum_are_fixpoints.
  apply powOmega_normal.
Qed.


Section veblen.
  Variable f : Ord -> Ord.
  Hypothesis f_normal : normal_function f.
  Hypothesis f_zero : zeroOrd < f zeroOrd.

  Fixpoint veblen (β:Ord) : Ord -> Ord :=
    fix inner (y:Ord) : Ord :=
      match β, y with
      | ord A g, ord X h =>
        f (ord X h) ⊔ supOrd (fun a => normal_fix (veblen (g a)) (ord X (fun x => inner (h x))))
      end.

  Lemma veblen_unroll (β:Ord) (y:Ord) :
    veblen β y = f y ⊔ boundedSup β (fun α => normal_fix (veblen α) (limOrd (fun x => veblen β (y x)))).
  Proof.
    destruct β; destruct y; reflexivity.
  Qed.

  Global Opaque veblen.

  Lemma veblen_unroll_nonzero (β:Ord) (y:Ord) :
    zeroOrd < β -> veblen β y ≈ boundedSup β (fun α => normal_fix (veblen α) (limOrd (fun x => veblen β (y x)))).
  Proof.
    destruct β as [B g].
    intros; split.
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb]. simpl in *.
    - rewrite veblen_unroll.
      apply lub_least.
      + simpl.
        rewrite <- (sup_le _ _ b).
        unfold normal_fix.
        rewrite <- (sup_le _ _ 1%nat).
        simpl.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        destruct y as [Y h]. simpl.
        rewrite ord_le_unfold.
        simpl; intro q.
        rewrite ord_lt_unfold. simpl.
        exists q.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_inflationary; auto.
      + reflexivity.
    - rewrite veblen_unroll.
      apply lub_le2.
  Qed.

  Lemma veblen_monotone (β:Ord) : forall x y, x ≤ y -> veblen β x ≤ veblen β y.
  Proof.
    induction β as [A g Hind]; simpl.
    intros x y; revert x.
    induction y as [X h Hind2]; simpl.
    intros.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite veblen_unroll.
      rewrite <- lub_le1.
      apply normal_monotone; auto.
    - rewrite veblen_unroll.
      rewrite <- lub_le2.
      simpl.
      apply sup_ord_le_morphism.
      red; simpl; intros.
      apply normal_fix_monotone.
      apply Hind.
      apply limit_least.
      intro i.
      rewrite ord_le_unfold in H.
      generalize (H i).
      intro Hj.
      rewrite ord_lt_unfold in Hj.
      destruct Hj as [j Hj].
      apply ord_le_lt_trans with (veblen (ord A g) (h j)).
      + apply Hind2; auto.
      + rewrite ord_lt_unfold.
        exists j. simpl.
        reflexivity.
  Qed.

  Lemma veblen_monotone_first β : forall α x, α ≤ β -> veblen α x ≤ veblen β x.
  Proof.
    induction β as [β Hβ] using ordinal_induction.
    intros a x.
    revert a.
    induction x as [x Hx] using ordinal_induction.
    intros.
    rewrite (veblen_unroll a).
    rewrite (veblen_unroll β).
    apply lub_least; [ apply lub_le1 | rewrite <- lub_le2 ].
    apply boundedSup_least. intros c Hc.
    destruct β as [B g].
    simpl.
    assert (Hc2 : c < ord B g).
    apply ord_lt_le_trans with a; auto.
    rewrite ord_lt_unfold in Hc2.
    destruct  Hc2 as [i Hi].
    rewrite <- (sup_le _ _ i).
    simpl in *.
    transitivity (normal_fix (veblen c) (limOrd (fun i => veblen (ord B g) (x i)))).
    apply normal_fix_monotone.
    apply veblen_monotone.
    rewrite ord_le_unfold. simpl; intros.
    rewrite ord_lt_unfold. simpl. exists a0.
    apply Hx; auto.
    apply index_lt.
    unfold normal_fix.
    apply sup_ord_le_morphism.
    hnf; simpl; intro n.
    apply iter_f_monotone_func; intros; auto.
    apply Hβ.
    apply (index_lt (ord B g)). auto.
    apply veblen_monotone; auto.
  Qed.

  Lemma veblen_inflationary (β:Ord) : forall x, x ≤ veblen β x.
  Proof.
    intro x.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply normal_inflationary. auto.
  Qed.

  Lemma veblen_increasing0 : forall x y, x < y -> veblen zeroOrd x < veblen zeroOrd y.
  Proof.
    intros.
    apply ord_le_lt_trans with (f x).
    { rewrite veblen_unroll.
      apply lub_least; auto with ord.
      apply boundedSup_least. simpl; intros.
      elim (ord_lt_irreflexive zeroOrd).
      apply ord_le_lt_trans with x0; auto.
      apply zero_least. }
    apply ord_lt_le_trans with (f y).
    apply normal_increasing; auto.
    rewrite veblen_unroll.
    apply lub_le1.
  Qed.

  Lemma veblen_increasing_nonzero (β:Ord) : zeroOrd < β -> forall x y, x < y -> veblen β x < veblen β y.
  Proof.
    intros.
    rewrite (veblen_unroll β y).
    rewrite <- lub_le2.
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb].
    destruct β as [B g]. simpl.
    rewrite <- (sup_le _ _ b).
    unfold normal_fix.
    rewrite <- (sup_le _ _ 0%nat).
    simpl.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [q Hq].
    rewrite ord_lt_unfold. simpl.
    exists q.
    apply veblen_monotone. auto.
  Qed.

  Hypothesis Hzero_dec : forall x, x <= zeroOrd \/ zeroOrd < x.

  Lemma veblen_increasing (β:Ord) : forall x y, x < y -> veblen β x < veblen β y.
  Proof.
    destruct (Hzero_dec β).
    - intros.
      apply ord_le_lt_trans with (veblen zeroOrd x).
      apply veblen_monotone_first; auto.
      apply ord_lt_le_trans with (veblen zeroOrd y).
      apply veblen_increasing0; auto.
      apply veblen_monotone_first; auto.
      apply zero_least.
    - intros. apply veblen_increasing_nonzero; auto.
  Qed.

  Lemma veblen_lt_lemma β : zeroOrd < β -> forall x q,
     q < veblen β x ->
     exists a, a < β /\ exists n,
         q < iter_f (veblen a) (limOrd (fun i => veblen β (x i))) n.
  Proof.
    intros.
    rewrite veblen_unroll_nonzero in H0; auto.
    destruct β as [B g]. simpl in H0.
    rewrite ord_lt_unfold in H0.
    simpl in H0.
    destruct H0 as [[b [n z]] Hq].
    simpl in *.
    exists (g b). split; [ apply (index_lt (ord B g)) | ].
    exists n.
    rewrite ord_lt_unfold. simpl. exists z. auto.
  Qed.

  Lemma veblen_fixpoints_aux (β:Ord) (Hcomplete : complete β) :
      (forall y, y < β -> complete y -> strongly_continuous (veblen y)) ->
      forall α x, α < β -> complete α -> veblen α (veblen β x) ≤ veblen β x.
  Proof.
    intros Hcont a x H Hcomplete'.
    rewrite (veblen_unroll a).
    apply lub_least.
    - transitivity (f (boundedSup β (fun α => normal_fix (veblen α) (limOrd (fun i => veblen β (x i)))))).
      apply normal_monotone; auto.
      rewrite (veblen_unroll_nonzero); auto. reflexivity.
      apply ord_le_lt_trans with a; auto. apply zero_least.
      rewrite (veblen_unroll_nonzero); auto.
      destruct β as [B g]. simpl.
      rewrite ord_lt_unfold in H.
      destruct H as [b Hb].
      rewrite (normal_continuous f f_normal B _ b).
      apply sup_least; intro i.
      rewrite <- (sup_le _ _ i).
      transitivity (veblen (g i)
                           (normal_fix (veblen (g i))
                                       (limOrd (fun i0 : x => veblen (ord B g) (x i0))))).
      rewrite (veblen_unroll (g i)).
      apply lub_le1.
      apply normal_prefixpoint.
      { constructor.
      + apply veblen_monotone.
      + apply veblen_increasing.
      + apply Hcont. apply (index_lt (ord B g)).
        destruct Hcomplete as [?[??]]; auto.
      }

      apply ord_le_lt_trans with a; auto. apply zero_least.

    - destruct a as [A g]. simpl.
      apply sup_least. intro y.
      rewrite (veblen_unroll β) at 2.
      rewrite <- lub_le2.
      unfold normal_fix.
      apply sup_least.
      intro i.
      simpl.
      induction i; simpl.
      + apply limit_least. intro q.
        destruct (veblen_lt_lemma β) with x q as [a' [Ha' [n Hn]]].
        apply ord_le_lt_trans with (ord A g); auto. apply zero_least.
        apply index_lt.
        assert (exists a2, a2 < β /\ ord A g <= a2 /\ a' <= a2).
        { destruct β as [B h].
          simpl in Hcomplete.
          destruct Hcomplete as [Hc1 _].
          rewrite ord_lt_unfold in H.
          destruct H as [b1 Hb1].
          rewrite ord_lt_unfold in Ha'.
          destruct Ha' as [b2 Hb2].
          destruct (Hc1 b1 b2) as [b' [??]].
          exists (h b').
          split.
          apply (index_lt (ord B h)).
          split.
          simpl in *.
          transitivity (h b1); auto.
          transitivity (h b2); auto.
        }
        destruct H0 as [a2 [?[??]]].
        apply ord_lt_le_trans with (iter_f (veblen a2) (limOrd (fun i => veblen β (x i))) (S n)).
        simpl.
        apply ord_lt_le_trans with (veblen (ord A g) (iter_f (veblen a2) (limOrd (fun i => veblen β (x i))) n)).
        apply veblen_increasing_nonzero; auto.
        apply ord_le_lt_trans with (g y); auto. apply zero_least.
        apply (index_lt (ord A g)).
        eapply ord_lt_le_trans; [ apply Hn | ].
        apply iter_f_monotone_func; intros;
          [ apply veblen_monotone_first; auto
          | apply veblen_monotone; auto ].
        apply veblen_monotone_first; auto.
        transitivity (supOrd (iter_f (veblen a2) (limOrd (fun x0 : x => veblen β (x x0))))).
        apply sup_le.
        rewrite <- boundedSup_le.
        reflexivity.
        intros.
        { apply sup_ord_le_morphism.
          hnf; simpl; intros.
          apply iter_f_monotone_func; intros.
          - apply veblen_monotone_first; auto.
          - apply veblen_monotone; auto.
        }
        auto.
      + transitivity
          (veblen (g y) (boundedSup β
            (fun α : Ord =>
             supOrd
               (iter_f (veblen α) (limOrd (fun x0 : x => veblen β (x x0))))))).
        apply veblen_monotone; auto.
        destruct β as [B h].
        simpl.
        rewrite ord_lt_unfold in H.
        destruct H as [b Hb].
        simpl in *.
        assert (Hy' : g y < ord B h).
        { transitivity (ord A g) ; auto.
          apply (index_lt (ord A g)).
          rewrite ord_lt_unfold. exists b. auto.
        }
        assert (Hcy: complete (g y)).
        { destruct Hcomplete' as [?[??]]; auto. }
        rewrite (Hcont (g y) Hy' Hcy B _ b).
        apply sup_least.
        intro b'.
        assert (exists b2, h b <= h b2 /\ h b' <= h b2).
        { destruct Hcomplete as [Hc ?].
          destruct (Hc b b'); auto.
        }
        destruct H as [b2 [??]].
        rewrite <- (sup_le _ _ b2).
        rewrite (Hcont (g y) Hy' Hcy nat _ 0%nat).
        apply sup_least.
        simpl; intro j.
        rewrite <- (sup_le _ _ (S j)).
        simpl.
        transitivity (veblen (g y) (iter_f (veblen (h b2)) (limOrd (fun x0 : x => veblen (ord B h) (x x0))) j)).
        apply veblen_monotone.
        { apply iter_f_monotone_func; intros.
          - apply veblen_monotone_first; auto.
          - apply veblen_monotone; auto.
        }
        apply veblen_monotone_first.
        transitivity (ord A g); auto with ord.
        transitivity (h b); auto.
  Qed.

  Lemma veblen_continuous (β:Ord) : complete β -> strongly_continuous (veblen β).
  Proof.
    induction β as [β Hind] using ordinal_induction.
    intro Hc.
    destruct β as [A g]; simpl.
    hnf; intros X h x.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite (normal_continuous f f_normal X h x).
      apply sup_ord_le_morphism.
      hnf; simpl; intros.
      rewrite veblen_unroll.
      rewrite <- lub_le1.
      reflexivity.
    - apply sup_least. intro a.
      apply normal_fix_least.
      + constructor.
        * apply veblen_monotone.
        * apply veblen_increasing.
        * apply Hind. apply (index_lt (ord A g)).
          destruct Hc as [?[??]]. auto.
      + rewrite ord_le_unfold.
        simpl. intros [x' y]. simpl.
        rewrite <- (sup_le _ _ x').
        rewrite (veblen_unroll (ord A g) (h x')).
        rewrite <- lub_le2.
        simpl.
        rewrite <- (sup_le _ _ a).
        rewrite <- (normal_fix_above).
        rewrite ord_lt_unfold. simpl.
        exists y. reflexivity.
      + assert (Hc' : complete (g a)).
        { destruct Hc as [?[??]]; auto. }
        rewrite (Hind (g a) (index_lt (ord A g) a) Hc' X (fun i => veblen (ord A g) (h i)) x).
        apply sup_ord_le_morphism. hnf; simpl. intro x'.
        apply veblen_fixpoints_aux; auto.
        apply (index_lt (ord A g)).
  Qed.

  Lemma veblen_fixpoints :
    forall α β x,
      complete α ->
      complete β ->
      α < β ->
      veblen α (veblen β x) ≤ veblen β x.
  Proof.
    intros.
    apply veblen_fixpoints_aux; auto.
    intros. apply veblen_continuous; auto.
  Qed.

  Lemma veblen_continuous_first : strongly_continuous (fun β => veblen β zeroOrd).
  Proof.
    hnf; intros A g a.
    rewrite veblen_unroll.
    apply lub_least.
    - rewrite <- (sup_le _ _ a).
      rewrite veblen_unroll.
      apply lub_le1.
    - simpl.
      apply sup_least. intros [a' z]. simpl.
      rewrite <- (sup_le A (fun i => veblen (g i) zeroOrd) a').
      rewrite veblen_unroll.
      rewrite <- lub_le2.
      destruct (g a') as [Q q]. simpl in *.
      rewrite <- (sup_le Q _ z).
      apply normal_fix_monotone; auto.
      apply veblen_monotone.
      rewrite ord_le_unfold.
      simpl; intros. elim a0.
  Qed.

  Lemma veblen_increasing_first β :
    forall a, a < β -> veblen a zeroOrd < veblen β zeroOrd.
  Proof.
    intros.
    rewrite (veblen_unroll β).
    rewrite <- lub_le2.
    destruct β as [B g].
    rewrite ord_lt_unfold in H.
    destruct H as [b Hb].
    simpl.
    rewrite <- (sup_le _ _ b).
    apply ord_le_lt_trans with (veblen (g b) zeroOrd).
    apply veblen_monotone_first; auto.
    unfold normal_fix.
    rewrite <- (sup_le _ _ 2%nat). simpl.
    apply veblen_increasing.
    rewrite veblen_unroll.
    rewrite <- lub_le1.
    apply ord_lt_le_trans with (f zeroOrd); auto.
    apply normal_monotone; auto.
    apply zero_least.
  Qed.

  Lemma veblen_normal (β:Ord) : complete β -> normal_function (veblen β).
  Proof.
    constructor.
    - apply veblen_monotone.
    - apply veblen_increasing.
    - apply veblen_continuous; auto.
  Qed.

  Lemma veblen_first_normal : normal_function (fun β => veblen β zeroOrd).
  Proof.
    constructor.
    - intros; apply veblen_monotone_first; auto.
    - intros; apply veblen_increasing_first; auto.
    - apply veblen_continuous_first.
  Qed.

  Lemma veblen_zero : forall x,
    veblen zeroOrd x ≈ f x.
  Proof.
    intro x.
    rewrite veblen_unroll. simpl.
    split.
    - apply lub_least; auto with ord.
      apply sup_least; simpl; intros.
      exfalso; auto.
    - apply lub_le1.
  Qed.

  Lemma veblen_succ : forall a x, complete a ->
    veblen (succOrd a) x ≈ enum_fixpoints (veblen a) x.
  Proof.
    intros a x Ha; induction x as [X g Hind].
    simpl.
    rewrite veblen_unroll.
    split.
    - simpl.
      apply lub_least.
      + unfold  normal_fix.
        rewrite <- (sup_le _ _ 1%nat). simpl.
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; simpl; intro x.
        rewrite ord_lt_unfold; simpl; exists x.
        apply increasing_inflationary.
        apply enum_fixpoints_increasing.
        apply veblen_normal; auto.
      + apply sup_least. intro.
        apply normal_fix_monotone.
        intros; apply veblen_monotone; auto.
        unfold limOrd.
        rewrite ord_le_unfold; simpl; intro x.
        rewrite ord_lt_unfold; simpl; exists x.
        apply Hind.
    - rewrite <- lub_le2.
      simpl.
      rewrite <- (sup_le _ _ tt).
      apply normal_fix_monotone.
      apply veblen_monotone.
      rewrite ord_le_unfold; simpl; intro x.
      rewrite ord_lt_unfold; simpl; exists x.
      apply Hind.
  Qed.

  Lemma veblen_limit_zero :
    forall β, limitOrdinal β -> complete β ->
      veblen β zeroOrd ≈ boundedSup β (fun a => veblen a zeroOrd).
  Proof.
    intros.
    rewrite (veblen_unroll β).
    split.
    - apply lub_least.
      + transitivity (veblen zeroOrd zeroOrd).
        rewrite veblen_zero.
        reflexivity.
        destruct β as [B g]; simpl in *.
        destruct H as [[b] _].
        rewrite <- (sup_le _ _ b).
        apply veblen_monotone_first.
        apply zero_least.
      + destruct β as [B g]; simpl in *.
        apply sup_least; simpl; intro b.
        destruct H as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold normal_fix.
        apply sup_least.
        intro i; induction i; simpl.
        * rewrite ord_le_unfold; simpl; intuition.
        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          apply veblen_monotone. auto.
          destruct H0 as [?[??]]; auto.
          destruct H0 as [?[??]]; auto.
    - rewrite <- lub_le2.
      destruct β as [B g]; simpl in *.
      apply sup_least; simpl; intro i.
      rewrite <- (sup_le _ _ i).
      unfold normal_fix.
      rewrite <- (sup_le _ _ 1%nat).
      simpl.
      apply veblen_monotone.
      apply zero_least.
  Qed.

  Lemma veblen_limit_succ :
    forall β x, limitOrdinal β -> complete β ->
      veblen β (succOrd x) ≈ boundedSup β (fun a => veblen a (succOrd (veblen β x))).
  Proof.
    intros.
    rewrite veblen_unroll.
    split.
    - apply lub_least.
      + destruct β as [B g]; simpl.
        destruct H as [[b] _].
        rewrite <- (sup_le _ _ b).
        rewrite (veblen_unroll (g b)).
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        apply succ_monotone_le.
        apply veblen_inflationary.
      + destruct β as [B g]; simpl.
        apply sup_least; simpl; intro b.
        destruct H as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold normal_fix. apply sup_least.
        intro i; simpl.
        induction i; simpl.
        * rewrite ord_le_unfold; simpl; intro.
          apply ord_lt_le_trans with (succOrd (veblen (ord B g) x)).
          rewrite ord_lt_unfold. exists tt; simpl.
          reflexivity.
          apply veblen_inflationary.
        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          apply veblen_monotone; auto.
          destruct H0 as [?[??]]; auto.
          destruct H0 as [?[??]]; auto.
    - destruct β as [B g]; simpl.
      apply sup_least; intro b.
      rewrite <- lub_le2.
      rewrite <- (sup_le _ _ b).
      unfold normal_fix.
      rewrite <- (sup_le _ _ 1%nat).
      simpl.
      apply veblen_monotone.
      apply succ_least.
      rewrite ord_lt_unfold; exists tt. simpl.
      reflexivity.
  Qed.

  Lemma veblen_limit_limit :
    forall β x, limitOrdinal β -> limitOrdinal x -> complete β ->
      veblen β x ≈ boundedSup β (fun a => veblen a (boundedSup x (fun y => veblen β y))).
  Proof.
    intros.
    destruct β as [B g].
    destruct x as [X h]. simpl.
    rewrite veblen_unroll. simpl.
    split.
    - apply lub_least.
      + destruct H as [[b] H].
        rewrite <- (sup_le _ _ b).
        rewrite veblen_unroll.
        rewrite <- lub_le1.
        apply normal_monotone; auto.
        rewrite ord_le_unfold; simpl; intro x.
        destruct H0 as [_ H0].
        destruct (H0 x) as [x' Hx'].
        rewrite <- (sup_le _ _ x').
        apply ord_lt_le_trans with (h x'); auto.
        apply veblen_inflationary.
      + apply sup_least; intro b.
        destruct H as [_ H].
        destruct (H b) as [b' Hb'].
        rewrite <- (sup_le _ _ b').
        unfold normal_fix.
        apply sup_least.
        simpl; intro i.
        induction i; simpl.
        * rewrite ord_le_unfold; simpl; intro x.
          rewrite <- (veblen_inflationary (g b')).
          destruct H0 as [_ H0].
          destruct (H0 x) as [x' Hx'].
          rewrite <- (sup_le _ _ x').
          apply veblen_increasing_nonzero; auto.
          apply ord_le_lt_trans with (g b'); auto.
          apply zero_least.
          apply (index_lt (ord B g)).
        * rewrite <- (veblen_fixpoints (g b) (g b')); auto.
          apply veblen_monotone; auto.
          destruct H1 as [?[??]]; auto.
          destruct H1 as [?[??]]; auto.
    - rewrite <- lub_le2.
      apply sup_least; intro b.
      rewrite <- (sup_le _ _ b).
      unfold normal_fix.
      rewrite <- (sup_le _ _ 1%nat); simpl.
      apply veblen_monotone.
      apply sup_least. intro x.
      apply ord_lt_le.
      rewrite ord_lt_unfold. simpl. exists x.
      reflexivity.
  Qed.

End veblen.

Definition Γ a := enum_fixpoints (fun b => veblen powOmega b zeroOrd) a.

Theorem Gamma_fixpoints (EM:excluded_middle) : forall a, Γ a ≈ veblen powOmega (Γ a) zeroOrd.
Proof.
  intro a. unfold Γ.
  apply enum_are_fixpoints.
  apply veblen_first_normal; auto.
  - apply powOmega_normal.
  - unfold powOmega; apply expOrd_nonzero.
  - intro; apply (order_total EM).
Qed.

Theorem Gamma_normal (EM:excluded_middle) : normal_function Γ.
Proof.
  unfold Γ.
  apply enum_fixpoints_normal.
  apply veblen_first_normal; auto.
  - apply powOmega_normal.
  - unfold powOmega; apply expOrd_nonzero.
  - intro; apply (order_total EM).
Qed.
