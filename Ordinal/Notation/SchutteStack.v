From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Wf.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.

From Ordinal Require Import Notation.CantorDecomposition.

Open Scope ord_scope.


Local Hint Resolve
      schutte_column_normal
      schutte_column_normal_arg
      schutte_column_monotone
      normal_complete
      normal_monotone
      normal_fix_complete
      normal_inflationary
      veblen_complete
      veblen_normal
      veblen_first_normal
      veblen_first_onePlus_normal
      normal_monotone
      onePlus_normal
      powOmega_normal
      addOrd_complete
      addOrd_increasing
      succ_complete
      zero_complete
      natOrdSize_complete
  : core.

Scheme All for list.
Inductive VForm :=
| Z
| N : list VForm -> VForm.

Fixpoint VF_termSize (x:VForm) : nat :=
  match x with
  | Z   => 0%nat
  | N l => 1%nat + fold_right Nat.add 0%nat (map VF_termSize l)
  end.

Definition VF_listSize (xs:list VForm) : nat :=
  fold_right Nat.add 0%nat (map VF_termSize xs).

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | N l => schutte_stack (addOrd 1) (map VF_denote l) 0
  end.

Definition VForm_induction : forall
  (P:VForm -> Prop)
  (HZ: P Z)
  (Hind: forall xs, each P xs -> P (N xs)),
  forall x, P x :=

  fun P HZ Hind =>
  fix outer (x:VForm) : P x :=
    match x as x' return P x' with
    | Z => HZ
    | N xs0 =>
        Hind xs0
          ((fix inner (xs:list VForm) : each P xs :=
              match xs as xs' return each P xs' with
              | nil => I
              | (y::ys) => conj (outer y) (inner ys)
              end
           ) xs0)
    end.

Lemma VForm_complete: forall x:VForm, complete (VF_denote x).
Proof.
  induction x using VForm_induction; auto.
  induction xs; simpl each in *; simpl VF_denote in *; auto with ord.
  apply normal_complete; auto with ord.
  apply schutte_stack_normal; auto with ord.
  { unfold list_complete.
    destruct H as [_ Hxs]. clear -Hxs.
    induction xs; simpl in *; intuition. }
  apply schutte_column_normal; auto with ord.
  destruct H; auto.
Qed.

Lemma VForm_each_complete: forall xs, each complete (map VF_denote xs).
Proof.
  induction xs; simpl; intuition.
  apply VForm_complete.
Qed.

Local Hint Resolve VForm_complete VForm_each_complete: core.

Theorem VForm_bounded : forall x:VForm, VF_denote x < SmallVeblenOrdinal.
Proof.
  intro x.
  induction x using VForm_induction.

  - simpl. apply SVO_nonzero.
  - simpl.
    apply SVO_stack_unreachable'; auto with ord.
    + unfold list_complete; auto.
    + apply SVO_nonzero.
    + unfold schutte_stack_proper.
      induction xs; simpl in *; intuition.
Qed.

Canonical Structure VF := ord VForm VF_denote.

Lemma VForm_le_SVO: SmallVeblenOrdinal <= VF.
Proof.
  rewrite SVO_alt.
  rewrite schutte_column_omega_sup; auto with ord.
  apply sup_least; intro i.
  transitivity (VF_denote (N (N [] :: repeat Z i))).
  - simpl.
    rewrite length_map.
    rewrite repeat_length.
    replace (map VF_denote (repeat Z i)) with (repeat 0 i).
    2:{ induction i; simpl; congruence. }
    rewrite schutte_stack_zeros; auto with ord.
  - apply ord_lt_le.
    auto with ord.
Qed.

Theorem VF_SVO : VF ≈ SmallVeblenOrdinal.
Proof.
  split. 
  - apply limit_least. intro i. apply VForm_bounded.
  - apply VForm_le_SVO.
Qed.

Lemma schutte_stack_base: forall xs f x,
  normal_function f ->
  list_complete xs ->
  f x <= schutte_stack f xs x.
Proof.
  unfold list_complete.
  induction xs; simpl; intuition auto with ord.
  rewrite <- IHxs; auto with ord.
  rewrite schutte_column_unroll.
  rewrite <- lub_le1.
  apply normal_monotone; intuition auto with ord.
Qed.


Lemma schutte_column_collapse :
  forall f (Hf:normal_function f),
  forall n a b c,
    complete n ->
    complete a ->
    complete b ->
    complete c ->
    0 < n ->
    a < c ->
    b <= c ->
    schutte_column f n c 0 <= c ->
    schutte_column f n a b <= c.
Proof.
  intros.
  transitivity (schutte_column f n c 0); auto.
  rewrite <- (schutte_column_fixpoint n c 0 f 0 a); auto with ord.
  rewrite schutte_column0.
  apply normal_monotone; auto with ord.
  transitivity c; auto.
  rewrite addOrd_zero_r.
  apply (normal_inflationary (fun x => schutte_column f n x 0)); auto with ord.
Qed.

Lemma schutte_column_collapse' :
  forall f (Hf:normal_function f),
  forall n a b c,
    complete n ->
    complete a ->
    complete b ->
    complete c ->
    0 < n ->
    a < c ->
    b < c ->
    schutte_column f n c 0 <= c ->
    schutte_column f n a b < c.
Proof.
  intros.
  apply ord_lt_le_trans with (schutte_column f n c 0); auto.
  rewrite <- (schutte_column_fixpoint n c 0 f 0 a); auto with ord.
  rewrite schutte_column0.
  apply normal_increasing; auto with ord.
  apply ord_lt_le_trans with c; auto with ord.
  rewrite addOrd_zero_r.
  apply (normal_inflationary (fun x => schutte_column f n x 0)); auto with ord.
Qed.


Lemma stack_lt_fixpoint :
  forall xs f z,
    normal_function f ->
    each complete xs ->
    each (fun x => x < z) xs ->
    complete z ->
    limitOrdinal z ->
    (forall q, complete q -> q < z -> schutte_column f (natOrdSize (length xs)) q z <= z) ->
    schutte_stack f xs 0 < z.
Proof.
  induction xs; simpl; intros f z Hf Hc Hltz Hzc Hz Hfix; intuition.
  - rewrite ord_isLimit in Hz. destruct Hz as [Hz0 Hz].
    rewrite <- (Hfix 0); auto.
    rewrite schutte_column0.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_l.
    auto.
  - apply IHxs; simpl; auto with ord.
    intros.
    rewrite <- (Hfix (succOrd a)) at 2; auto.
    2:{ apply limit_unreachable; auto. }
    case_eq (length xs).
    { intro Hxs. simpl.
      rewrite schutte_column0.
      rewrite schutte_column0.
      rewrite schutte_column_veblen; auto with ord.
      rewrite <- (veblen_fixpoints f) with (α:=a); auto with ord.
      rewrite <- veblen_fax; auto with ord.
      apply normal_monotone; auto with ord.
      apply addOrd_monotone; auto with ord.
      transitivity z.
      2:{ apply normal_inflationary; auto with ord. }
      rewrite <- (Hfix q) at 2; auto with ord.
      transitivity (schutte_column f 1 q z).
      - rewrite schutte_column_veblen; auto with ord.
        rewrite <- veblen_fax; auto with ord.
      - apply schutte_column_monotoneβ; auto with ord. }
    
    intros.
    rewrite <- (schutte_column_fixpoint 
                  (succOrd (natOrdSize (S n))) (succOrd a) z f
                  (natOrdSize (S n)) a); auto with ord.
    apply schutte_column_collapse; auto with ord.
    + apply normal_complete; auto with ord.
    + simpl. auto with ord.
    + apply ord_lt_le_trans with z; auto.
      rewrite <- normal_inflationary with (f := fun x => schutte_column _ _ x 0); auto with ord.
    + rewrite <- normal_inflationary with (f := fun x => schutte_column _ _ x 0); auto with ord.
    + apply schutte_column_monotone_full; auto with ord.
      intros. apply schutte_column_monotoneβ; auto with ord.
      apply schutte_column_fixpoint; auto with ord.
Qed.

Lemma schutte_stack_lt_short:
  forall xs ys x y f,
    normal_function f ->
    each complete (x::xs) ->
    each complete (y::ys) ->
    x < y ->
    length xs = length ys ->
    (length ys <= 1)%nat ->
    each (fun x => x < schutte_stack f (y::ys) 0) xs ->
    schutte_stack f (x::xs) 0 < schutte_stack f (y::ys) 0.
Proof.
  intros.
  destruct ys. simpl in *.
  { destruct xs; simpl in *; try discriminate.
    repeat rewrite schutte_column0.
    intuition.
    apply normal_increasing; auto with ord.
    repeat rewrite addOrd_zero_r.
    auto. }
  destruct xs; simpl in *; try discriminate.
  destruct ys; simpl in *; try lia.
  destruct xs; simpl in *; try discriminate.
  intuition.
  repeat rewrite schutte_column0.
  repeat rewrite schutte_column_veblen; auto with ord.
  rewrite <- (veblen_fixpoints f) with (α:=x) (β:=y); auto with ord.
  apply normal_increasing; auto with ord.
  rewrite addOrd_zero_r.
  rewrite schutte_column0 in H1.
  rewrite schutte_column_veblen in H1; auto with ord.
Qed.

Fixpoint schutte_stack_aug (f:Ord -> Ord) (xs:list Ord) (n:nat) : Ord -> Ord :=
  match xs with
  | [] => f
  | α::xs' => schutte_stack_aug (schutte_column f (sz (length xs' + n)%nat) α) xs' n
  end.

Lemma schutte_stack_aug_normal: forall xs n f,
    normal_function f ->
    each complete xs ->
    normal_function (schutte_stack_aug f xs n).
Proof.
  induction xs; simpl; intuition.
Qed.

Local Hint Resolve schutte_stack_aug_normal: core.


Lemma schutte_stack_to_aug xs : forall f x,
  schutte_stack f xs x = schutte_stack_aug f xs O x.
Proof.
  induction xs; simpl; intuition.
  rewrite IHxs.
  rewrite <- (plus_n_O (length xs)).
  auto.
Qed.

Lemma schutte_stack_aug_app: forall xs ys f x n,
    schutte_stack_aug f (xs++ys) n x =
      schutte_stack_aug (schutte_stack_aug f xs (n+length ys)%nat) ys n x.
Proof.
  induction xs; simpl; intuition.
  rewrite IHxs.
  rewrite length_app.
  replace (length xs + length ys + n)%nat with 
    (length xs + (n + length ys))%nat by lia.
  auto.
Qed.

Lemma schutte_stack_rev_induction:
  forall f (P: list Ord -> nat -> Ord -> Ord -> Prop),
    (forall n x0, P [] n x0 (f x0)) ->
    (forall xs n,
      (forall x0, P xs (S n) x0 (schutte_stack_aug f xs (S n) x0)) ->
      (forall x x0, P (xs++[x]) n x0 (schutte_column (schutte_stack_aug f xs (S n)) (natOrdSize n) x x0))) ->
    (forall xs n x0, P xs n x0 (schutte_stack_aug f xs n x0)).
Proof.
  intros f P HP0 HPind xs.
  rewrite <- (rev_involutive xs).
  apply rev_list_ind.
  - simpl; intros; auto.
  - simpl; intros.
    rewrite schutte_stack_aug_app.
    simpl.
    replace (n+1)%nat with (S n) by lia.
    apply HPind; auto.
Qed.    

Lemma schutte_stack_aug_add_closed:
  forall f,
    normal_function f ->
    (forall x p q, complete x -> p < f x -> q < f x -> p + q < f x) ->
    (forall xs n x0 p q,
        complete x0 ->
        each complete xs ->
        p < schutte_stack_aug f xs n x0 ->
        q < schutte_stack_aug f xs n x0 ->
        p + q < schutte_stack_aug f xs n x0).
Proof.
  intros f Hf1 Hf2 xs n x0.
  apply (schutte_stack_rev_induction f (fun xs n x0 z =>
    forall p q : Ord,
      complete x0 ->
      each complete xs ->
      p < z ->
      q < z ->
      p + q < z)).
  - simpl; intros. apply Hf2; auto.
  - simpl; intros.
    rewrite each_app in *. simpl in *; intuition.
    apply schutte_column_preserves_add_closed; auto with ord.
Qed.    

Lemma schutte_stack_add_closed:
  forall f x xs x0 p q,
    normal_function f ->
    complete x ->
    each complete xs ->
    complete x0 ->
    x > 0 ->
    (length xs > 1)%nat ->
    p < schutte_stack f (x::xs) x0 ->
    q < schutte_stack f (x::xs) x0 ->
    p + q < schutte_stack f (x::xs) x0.
Proof.
  intros f x xs x0 p q.
  simpl.
  rewrite (schutte_stack_to_aug xs).
  intros.
  apply schutte_stack_aug_add_closed; auto with ord.
  intros; apply schutte_column_add_closed; auto with ord.
  apply ord_le_lt_trans with (natOrdSize 1%nat); [ simpl; auto with ord |].
  apply natOrdSize_increasing; auto.
Qed.  


Lemma schutte_stack_fixpoint1 : forall xs x0 f g,
    each complete xs ->
    complete x0 ->
    normal_function f ->
    normal_function g ->
    (forall z, complete z -> g (f z) <= f z) ->
    g (schutte_stack f xs x0) <= schutte_stack f xs x0.
Proof.
  induction xs; simpl; intros; simpl in *; intuition.
  apply IHxs; intuition.
  destruct (complete_zeroDec a); auto with ord.
  - assert (Heq: schutte_column f (natOrdSize (length xs)) a z ≈ f z).
    split.
    + transitivity (schutte_column f (natOrdSize (length xs)) 0 z); auto with ord.
      rewrite schutte_column_arg0; auto with ord.
    + rewrite schutte_column_unroll; auto with ord.
      rewrite <- lub_le1.
      apply normal_monotone; auto with ord.
    + rewrite Heq at 2.
      rewrite <- H3; auto with ord.
      apply normal_monotone; auto with ord.
      apply Heq.
  - destruct xs.
    { simpl.
      rewrite schutte_column0 at 2.
      rewrite <- H3; auto with ord.
      apply normal_monotone; auto with ord.
      rewrite schutte_column0.
      auto with ord. }
    rewrite <- (schutte_column_fixpoint (natOrdSize (length (o::xs))) a z f 0 0) at 2; auto with ord.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    rewrite <- H3; auto with ord.
    apply normal_monotone; auto with ord.
    rewrite <- (normal_inflationary f); auto with ord.
    simpl; auto with ord.
Qed.    
    

(* Need lemmas like this for schutte stack....

Fixpoint hasNonzeroIndexLoop (x:Ord) (xs:list Ord) :=
  match xs with
  | [] => False
  | (x'::xs') => x > 0 \/ hasNonzeroIndexLoop x' xs'
  end.

Definition hasNonzeroIndex (xs : list Ord) :=
  match xs with
  | [] => False
  | x::xs => hasNonzeroIndexLoop x xs
  end.

Lemma BH_stack_fixpoint2 : forall xs x f,
    each complete (x::xs) ->
    normal_function f ->
    hasNonzeroIndexLoop x xs ->
    f (BH_stack f x xs) <= BH_stack f x xs.
Proof.
  induction xs; simpl; intros; simpl in *; intuition.
  - apply BH_stack_fixpoint1; auto.
    simpl; intuition.
    intros.
    rewrite <- (bhtower_fixpoint (S (length xs)) f 0 x z) at 2; auto with ord arith.
    rewrite bhtower_zero. auto with ord.
  - rewrite <- IHxs at 2; intuition.
    rewrite bhtower_unroll.
    auto with ord.
Qed.

Lemma BH_stack_lt_fixpoint_limit :
  forall xs f x z,
    normal_function f ->
    each complete (x::xs) ->
    each_lt z (x::xs) ->
    complete z ->
    limitOrdinal z ->
    (forall q, complete q -> q < z -> bhtower (length xs) f q z <= z) ->
    BH_stack f x xs < z.
Proof.
  unfold each_lt.
  induction xs; simpl; intros f x z Hf Hc Hltz Hz Hlim Hfix; intuition.
  - rewrite <- (Hfix x); auto.
    rewrite bhtower_index_zero.
    apply normal_increasing; auto with ord.

  - apply IHxs; simpl; auto with ord.
    intros.
    destruct xs; simpl.
    { rewrite bhtower_index_zero. simpl in *. apply Hfix; auto. }
    rewrite <- (Hfix (succOrd x)) at 2; auto with ord.
    rewrite bhtower_succ; simpl; auto with ord arith.
    rewrite <- (bhtower_fixpoint (S (length xs)) _ q (1+z) 0); auto with ord arith.
    apply bhtower_monotone; auto with ord.
    transitivity (1+z); auto with ord.
    apply (normal_inflationary (fun q => bhtower (S (length xs)) (bhtower (S (S (length xs))) f x) q 0)); auto with ord.
    apply ord_lt_le_trans with z; auto with ord.
    apply limit_unreachable; auto.
Qed.

*)

Lemma schutte_stack_lt_fixpoint_limit :
  forall xs f x z,
    normal_function f ->
    each complete (x::xs) ->
    each (fun x => x < z) (x::xs) ->
    complete z ->
    limitOrdinal z ->
    (forall q, complete q -> q < z -> schutte_column f (natOrdSize (length xs)) q z <= z) ->
    schutte_stack f (x::xs) 0 < z.
Proof.
  induction xs; simpl; intros f x z Hf Hc Hltz Hz Hlim Hfix; intuition.
  - rewrite <- (Hfix x); auto.
    repeat rewrite schutte_column0.
    apply normal_increasing; auto with ord.
    apply addOrd_increasing; auto with ord.
    apply ord_le_lt_trans with x; auto with ord.
  - apply IHxs; simpl; auto with ord.
    intros.
Admitted.

(*
    destruct xs.
    { simpl.
      rewrite schutte_column0.
      rewrite <- (Hfix (succOrd x)) at 2; auto with ord.
      simpl.



    apply schutte_column_collapse; auto with ord.

    admit.

    rewrite <- (Hfix (succOrd x)) at 2; auto with ord.
    rewrite <- (schutte_column_fixpoint (succOrd (natOrdSize (length xs))) (succOrd x) z f
                                           (natOrdSize (length xs)) x); auto with ord.
    
    
    
    
    



    rewrite bhtower_succ; simpl; auto with ord arith.
    rewrite <- (bhtower_fixpoint (S (length xs)) _ q (1+z) 0); auto with ord arith.
    apply bhtower_monotone; auto with ord.
    transitivity (1+z); auto with ord.
    apply (normal_inflationary (fun q => bhtower (S (length xs)) (bhtower (S (S (length xs))) f x) q 0)); auto with ord.
    apply ord_lt_le_trans with z; auto with ord.
    apply limit_unreachable; auto.
Qed.
*)





Lemma schutte_stack_lt_long:
  forall xs ys x y f,
    normal_function f ->
    each complete (x::xs) ->
    each complete (y::ys) ->
    x < y ->
    length xs = length ys ->
    (length ys > 1)%nat ->
    each (fun x => x < schutte_stack f (y::ys) 0) xs ->
    schutte_stack f (x::xs) 0 < schutte_stack f (y::ys) 0.
Proof.
  intros.
  simpl.
  simpl in *; intuition.
  rewrite H3.
  
  assert (Hgen: forall xs n x0,
    complete x0 ->
    x0 < schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0 ->
    each (fun x : Ord => x < schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0) xs ->
    each complete xs ->
    (length xs + n = length ys)%nat ->
    schutte_stack_aug (schutte_column f (natOrdSize (length ys)) x) xs n x0 <
    schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0).

  - apply (schutte_stack_rev_induction (schutte_column f (natOrdSize (length ys)) x) (fun xs n x0 z =>
         complete x0 ->
         x0 < schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0 ->
         each (fun x : Ord => x < schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0) xs ->
         each complete xs ->
         (length xs + n = length ys)%nat ->
         z <
           schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0)).
    + simpl; intuition.
      apply ord_lt_le_trans with 
        (schutte_column f (natOrdSize (length ys)) x 
           (schutte_stack (schutte_column f (natOrdSize (length ys)) y) ys 0)).
      { apply normal_increasing; auto with ord. }
      apply schutte_stack_fixpoint1; auto with ord.
      intros. 
      rewrite <- (schutte_column_fixpoint (natOrdSize (length ys)) y z f 0 x) at 2; auto with ord.
      rewrite schutte_column0; auto with ord.
      transitivity (natOrdSize 1%nat); [ simpl; auto with ord |].
      apply natOrdSize_increasing; auto.
    + intros xs' n Hind.
      simpl.
      intros x0 x1 Hx1 Hx2 Hx3 Hx4 Hlen.
      rewrite each_app in Hx3. rewrite each_app in Hx4.
      rewrite length_app in Hlen.
      simpl in *; intuition.

      destruct (PeanoNat.Nat.eq_0_gt_0_cases n).
      { subst n; simpl.
        rewrite schutte_column0.
        apply Hind; auto with ord.
        apply schutte_stack_add_closed; auto with ord.
        apply ord_le_lt_trans with x; auto with ord.
        lia. }

      apply schutte_column_collapse'; auto with ord.
      * admit.
Admitted.
(*
      * assert (Hasdf: 
                 schutte_column (schutte_stack_aug (schutte_column f (natOrdSize (length ys)) x) xs' (S n))
                   (natOrdSize n) (schutte_stack (schutte_column f (natOrdSize (length ys)) y) [] 0) 0
                   ≤ schutte_stack (schutte_column f (natOrdSize (length ys)) y) [] 0).
        { simpl.
          rewrite <- (schutte_column_fixpoint (natOrdSize (length ys)) y 0 f (natOrdSize n) x) at 2; auto with ord.
          
          
      
      



admit.  (* ???? *)

  - rewrite (schutte_stack_to_aug xs).
    apply Hgen; auto with ord.
    lia.
Qed.


Lemma schutte_stack_lt_long:
  forall xs ys x y f,
    normal_function f ->
    each complete (x::xs) ->
    each complete (y::ys) ->
    x < y ->
    length xs = length ys ->
    (length ys > 1)%nat ->
    each (fun x => x < schutte_stack f (y::ys) 0) xs ->
    schutte_stack f (x::xs) 0 < schutte_stack f (y::ys) 0.
Proof.
  intros.

  simpl in *; intuition.
  apply stack_lt_fixpoint; auto with ord.
  - admit.
  - simpl; intros.
    rewrite H3.
    apply schutte_column_collapse; auto with ord.
    { change (natOrdSize O < natOrdSize (length ys)).
      apply natOrdSize_increasing; lia. }
    clear H1 H9 q.
    clear H5 H3 H7 xs.
    induction ys; simpl in *; try lia.
    intuition.
    destruct ys; simpl.
    + rewrite schutte_column0 at 2.
      rewrite schutte_column_veblen; auto with ord.
      rewrite schutte_column_veblen; auto with ord.
      transitivity (veblen (schutte_column f 1 x) (schutte_column f 1 y a) 0).
      { apply veblen_monotone_first; auto with ord.
        rewrite schutte_column0.
        apply schutte_column_monotone; auto with ord.
        rewrite addOrd_zero_r. auto with ord. }
      





rewrite schutte_column0.
      rewrite schutte_column0.
      


  simpl; intuition.

  - rewrite <- schutte_stack_base; simpl in *; intuition auto with ord.
    apply ord_lt_le_trans with y; auto.
    apply normal_inflationary with (f:=fun x => schutte_column _ _ x 0); auto with ord.
  - admit.
  - intros; simpl.
    rewrite H3.
    
    

    
    
    
  




apply limitOrdinal_intro; auto with ord.
    intros.
    exists (i+1); split; auto with ord.
    { apply ord_le_lt_trans with (i+0); auto with ord. }
    admit.
  - simpl; intros.
    rewrite H3.
    apply schutte_column_collapse; auto with ord.
    + transitivity (natOrdSize 1); [ simpl; auto with ord |].
      apply natOrdSize_increasing; auto.
    + 
      


admit.
Admitted.
*)

    
Lemma schutte_stack_lt:
  forall xs ys x y f,
    normal_function f ->
    each complete (x::xs) ->
    each complete (y::ys) ->
    x < y ->
    length xs = length ys ->
    each (fun x => x < schutte_stack f (y::ys) 0) xs ->
    schutte_stack f (x::xs) 0 < schutte_stack f (y::ys) 0.
Proof.
  intros.
  destruct (PeanoNat.Nat.le_gt_cases (length ys) 1).
  - apply schutte_stack_lt_short; auto.
  - apply schutte_stack_lt_long; auto.
Qed.
