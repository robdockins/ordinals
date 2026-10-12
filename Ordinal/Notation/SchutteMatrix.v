From Stdlib Require Import Relations.Relation_Operators.
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
From Ordinal Require Import AckermannTower.
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
      schutte_stack_normal
  : core.

Scheme All for prod.
Scheme All for list.

Inductive VForm :=
| Z
| N : list (VForm * VForm) -> VForm.

Fixpoint VF_termSize (x:VForm) : nat :=
  match x with
  | Z   => 0%nat
  | N l => 1%nat + fold_right (fun a b => 1 + VF_termSize (fst a) + VF_termSize (snd a) + b)%nat 0%nat l
  end.

Definition VF_matrixSize (xs:list (VForm*VForm)) : nat :=
  fold_right (fun a b => 1 + VF_termSize (fst a) + VF_termSize (snd a) + b)%nat 0%nat xs.

Fixpoint VF_denote (x:VForm) : Ord :=
  match x with
  | Z => 0
  | N l => schutte_matrix (addOrd 1) (map (fun x => (VF_denote (fst x), VF_denote (snd x))) l) 0
  end.

Definition matrix_denote (xs: list (VForm  * VForm)) : list (Ord * Ord) :=
  map (fun x => (VF_denote (fst x), VF_denote (snd x))) xs.

Definition VForm_induction : forall
  (P:VForm -> Prop)
  (HZ: P Z)
  (Hind: forall xs, each (fun x => P (fst x) /\ P (snd x)) xs -> P (N xs)),
  forall x, P x :=

  fun P HZ Hind =>
  fix outer (x:VForm) : P x :=
    match x as x' return P x' with
    | Z => HZ
    | N xs0 =>
        Hind xs0
          ((fix inner (xs:list (VForm*VForm)) : each _ xs :=
              match xs as xs' return each _ xs' with
              | nil => I
              | (y::ys) => conj (conj (outer (fst y)) (outer (snd y))) (inner ys)
              end
           ) xs0)
    end.

Theorem VForm_complete: forall x:VForm, complete (VF_denote x).
Proof.
  induction x using VForm_induction; auto.
  induction xs; simpl each in *; simpl VF_denote in *; auto with ord.
  apply normal_complete; auto with ord.
  apply schutte_matrix_normal; auto with ord.
  { destruct H as [_ Hxs]. clear -Hxs.
    induction xs; simpl in *; intuition. }
  apply schutte_column_normal; intuition auto with ord.
Qed.

Lemma VForm_all_complete: forall xs, all_complete (matrix_denote xs).
Proof.
  unfold matrix_denote.
  induction xs as [|[b a] xs IHxs]; simpl in *; intuition.
  apply VForm_complete.
  apply VForm_complete.
Qed.

Lemma VForm_each_complete: forall xs,
    each (fun x => complete (VF_denote (fst x)) /\ complete (VF_denote (snd x))) xs.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl in *; intuition.
  apply VForm_complete.
  apply VForm_complete.
Qed.

Local Hint Resolve VForm_complete VForm_each_complete VForm_all_complete: core.

Lemma VF_matrixSize_app: forall xs ys,
    VF_matrixSize (xs++ys) = (VF_matrixSize xs + VF_matrixSize ys)%nat.
Proof.
  unfold VF_matrixSize.
  induction xs; simpl; intuition.
  rewrite IHxs; simpl; lia.
Qed.

Fixpoint VF_proper (x:VForm) :=
  match x with
  | Z => True
  | N l =>
      (fix VF_matrix_proper (xs:list (VForm*VForm)) : Prop :=
         match xs with
         | [] => True
         | (b1,a1)::xs =>
             VF_proper b1 /\
             VF_proper a1 /\
             match xs with
             | [] => True
             | (b2,_)::_ => VF_denote b1 > VF_denote b2 /\ VF_matrix_proper xs
             end
         end
      ) l
  end.

Fixpoint VF_matrix_proper (xs:list (VForm*VForm)) : Prop :=
  match xs with
  | [] => True
  | (b1,a1)::xs =>
      VF_proper b1 /\
        VF_proper a1 /\
        match xs with
        | [] => True
        | (b2,_)::_ => VF_denote b1 > VF_denote b2 /\ VF_matrix_proper xs
        end
  end.

Lemma VF_proper_eq x:
  VF_proper x =
  match x with
  | Z => True
  | N l => VF_matrix_proper l
  end.
Proof.
  destruct x; reflexivity.
Qed.


Theorem VForm_bounded : forall x:VForm, VF_denote x < LargeVeblenOrdinal.
Proof.
  intro x.
  induction x using VForm_induction.

  - simpl. apply LVO_nonzero.
  - simpl.
    apply matrix_E_unreachable; auto with ord.
    + apply LVO_complete.
    + rewrite each_map. simpl. auto.
    + apply LVO_nonzero.
    + rewrite LVO_alt at 2.
      rewrite normal_fixpoint; auto with ord.
      apply schutte_column_monotoneβ; auto with ord.
      apply LVO_alt.
Qed.

Canonical Structure VF := ord VForm VF_denote.

Lemma LVO_proper_VForm: forall x,
    x < LargeVeblenOrdinal ->
    exists y:VForm, VF_proper y /\ x <= VF_denote y.
Proof.
  intros.
  rewrite LVO_alt in H.
  unfold fixOrd in H.
  apply sup_lt in H.
  destruct H as [k Hk].
  apply ord_lt_le in Hk.
  revert x Hk.
  induction k; simpl in *; auto with ord.
  - intros. exists Z; simpl; intuition.
  - intros.
    destruct (IHk (iter_f (fun x : Ord => schutte_column (addOrd 1) x 1 0) 0 k)) as [y [Hy1 Hy2]]; auto with ord.
    exists (N [(y, N [])]); simpl; intuition.
    rewrite Hk.
    apply schutte_column_monotone_full; auto with ord.
Qed.

Lemma VForm_le_LVO: LargeVeblenOrdinal <= VF.
Proof.
  rewrite ord_le_unfold; intros.
  destruct (LVO_proper_VForm a) as [y [Hy1 Hy2]]; auto with ord.
  rewrite ord_lt_unfold.
  exists y. auto.
Qed.

Theorem VF_LVO : VF ≈ LargeVeblenOrdinal.
Proof.
  split.
  - apply limit_least. intro i. apply VForm_bounded.
  - apply VForm_le_LVO.
Qed.

Inductive active_subterm : list (VForm*VForm) -> VForm -> Prop :=
| active_last : forall b a xs,
    a <> Z ->
    each (fun x => snd x = Z) xs ->
    active_subterm ((b,a)::xs) a

| active_later: forall z x xs,
    active_subterm xs z ->
    active_subterm (x::xs) z.

Lemma active_subterm_nonzero: forall xs a,
    active_subterm xs a -> a <> Z.
Proof.
  induction xs; simpl; intros b Hactive.
  - inversion Hactive.
  - inversion Hactive; intuition; subst; auto.
    apply IHxs with Z; auto.
Qed.

Lemma active_subterm_all_zeros: forall xs a,
    each (fun x : VForm*VForm => snd x = Z) xs ->
    active_subterm xs a ->
    False.
Proof.
  induction xs; simpl; intros b Heach Hactive.
  - inversion Hactive.
  - inversion Hactive; intuition; subst; auto.
    apply IHxs with b; auto.
Qed.

Lemma active_subterm_unique: forall xs a b,
    active_subterm xs a ->
    active_subterm xs b ->
    a = b.
Proof.
  induction xs as [|[p q] xs IHxs]; simpl; intros a b Ha Hb.
  - inversion Ha.
  - inversion Ha; subst; inversion Hb; subst; auto.
    elim (active_subterm_all_zeros xs b); auto.
    elim (active_subterm_all_zeros xs a); auto.
Qed.

Lemma VF_matrix_proper_correct: forall xs,
    VF_matrix_proper xs <->
      (each (fun x => VF_proper (fst x) /\ VF_proper (snd x)) xs /\
       schutte_matrix_proper (matrix_denote xs) LargeVeblenOrdinal LargeVeblenOrdinal).
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  - destruct xs as [|[b' a'] xs]; simpl in *; intuition.
  - apply VForm_bounded.
  - apply VForm_bounded.
  - destruct xs as [|[b' a'] xs]; simpl in *; intuition.
  - destruct xs as [|[b' a'] xs]; simpl in *; intuition.
    apply H9; intuition.
    apply VForm_bounded.
Qed.

Lemma ordering_swap_inv: forall o, ordering_swap (ordering_swap o) = o.
Proof.
  intro o; destruct o; simpl; auto.
Qed.

Lemma VF_nonzero: forall x, 0 < VF_denote x <-> x <> Z.
Proof.
  intro x; destruct x; simpl; intuition auto with ord.
  apply (ord_lt_irreflexive 0); auto.
  discriminate.
Qed.

Fixpoint is_sparse (xs: list (VForm * VForm)) : Prop :=
  match xs with
  | [] => True
  | ((b,a)::xs) => a <> Z /\ is_sparse xs
  end.

Fixpoint make_sparse (xs: list (VForm * VForm)) : list (VForm * VForm) :=
  match xs with
  | [] => []
  | ((_,Z)::xs) => make_sparse xs
  | ((b,a)::xs) => (b,a) :: make_sparse xs
  end.

Lemma make_sparse_is_sparse: forall xs,
    is_sparse (make_sparse xs).
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  destruct a; simpl; intuition.
  discriminate.
Qed.

Lemma make_sparse_size: forall xs,
    (VF_matrixSize (make_sparse xs) <= VF_matrixSize xs)%nat.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  destruct a; simpl; lia.
Qed.

Lemma make_sparse_proper_one: forall xs b a,
  VF_matrix_proper ((b,a)::xs) ->
  VF_matrix_proper ((b,a)::make_sparse xs).
Proof.
  induction xs as [|[b' a'] xs IHxs]; simpl in *; intuition.
  destruct (IHxs b' a'); intuition.
  destruct a'; simpl; intuition.
  destruct (make_sparse xs); simpl; intuition.
  destruct p; simpl in *; intuition.
  transitivity (VF_denote b'); auto.
Qed.

Lemma make_sparse_proper: forall xs,
  VF_matrix_proper xs ->
  VF_matrix_proper (make_sparse xs).
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  assert (VF_matrix_proper xs).
  { destruct xs as [|[b' a'] ?]; intuition. }
  assert (VF_matrix_proper (make_sparse xs)).
  { apply IHxs. auto. }
  destruct a; auto.
  apply make_sparse_proper_one; simpl; auto.
Qed.

Lemma make_sparse_eq: forall xs f,
    normal_function f ->
    schutte_matrix f (matrix_denote (make_sparse xs)) 0 ≈ schutte_matrix f (matrix_denote xs) 0.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition auto with ord.
  destruct a; simpl in *; intuition.
  - rewrite IHxs; auto.
    split; apply schutte_matrix_monotone_func; auto with ord.
    + intros; rewrite schutte_column_arg0; auto with ord.
    + intros; rewrite schutte_column_arg0; auto with ord.
  - rewrite IHxs; auto with ord.
Qed.

Lemma active_subterm_sparse:
  forall xs x,
    is_sparse xs ->
    (active_subterm xs x <-> exists l b, xs = (l ++ [(b,x)])).
Proof.
  induction xs; simpl; intuition.
  - inversion H0.
  - destruct H0 as [?[??]].
    destruct x0; discriminate.
  - inversion H; subst.
    + exists []. exists a0; simpl.
      destruct xs as [|[??]?]; simpl in *; intuition.
    + rewrite IHxs in H5; auto.
      destruct H5 as [l [b' H5]].
      exists ((a0,b)::l), b'. rewrite H5.
      auto.
  - destruct H as [l [b' H]].
    destruct l; simpl in *.
    + inversion H; subst.
      apply active_last; auto.
    + inversion H; subst.
      apply active_later.
      rewrite IHxs; simpl; auto.
      exists l. exists b'. auto.
Qed.

Lemma is_sparse_app: forall xs ys,
    is_sparse (xs ++ ys) <-> is_sparse xs /\ is_sparse ys.
Proof.
  induction xs as [|[??]?]; simpl; intuition.
  rewrite IHxs in H1; intuition.
  rewrite IHxs in H1; intuition.
  rewrite IHxs; auto.
Qed.

Lemma matrix_denote_app: forall xs ys,
    matrix_denote (xs++ys) = matrix_denote xs ++ matrix_denote ys.
Proof.
  induction xs as [|[??]?]; simpl; intuition.
  rewrite IHxs; auto.
Qed.

Fixpoint matrix_trivial_dec (xs:list (VForm * VForm)) :
  { trivial_matrix (matrix_denote xs) } + { nontrivial_matrix (matrix_denote xs) }.

  refine (
  match xs with
  | [] => left _
  | (b,a)::xs =>
      match a with
      | Z =>
          match matrix_trivial_dec xs with
          | left H => left _
          | right H => right _
          end
      | N _ => right _
      end
  end).

  - hnf; auto.
  - hnf; simpl; split; auto with ord.
  - hnf; simpl; auto.
  - hnf; simpl. left. auto with ord.
Defined.

Section sparse_compare.
  Variable n:nat.
  Variable compare_rec :
    forall x y, (VF_termSize x + VF_termSize y < n)%nat ->
                { o | VF_proper x -> VF_proper y ->ordering_correct o (VF_denote x) (VF_denote y) }.

  Fixpoint check_lt xs ytop {struct xs} :
    (VF_matrixSize xs + VF_termSize ytop < n)%nat ->
    { o | VF_matrix_proper xs ->
          VF_proper ytop ->
          confirm_lt o (matrix_denote xs) (VF_denote ytop) }.
    refine (
    match xs as xs' return
          (VF_matrixSize xs' + VF_termSize ytop < n)%nat ->
          { o | VF_matrix_proper xs' -> VF_proper ytop -> confirm_lt o (matrix_denote xs') (VF_denote ytop) }
    with
    | [] => fun H => exist _ LT _
    | (b,a)::xs =>
        fun H =>
          let (o, Hcomp) := compare_rec a ytop _ in
          match o as o' return (_ -> _ -> ordering_correct o' (VF_denote a) (VF_denote ytop)) -> _ with
          | LT =>
              fun Hcomp =>
                let (o, Hrec) := check_lt xs ytop _ in exist _ o _
          | EQ =>
              fun Hcomp =>
                if matrix_trivial_dec xs then exist _ EQ _ else exist _ GT _
          | GT =>
              fun Hcomp => exist _ GT _
        end Hcomp
    end).

    - intros; apply confirm_lt_nil.
    - simpl in *. lia.
    - simpl in *. lia.
    - simpl in *; intuition.
      apply confirm_lt_lt; auto.
      apply Hrec; auto.
      destruct xs as [|[? ?]?]; simpl in *; intuition.
    - simpl in *; intuition.
      apply confirm_lt_eq1; auto.
    - simpl in *. intuition.
      apply confirm_lt_eq2; auto.
    - simpl in *. intuition.
      apply confirm_lt_gt; auto.
  Defined.

  Fixpoint matrix_compare xtop xs ys ytop f (Hf: normal_function f):
    (VF_matrixSize xs + VF_matrixSize ys < n)%nat ->
    (VF_matrixSize xs + VF_termSize ytop < n)%nat ->
    (VF_matrixSize ys + VF_termSize xtop < n)%nat ->
    is_sparse xs ->
    is_sparse ys ->
    { o | VF_proper xtop ->
          VF_matrix_proper xs ->
          VF_matrix_proper ys ->
          VF_proper ytop ->
          VF_denote xtop ≈ schutte_matrix f (matrix_denote xs) 0 ->
          VF_denote ytop ≈ schutte_matrix f (matrix_denote ys) 0 ->
          schutte_matrix_compare o f (matrix_denote xs) (matrix_denote ys) }.

  refine (match xs as xs', ys as ys' return
    (VF_matrixSize xs' + VF_matrixSize ys' < n)%nat ->
    (VF_matrixSize xs' + VF_termSize ytop < n)%nat ->
    (VF_matrixSize ys' + VF_termSize xtop < n)%nat ->
    is_sparse xs' ->
    is_sparse ys' ->
    { o | VF_proper xtop ->
          VF_matrix_proper xs' ->
          VF_matrix_proper ys' ->
          VF_proper ytop ->
          VF_denote xtop ≈ schutte_matrix f (matrix_denote xs') 0 ->
          VF_denote ytop ≈ schutte_matrix f (matrix_denote ys') 0 ->
          schutte_matrix_compare o f (matrix_denote xs') (matrix_denote ys') }
  with
  | [], [] => fun _ _ _ _ _ => exist _ EQ _
  | [], (yb,ya)::_ => fun _ _ _ _ _ => exist _ LT _
  | (xb,xa)::_, [] => fun _ _ _ _ _ => exist _ GT _
  | (xb,xa)::xs, (yb,ya)::ys =>
      fun Hsz1 Hsz2 Hsz3 Hspx Hspy =>
        let (ob, Hcompb) := compare_rec xb yb _ in
        match ob as ob' return (_ -> _ -> ordering_correct ob' (VF_denote xb) (VF_denote yb)) -> _ with
        | LT => fun Hlt => let (o, Hconfirm) := check_lt ((xb,xa)::xs) ytop _ in exist _ o _
        | EQ => fun Heq =>
            let (o, Hcomp) := compare_rec xa ya _ in
            match o as o' return (_ -> _ -> ordering_correct o' (VF_denote xa) (VF_denote ya)) -> _ with
            | LT => fun Hcomp => let (o, Hconfirm) := check_lt xs ytop _ in exist _ o _
            | EQ => fun Hcomp =>
                      let (o, Hcomp2) :=
                        matrix_compare xtop xs ys ytop (schutte_column f (VF_denote xb) (VF_denote xa)) _ _ _ _ _ _                       in exist _ o _
            | GT => fun Hcomp => let (o, Hconfirm) := check_lt ys xtop _ in exist _ (ordering_swap o) _
            end Hcomp
        | GT => fun Hgt => let (o, Hconfirm) := check_lt ((yb,ya)::ys) xtop _ in exist _ (ordering_swap o) _
        end Hcompb
   end).

  - simpl. intros. apply mat_comp_nil_nil.
  - simpl; intros. apply mat_comp_nil_left.
    simpl in *; rewrite VF_nonzero; intuition.
  - simpl; intros.
    apply mat_comp_nil_right.
    simpl in *; rewrite VF_nonzero; intuition.
  - simpl in *. lia.
  - simpl in *; intuition.
  - simpl in *. intuition.
    apply mat_comp_index_lt; auto with ord.
    + rewrite VF_nonzero; intuition.
    + simpl. rewrite <- H4. auto.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. intuition.
    apply mat_comp_arg_lt; subst; auto with ord.
    simpl. rewrite <- H4; auto.
    apply Hconfirm; intuition.
    destruct xs as [|[? ?] ?]; simpl in *; intuition.
  - auto with ord.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *. lia.
  - simpl in *; intuition.
  - simpl in *; intuition.
  - simpl in *; intuition.
    apply mat_comp_eq; subst; auto with ord.
    apply H11; intuition.
    + destruct xs as [|[? ?] ?]; simpl in *; intuition.
    + destruct ys as [|[? ?] ?]; simpl in *; intuition.
    + rewrite H4.
      split; apply schutte_matrix_monotone_func; auto with ord.
      * intros. apply schutte_column_monotone_full; auto with ord.
        apply H14. apply H15.
      * intros. apply schutte_column_monotone_full; auto with ord.
        apply H14. apply H15.
  - simpl in *. lia.
  - simpl in *. intuition.
    apply mat_comp_arg_gt; subst; auto with ord.
    simpl. rewrite ordering_swap_inv.
    rewrite <- H3.
    apply Hconfirm; auto.
    destruct ys as [|[? ?] ?]; simpl in *; intuition.

  - simpl in *; lia.
  - simpl in *. intuition.
    apply mat_comp_index_gt; auto with ord.
    + rewrite VF_nonzero; intuition.
    + simpl. rewrite ordering_swap_inv.
      rewrite <- H3. auto.
  Defined.
End sparse_compare.

Fixpoint VF_compare_loop x y
  (Wf: Acc lt (VF_termSize x + VF_termSize y)%nat) {struct Wf} :
  { o | VF_proper x -> VF_proper y -> ordering_correct o (VF_denote x) (VF_denote y) }.

  refine (
  match Wf with
  | Acc_intro _ H =>
      match x as x', y as y'
            return x = x' -> y = y' -> { o | VF_proper x' -> VF_proper y' -> ordering_correct o (VF_denote x') (VF_denote y') }
      with
      | Z, Z => fun _ _ => exist _ EQ _
      | Z, N _ => fun _ _ => exist _ LT _
      | N _, Z => fun _ _ => exist _ GT _
      | N xs, N ys => fun Hx Hy =>
          let (o, Ho) :=
            matrix_compare
              ((VF_termSize x + VF_termSize y)%nat)
              (fun a b Hab => VF_compare_loop a b (H _ Hab))
              (N xs) (make_sparse xs) (make_sparse ys) (N ys)
              (addOrd 1) onePlus_normal
              _ _ _ _ _
          in exist _ o _
      end (eq_refl _) (eq_refl _)
  end).

  - simpl; auto with ord.
  - simpl; auto with ord.
  - simpl; auto with ord.
  - subst; simpl.
    generalize (make_sparse_size xs).
    generalize (make_sparse_size ys).
    unfold VF_matrixSize.
    simpl in *; lia.
  - subst; simpl.
    generalize (make_sparse_size xs).
    unfold VF_matrixSize.
    simpl in *; lia.
  - subst; simpl.
    generalize (make_sparse_size ys).
    unfold VF_matrixSize.
    simpl in *; lia.
  - apply make_sparse_is_sparse.
  - apply make_sparse_is_sparse.
  - intros.
    assert (Ho': schutte_matrix_compare o (addOrd 1) (matrix_denote (make_sparse xs))
      (matrix_denote (make_sparse ys))).
    { apply Ho; intuition.
      - apply make_sparse_proper; auto.
      - apply make_sparse_proper; auto.
      - rewrite make_sparse_eq; auto with ord.
      - rewrite make_sparse_eq; auto with ord. }
    eapply schutte_matrix_compare_correct in Ho'; auto with ord.
    + rewrite make_sparse_eq in Ho'; auto with ord.
      rewrite make_sparse_eq in Ho'; auto with ord.
    + apply VF_matrix_proper_correct.
      apply make_sparse_proper.
      auto.
    + apply VF_matrix_proper_correct.
      apply make_sparse_proper.
      auto.
Defined.

Definition VF_compare x y : ordering :=
  proj1_sig (VF_compare_loop x y (Wf_nat.lt_wf (VF_termSize x + VF_termSize y)%nat)).

Theorem VF_compare_correct :
  forall x y,
    VF_proper x ->
    VF_proper y ->
    ordering_correct (VF_compare x y) (VF_denote x) (VF_denote y).
Proof.
  intros x y Hx Hy. unfold VF_compare.
  destruct (VF_compare_loop x y (Wf_nat.lt_wf (VF_termSize x + VF_termSize y)%nat)).
  simpl; auto.
Qed.

Theorem VF_dec_order: forall x y,
    VF_proper x ->
    VF_proper y ->
    { VF_denote x < VF_denote y } + { VF_denote x ≈ VF_denote y } + { VF_denote x > VF_denote y }.
Proof.
  intros x y Hx Hy.
  generalize (VF_compare_correct x y Hx Hy).
  destruct (VF_compare x y); auto.
Defined.

Theorem VF_dec_lt_ge: forall x y,
    VF_proper x ->
    VF_proper y ->
    { VF_denote x < VF_denote y } + { VF_denote x >= VF_denote y }.
Proof.
  intros x y Hx Hy.
  generalize (VF_compare_correct x y Hx Hy).
  destruct (VF_compare x y); auto with ord.
  intro H. right. apply H.
Defined.

Lemma VF_dec_proper: forall x, { VF_proper x } + { ~VF_proper x }.
Proof.
  induction x; simpl; auto.
  induction l as [|[b a] l Hl]; simpl in *; auto.
  inversion H; clear H; simpl in *; subst.
  inversion H2; clear H; simpl in *; subst.
  destruct l as [|[b' a'] l]; simpl in *; intuition.
  destruct (VF_dec_lt_ge b' b); intuition.
  right; intuition.
  elim (ord_lt_irreflexive (VF_denote b)).
  rewrite o at 1. auto.
Defined.

Lemma VF_dec_proper_order : forall x y,
    { ~VF_proper x } + { ~VF_proper y } +
      { VF_denote x < VF_denote y } + { VF_denote x ≈ VF_denote y } + { VF_denote x > VF_denote y }.
Proof.
  intro x. destruct (VF_dec_proper x); auto.
  intro y. destruct (VF_dec_proper y); auto.
  destruct (VF_dec_order x y); intuition.
Defined.

Lemma VF_matrix_proper_app: forall xs ys,
  VF_matrix_proper (xs++ys) ->
  VF_matrix_proper xs.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  destruct xs as [|[b' a'] ?]; simpl in *; intuition.
  destruct (IHxs ys); intuition.
Qed.

Lemma matrix_index_lt': forall m n b a,
    VF_matrix_proper (n++m) ->
    In (b,a) m ->
    0 < VF_denote a ->
    VF_denote b < schutte_matrix (schutte_matrix (addOrd 1) (matrix_denote n)) (matrix_denote m) 0.
Proof.
  induction m; simpl; intuition. inversion H2; clear H2; subst; simpl in *.
  - rewrite <- schutte_matrix_base; auto with ord.
    destruct (VF_dec_order b0 (N (n++[(b0,a)]))) as [[?|?]|?]; simpl in *; auto with ord.
    + rewrite VF_matrix_proper_correct in H.
      repeat rewrite each_app in H.
      simpl in *; intuition.
    + apply VF_matrix_proper_app with m.
      rewrite <- app_assoc. simpl; auto.
    + rewrite map_app in o.
      rewrite schutte_matrix_app in o. simpl in o.
      auto.
    + rewrite map_app in o.
      rewrite schutte_matrix_app in o. simpl in o.
      elim (ord_lt_irreflexive LargeVeblenOrdinal).
      apply ord_le_lt_trans with (VF_denote b0); [ | apply VForm_bounded ].
      rewrite LVO_alt.
      apply normal_fix_least; auto with ord.
      transitivity (schutte_column (addOrd 1) (VF_denote b0) (VF_denote a) 0); auto with ord.
      transitivity (
          schutte_column
            (schutte_matrix (addOrd 1)
               (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) n))
            (VF_denote b0) (VF_denote a) 0); auto with ord.
      apply schutte_column_monotone_func'; auto with ord.
      intros; apply onePlus_least_normal; auto with ord.
      apply o.
    + rewrite map_app in o.
      rewrite schutte_matrix_app in o. simpl in o.
      elim (ord_lt_irreflexive LargeVeblenOrdinal).
      apply ord_le_lt_trans with (VF_denote b0); [ | apply VForm_bounded ].
      rewrite LVO_alt.
      apply normal_fix_least; auto with ord.
      transitivity (schutte_column (addOrd 1) (VF_denote b0) (VF_denote a) 0); auto with ord.
      transitivity (
          schutte_column
            (schutte_matrix (addOrd 1)
               (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) n))
            (VF_denote b0) (VF_denote a) 0); auto with ord.
      apply schutte_column_monotone_func'; auto with ord.
      intros; apply onePlus_least_normal; auto with ord.

  - simpl.
    eapply ord_lt_le_trans; [ apply (IHm (n ++ [(a0,b)]) b0 a); try assumption |].
    + rewrite <- app_assoc. auto.
    + apply schutte_matrix_monotone_func; auto with ord.
      intros. unfold matrix_denote.
      rewrite map_app. simpl.
      rewrite schutte_matrix_app; simpl; auto with ord.
Qed.

Lemma matrix_index_lt: forall m b a,
    VF_matrix_proper m ->
    In (b,a) m ->
    0 < VF_denote a ->
    VF_denote b < schutte_matrix (addOrd 1) (matrix_denote m) 0.
Proof.
  intros. apply (matrix_index_lt' m [] b a); auto.
Qed.

Lemma sparse_subterm_lt:
  forall l b x f,
    normal_function f ->
    is_sparse (l ++ [(b,x)]) ->
    each (fun z => VF_denote (snd z) < schutte_matrix f (matrix_denote (l ++ [(b,x)])) 0) l.
Proof.
  induction l as [|[b a] l IHl].
  - simpl. auto.
  - simpl; intuition.
    rewrite matrix_denote_app.
    rewrite schutte_matrix_app.
    simpl.
    rewrite is_sparse_app in H2. simpl in *; intuition.
    apply ord_le_lt_trans with
      (schutte_column
         (schutte_matrix (schutte_column f (VF_denote b) (VF_denote a)) (matrix_denote l))
         (VF_denote b0) 0 0).
    + rewrite schutte_column_arg0; auto with ord.
      rewrite <- schutte_matrix_base; auto with ord.
      apply normal_inflationary with (f:=fun x => schutte_column _ _ x 0); auto with ord.
    + apply normal_increasing with (f:=fun x => schutte_column _ _ x 0); auto with ord.
      apply VF_nonzero; auto.
Qed.

Lemma active_subterm_lt:
  forall xs,
    is_sparse xs ->
    (forall x, active_subterm xs x -> VF_denote x < VF_denote (N xs)) ->
    each (fun x => VF_denote (snd x) < VF_denote (N xs)) xs.
Proof.
  intros xs Hactive.
  assert (Hxs: xs = [] \/ exists l b a, xs = l ++ [(b,a)]).
  { clear. induction xs; intuition; subst; eauto.
    - right. exists []. simpl. eauto.
    - destruct H as [l [b' [a' Hl]]].
      right. exists ((a0,b)::l), b', a'.
      simpl; rewrite Hl; auto. }
  destruct Hxs as [|[l [b [a Hxs]]]]; subst; simpl; auto.
  rewrite each_app; simpl; intuition.
  apply sparse_subterm_lt; auto with ord.
  apply H.
  rewrite active_subterm_sparse; eauto.
Qed.


Fixpoint VF_normal (x:VForm) :=
  match x with
  | Z => True
  | N l => is_sparse l /\
           VF_matrix_proper l /\
           each (fun x => VF_normal (fst x) /\ VF_normal (snd x)) l /\
           each (fun x => VF_denote (snd x) < VF_denote (N l)) l
  end.

Lemma VF_normal_proper : forall x, VF_normal x -> VF_proper x.
Proof.
  induction x using VForm_induction; simpl; intuition.
Qed.

Local Hint Resolve VF_normal_proper: core.

Lemma active_subterm_le:
  forall xs x,
    active_subterm xs x ->
    forall f,
      normal_function f ->
      VF_denote x <= schutte_matrix f (matrix_denote xs) 0.
Proof.
  intros xs x H; induction H; simpl; intros.
  - rewrite <- schutte_matrix_base; auto with ord.
    apply normal_inflationary with (f:= fun x => schutte_column _ _ x 0); auto with ord.
  - apply IHactive_subterm; auto with ord.
Qed.

Lemma VF_normal_alt: forall l,
  VF_normal (N l) <->
    is_sparse l /\
      VF_matrix_proper l /\
      each (fun x => VF_normal (fst x) /\ VF_normal (snd x)) l /\
      (forall x, active_subterm l x -> VF_denote x < VF_denote (N l)).
Proof.
  simpl; intuition.
  - cut (forall q, each (fun x:VForm*VForm => VF_denote (snd x) < q) l ->
                   active_subterm l x ->
                   VF_denote x < q).
    { intros Hq; apply Hq; auto. }
    clear. induction l; simpl; intuition.
    + inversion H0.
    + inversion H0; subst; simpl in *; auto.
  - apply active_subterm_lt; auto.
Qed.

Definition dec_prod P Q:
  { P } + { ~P } ->
  (P -> { Q } + { ~Q }) ->
  { P /\ Q } + { ~(P /\ Q) }.
Proof.
  intuition.
Defined.

Definition dec_each A (P:A -> Prop) xs:
  (forall x, In x xs -> { P x } + { ~(P x) }) ->
  { each P xs } + { ~(each P xs) }.
Proof.
  induction xs; simpl; intuition.
  destruct (X a); intuition.
  destruct (IHxs); intuition.
Defined.

Lemma VF_dec_is_sparse: forall l, { is_sparse l } + { ~is_sparse l }.
Proof.
  induction l as [|[b a] l Hl]; simpl; intuition.
  destruct a; intuition.
  left; intuition; discriminate.
Defined.

Lemma VF_dec_normal: forall x, { VF_normal x } + { ~VF_normal x }.
Proof.
  induction x; simpl; auto.
  apply dec_prod; [ apply VF_dec_is_sparse |]. intro Hsparse.
  apply dec_prod; [ apply (VF_dec_proper (N l)) |]. intro Hproper.
  apply dec_prod.
  { clear -H.
    induction H; simpl; intuition.
    inversion p; intuition. }
  intro Hnormal.
  apply dec_each.
  intros.
  destruct (VF_dec_lt_ge (snd x) (N l)); simpl; auto.
  - clear -Hproper H0. induction l as [|[a b] l Hl]; simpl in *; subst; intuition.
    rewrite <- H1. auto.
    apply Hl; auto.
    destruct l as [|[??]?]; simpl in *; intuition.
  - right. intro.
    elim (ord_lt_irreflexive (VF_denote (snd x))).
    rewrite <- o at 2.
    auto.
Defined.

Lemma matrix_denote_eq_unique: forall xs ys f p q,
    normal_function f ->
    schutte_matrix f (matrix_denote xs) 0 ≈ schutte_matrix f (matrix_denote ys) 0 ->
    is_sparse xs ->
    is_sparse ys ->
    schutte_matrix_proper (matrix_denote xs) p (schutte_matrix f (matrix_denote xs) 0) ->
    schutte_matrix_proper (matrix_denote ys) q (schutte_matrix f (matrix_denote ys) 0) ->
    each (fun x => VF_proper (fst x) /\ VF_proper (snd x)) xs ->
    each (fun x => VF_proper (fst x) /\ VF_proper (snd x)) ys ->
    pairwise (fun x y => VF_denote (fst x) ≈ VF_denote (fst y) /\ VF_denote (snd x) ≈ VF_denote (snd y)) xs ys.
Proof.
  induction xs as [|[xb xa] xs IHxs]; simpl; intros ys f p q Hf Heq Hxs1 Hys1 Hxs2 Hys2 Hxs3 Hys3.
  { destruct ys as [|[yb ya] ys]; simpl in *.
    - apply pairwise_nil.
    - destruct Heq as [Heq1 Heq2].
      rewrite <- schutte_matrix_base in Heq2; auto with ord.
      elim (ord_lt_irreflexive (f 0)).
      rewrite <- Heq2 at 2.
      rewrite schutte_column_unroll.
      rewrite <- lub_le1.
      apply normal_increasing; auto with ord.
      rewrite addOrd_zero_r.
      rewrite VF_nonzero.
      intuition. }
  destruct ys as [|[yb ya] ys]; simpl in *.
  { destruct Heq as [Heq1 Heq2].
    rewrite <- schutte_matrix_base in Heq1; auto with ord.
    elim (ord_lt_irreflexive (f 0)).
    rewrite <- Heq1 at 2.
    rewrite schutte_column_unroll.
    rewrite <- lub_le1.
    apply normal_increasing; auto with ord.
    rewrite addOrd_zero_r.
    rewrite VF_nonzero.
    intuition. }

  assert (Hb: VF_denote xb ≈ VF_denote yb).
  { destruct (VF_dec_order xb yb) as [[Hlt|?]|Hgt]; [ intuition | intuition | exfalso | trivial | exfalso ].
    - eelim ord_lt_irreflexive. eapply ord_le_lt_trans; [ apply Heq |].
      apply schutte_matrix_lt1; intuition auto with ord.
      + simpl.
        revert H12; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq.
      + rewrite VF_nonzero; auto.
      + simpl. rewrite <- Heq. auto.
    - eelim ord_lt_irreflexive. eapply ord_lt_le_trans; [| apply (ord_eq_sym _ _ Heq) ].
      apply schutte_matrix_lt1; intuition auto with ord.
      + simpl.
        revert H13; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq.
      + rewrite VF_nonzero; auto.
      + simpl. rewrite Heq. auto. }

  assert (Ha: VF_denote xa ≈ VF_denote ya).
  { destruct (VF_dec_order xa ya) as [[Hlt|?]|Hgt]; [ intuition | intuition | exfalso | trivial | exfalso ].
    - eelim ord_lt_irreflexive. eapply ord_le_lt_trans; [ apply Heq |].
      apply ord_le_lt_trans with
        (schutte_matrix (schutte_column f (VF_denote yb) (VF_denote xa))
           (matrix_denote xs) 0).
      { apply schutte_matrix_monotone_func; auto with ord.
        intros; apply schutte_column_monotoneβ; auto with ord. apply Hb. }
      apply schutte_matrix_lt2; intuition auto with ord.
      + eauto.
      + simpl.
        revert H12; apply schutte_matrix_proper_monotone; auto with ord.
        apply Hb.
        apply Heq.
    - eelim ord_lt_irreflexive. eapply ord_lt_le_trans; [| apply (ord_eq_sym _ _ Heq) ].
      apply ord_le_lt_trans with
        (schutte_matrix (schutte_column f (VF_denote xb) (VF_denote ya))
           (matrix_denote ys) 0).
      { apply schutte_matrix_monotone_func; auto with ord.
        intros; apply schutte_column_monotoneβ; auto with ord. apply Hb. }
      apply schutte_matrix_lt2; intuition auto with ord.
      + eauto.
      + simpl.
        revert H13; apply schutte_matrix_proper_monotone; auto with ord.
        apply Hb.
        apply Heq. }

  apply pairwise_cons; simpl; intuition.
  apply IHxs with (schutte_column f (VF_denote xb) (VF_denote xa)) (VF_denote xb) (VF_denote yb);
    intuition auto with ord.
  - rewrite Heq. split; apply schutte_matrix_monotone_func; auto with ord.
    + intros; apply schutte_column_monotone_full; auto with ord.
      apply Hb. apply Ha.
    + intros; apply schutte_column_monotone_full; auto with ord.
      apply Hb. apply Ha.
  - revert H13; apply schutte_matrix_proper_monotone; auto with ord.
    apply schutte_matrix_monotone_func; auto with ord.
    intros; apply schutte_column_monotone_full; auto with ord.
    apply Hb. apply Ha.
Qed.


Lemma VF_normal_schutte_matrix_proper: forall xl,
  VF_normal (N xl) ->
  schutte_matrix_proper (matrix_denote xl) LargeVeblenOrdinal
    (schutte_matrix (addOrd 1) (matrix_denote xl) 0).
Proof.
  intros.
  assert (Hp: VF_matrix_proper xl).
  { apply VF_normal_proper in H. auto. }
  rewrite VF_matrix_proper_correct in Hp.
  destruct Hp as [Hp1 Hp2].
  assert (Hpq: forall p q,
          each (fun x : VForm * VForm => VF_denote (snd x) < q) xl ->
          schutte_matrix_proper (matrix_denote xl) p LargeVeblenOrdinal ->
          schutte_matrix_proper (matrix_denote xl) p q).
  { clear. induction xl; simpl; intuition. }
  apply Hpq; simpl in *; intuition.
Qed.

Theorem VF_normal_form_unique:
  forall x y,
    VF_normal x ->
    VF_normal y ->
    VF_denote x ≈ VF_denote y ->
    x = y.
Proof.
  induction x as [|xl IHx] using VForm_induction.
  { simpl; intros. destruct y as [|yl]; auto.
    elim (ord_lt_irreflexive (VF_denote (N yl))).
    rewrite <- H1 at 1. simpl.
    auto with ord. }
  simpl; intros y [Hx1 [Hx2 [Hx3 Hx4]]] Hy Heq.
  destruct y as [|yl]; simpl in *.
  { elim (ord_lt_irreflexive (VF_denote (N xl))).
    rewrite Heq at 1. simpl.
    auto with ord. }
  f_equal.
  destruct Hy as [Hy1 [Hy2 [Hy3 Hy4]]].

  cut (pairwise (fun x y => VF_denote (fst x) ≈ VF_denote (fst y) /\ VF_denote (snd x) ≈ VF_denote (snd y)) xl yl).
  { clear -IHx Hx3 Hy3.
    revert yl Hy3.
    induction xl as [|[xb xa] xl]; intros; inversion H; subst; simpl in *; intuition.
    f_equal; auto.
    destruct y as [yb ya]; simpl in *; f_equal; auto with ord. }

  apply matrix_denote_eq_unique with (addOrd 1) LargeVeblenOrdinal LargeVeblenOrdinal; auto with ord.
  - apply VF_normal_schutte_matrix_proper; simpl; intuition.
  - apply VF_normal_schutte_matrix_proper; simpl; intuition.
  - revert Hx3. clear. induction xl; simpl; intuition.
  - revert Hy3. clear. induction yl; simpl; intuition.
Qed.

Inductive redex : VForm -> VForm -> Prop :=
| redex_zero: forall m n b,
    redex (N (m ++ [(b,Z)] ++ n)) (N (m ++ n))

| redex_fixpoint: forall l x,
    active_subterm l x ->
    VF_matrix_proper l ->
    VF_compare (N l) x = EQ ->
    redex (N l) x.

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H.
  inversion H; subst.
  - simpl.
    repeat rewrite map_app. simpl.
    repeat rewrite schutte_matrix_app.
    simpl.
    split; apply schutte_matrix_monotone_func; auto with ord.
    + intros. rewrite schutte_column_arg0; auto with ord.
    + intros. rewrite schutte_column_arg0; auto with ord.
  - generalize (VF_compare_correct (N l) y).
    rewrite H2. intros H3. apply H3.
    rewrite VF_proper_eq; auto.
    clear -H0 H1.
    induction H0; simpl in *; intuition.
    destruct x; intuition.
    destruct xs as [|[??]?]; intuition.
Qed.

Lemma redex_size: forall x y,
    redex x y ->
    (VF_termSize x > VF_termSize y)%nat.
Proof.
  intros x y H.
  inversion H; subst.
  - simpl. repeat rewrite VF_matrixSize_app.
    simpl. lia.
  - clear -H0. induction H0; simpl in *; intuition lia.
Qed.

Inductive one_step_reduce: VForm -> VForm -> Prop :=
| reduce_redex: forall x y, redex x y -> one_step_reduce x y
| reduce_cong_arg: forall b x x' l1 l2,
    one_step_reduce x x' ->
    one_step_reduce (N (l1 ++ [(b,x)] ++ l2)) (N (l1 ++ [(b,x')] ++ l2))
| reduce_cong_idx: forall a x x' l1 l2,
    one_step_reduce x x' ->
    one_step_reduce (N (l1 ++ [(x,a)] ++ l2)) (N (l1 ++ [(x',a)] ++ l2)).

Lemma one_step_reduce_sound: forall x y, one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H.
  - apply redex_sound; auto.
  - simpl.
    repeat rewrite map_app; simpl.
    repeat rewrite schutte_matrix_app. simpl.
    destruct IHone_step_reduce.
    split; apply schutte_matrix_monotone_func; auto with ord.
  - simpl.
    repeat rewrite map_app; simpl.
    repeat rewrite schutte_matrix_app. simpl.
    destruct IHone_step_reduce.
    split; apply schutte_matrix_monotone_func; auto with ord.
    intros; apply schutte_column_monotoneβ; auto with ord.
    intros; apply schutte_column_monotoneβ; auto with ord.
Qed.

Lemma one_step_reduce_size: forall x y, one_step_reduce x y -> (VF_termSize x > VF_termSize y)%nat.
Proof.
  intros x y H. induction H.
  - apply redex_size; auto.
  - simpl; repeat rewrite VF_matrixSize_app.
    simpl; lia.
  - simpl; repeat rewrite VF_matrixSize_app.
    simpl; lia.
Qed.

Theorem step_reduce_sound: forall x y,
    clos_refl_trans _ one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H; auto with ord.
  - apply one_step_reduce_sound; auto.
  - transitivity (VF_denote y); auto.
Qed.

Lemma VF_dec_active_subterm: forall xs,
    { y | active_subterm xs y } + { each (fun x => snd x = Z) xs }.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  - destruct a0 as [y Hy].
    left. exists y. apply active_later; auto.
  - destruct a; auto.
    left. exists (N l).
    apply active_last; auto.
    discriminate.
Qed.

Theorem VF_notIsNormal_redex: forall x,
    VF_proper x ->
    (~VF_normal x <-> exists y, one_step_reduce x y).
Proof.
  induction x using VForm_induction.
  - simpl; intuition. destruct H0 as [? H0]. inversion H0; subst.
    inversion H2.
  - rewrite VF_normal_alt; intuition.
    + destruct (VF_dec_is_sparse xs).
      2:{ assert (Hl : exists l1, exists b, exists l2, xs = l1 ++ (b,Z) :: l2).
          { clear -n. induction xs as [|[p q] xs IHxs]; simpl in *; intuition.
            destruct q.
            + exists nil. exists p. exists xs. auto.
            + destruct IHxs as [l1 [b [l2 Hl]]].
              intros; apply H; auto. discriminate.
              rewrite Hl. simpl.
              exists ((p, N l)::l1), b, l2. auto. }
          destruct Hl as [l1 [b [l2 Hl]]].
          rewrite Hl.
          exists (N (l1 ++ l2)).
          apply reduce_redex.
          apply redex_zero. }
      rewrite VF_proper_eq in H0.
      destruct (dec_each _ (fun x : VForm * VForm => VF_normal (fst x) /\ VF_normal (snd x)) xs).
      * clear -H. induction xs as [|[??]?]; simpl in *; intuition.
        apply dec_prod. apply VF_dec_normal.
        intro. apply VF_dec_normal.

      * destruct (VF_dec_active_subterm xs) as [[y Hy]|Hinactive].
        ** exists y. apply reduce_redex. apply redex_fixpoint; auto.
           assert (Hy2: VF_proper y).
           { clear -H0 Hy. induction Hy; subst; simpl in *; intuition.
             destruct x.
             apply IHHy. intuition.
             destruct xs as [|[??]?]; simpl in *; intuition. }
           generalize (VF_compare_correct (N xs) y H0 Hy2).
           destruct (VF_compare (N xs) y); simpl; auto. intro.
           *** elim (ord_lt_irreflexive (VF_denote y)).
               eapply ord_le_lt_trans; [ | apply H1].
               apply active_subterm_le; auto with ord.
           *** intros. elim H2; intuition.
               replace x with y; auto.
               apply active_subterm_unique with xs; auto.
        ** destruct xs as [|[??]?]; simpl in *; intuition.
           elim H1. intros. inversion H2.

      * assert (Hl: exists l1, exists b, exists a, exists l2,
                   xs = l1 ++ (b,a) :: l2 /\
                     ((exists y, one_step_reduce b y) \/ (exists y, one_step_reduce a y))).
        { clear H2 i.
          induction xs as [|[b a] xs]; simpl in *; intuition.
          destruct (VF_dec_normal b); auto.
          - destruct (VF_dec_normal a); auto.
            + destruct H3 as [l1 [b' [a' [l2 [Hl1 Hl2]]]]]; auto.
              destruct xs as [|[??]?]; simpl in *; intuition.
              exists ((b,a)::l1), b', a', l2. rewrite Hl1.
              auto.
            + exists nil, b, a, xs; simpl; auto.
          - exists nil, b, a, xs; simpl; auto.
        }
        destruct Hl as [l1 [b [a [l2 [Hl1 Hl2]]]]].
        rewrite Hl1.
        destruct Hl2 as [[y Hy]|[y Hy]].
        ** exists (N (l1 ++ (y,a) :: l2)).
           apply reduce_cong_idx; auto.
        ** exists (N (l1 ++ (b,y) :: l2)).
           apply reduce_cong_arg; auto.
    + destruct H1 as [y Hy].
      inversion Hy; subst; clear Hy.
      * inversion H1; subst; clear H1.
        ** rewrite is_sparse_app in H3. simpl in *; intuition.
        ** generalize (VF_compare_correct (N xs) y H2).
           rewrite H9; simpl; intros.
           apply (ord_lt_irreflexive (VF_denote y)).
           rewrite <- H1 at 2; auto.
           clear -H7 H8.
           induction H7; simpl in *; intuition.
           destruct x. intuition.
           apply IHactive_subterm.
           destruct xs as [|[??]?]; simpl in *; intuition.
      * rewrite each_app in H.
        rewrite each_app in H4.
        simpl in *; intuition.
        apply H11; eauto.
      * rewrite each_app in H.
        rewrite each_app in H4.
        simpl in *; intuition.
        apply H8; eauto.
Qed.

Lemma VF_normal_no_redex: forall x,
    VF_proper x ->
    (VF_normal x <-> ~exists y, one_step_reduce x y).
Proof.
  intros x.
  generalize (VF_notIsNormal_redex x).
  destruct (VF_dec_normal x); intuition.
Qed.

Lemma redex_proper: forall x y,
    redex x y ->
    VF_proper x ->
    VF_proper y.
Proof.
  intros. inversion H; subst; simpl in *.
  - clear H.
    induction m as [|[??]?]; simpl in *; intuition.
    destruct n as [|[??]?]; intuition.
    destruct m as [|[??]?]; simpl in *; intuition.
    destruct n as [|[??]?]; intuition.
    transitivity (VF_denote b); auto.
  - clear -H1 H2.
    induction H1; simpl in *; intuition.
    destruct x. intuition.
    apply IHactive_subterm.
    destruct xs as [|[??]?]; simpl in *; intuition.
Qed.

Lemma one_step_reduce_proper: forall x y,
    one_step_reduce x y ->
    VF_proper x ->
    VF_proper y.
Proof.
  intros x y H. induction H.
  - apply redex_proper; auto.
  - repeat rewrite VF_proper_eq.
    induction l1 as [|[r s] l1 Hl1]; simpl in *; intuition.
    destruct l1 as [|[??]?]; simpl in *; intuition.
  - repeat rewrite VF_proper_eq.
    induction l1 as [|[r s] l1 Hl1]; simpl in *; intuition.
    destruct l2 as [|[??]?]; simpl in *; intuition.
    apply ord_lt_le_trans with (VF_denote x); auto.
    apply one_step_reduce_sound in H. apply H.
    destruct l1 as [|[??]?]; simpl in *; intuition.
    apply ord_le_lt_trans with (VF_denote x); auto.
    apply one_step_reduce_sound in H. apply H.
Qed.

Inductive normalizes: VForm -> VForm -> Prop :=
| normal_normalizing:
  forall x,
    ~(exists y, one_step_reduce x y) ->
    normalizes x x
| step_normalizing:
  forall x y z,
    one_step_reduce x y ->
    normalizes y z ->
    normalizes x z.

Theorem normalizes_eq: forall x y, normalizes x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H; auto with ord.
  transitivity (VF_denote y); auto with ord.
  apply one_step_reduce_sound; auto.
Qed.

Theorem normalizes_normal: forall x y, VF_proper x -> normalizes x y -> VF_normal y.
Proof.
  intros x y Hp H. induction H; auto with ord.
  rewrite VF_normal_no_redex; auto.
  apply IHnormalizes.
  apply one_step_reduce_proper with x; auto.

Qed.

Theorem strongly_normalizing: forall x, VF_proper x -> exists! y, normalizes x y.
Proof.
  induction x as [x Hind] using (well_founded_induction (Wf_nat.well_founded_ltof _ VF_termSize)).
  intro Hp.
  destruct (VF_dec_normal x).
  - eexists.
    split.
    apply normal_normalizing; auto.
    + apply VF_normal_no_redex; auto.
    + intros x' Hx.
      inversion Hx; subst; auto.
      apply VF_normal_no_redex in v; auto.
      elim v. eauto.
  - assert (exists y, one_step_reduce x y).
    { rewrite <- VF_notIsNormal_redex; auto. }
    destruct H as [y Hy].
    destruct (Hind y) as [z [Hz1 Hz2]]; auto.
    { red. apply one_step_reduce_size; auto. }
    apply one_step_reduce_proper with x; auto.
    exists z.
    split.
    + apply step_normalizing with y; auto.
    + intros q Hq.
      apply VF_normal_form_unique; auto.
      * apply normalizes_normal with y; auto.
        apply one_step_reduce_proper with x; auto.
      * eapply normalizes_normal; eauto.
      * transitivity (VF_denote x).
        ** symmetry. transitivity (VF_denote y).
           *** apply one_step_reduce_sound; auto.
           *** apply normalizes_eq; auto.
        ** apply normalizes_eq; auto.
Qed.

Fixpoint find_active_subterm (l:list (VForm * VForm)) : option VForm :=
  match l with
  | [] => None
  | [(b,a)] => Some a
  | _::xs => find_active_subterm xs
  end.

Lemma find_active_subterm_correct: forall l x,
    is_sparse l ->
    find_active_subterm l = Some x <-> active_subterm l x.
Proof.
  induction l; simpl; intuition; try discriminate.
  - inversion H0.
  - destruct l. inversion H; subst.
    apply active_last; auto.
    apply active_later; auto.
    apply IHl; simpl in *; intuition.
  - inversion H; subst.
    + destruct l as [|[??] ?]; simpl in *; intuition.
    + rewrite <- IHl in H5; auto.
      destruct l; simpl in *; intuition.
      discriminate.
Qed.

Definition Nnorm (l:list (VForm*VForm)) : VForm :=
  let l' := make_sparse l in
  match find_active_subterm l' with
  | None => N l'
  | Some x =>
      match VF_compare x (N l') with
      | LT => N l'
      | _ => x
      end
  end.

Lemma Nnorm_eq: forall l,
    VF_matrix_proper l ->
    VF_denote (Nnorm l) ≈ VF_denote (N l).
Proof.
  intros; unfold Nnorm.
  generalize (find_active_subterm_correct (make_sparse l)).
  case_eq (find_active_subterm (make_sparse l)); intros.
  - simpl in *.
    assert (Hactive: active_subterm (make_sparse l) v).
    { apply H1; auto. apply make_sparse_is_sparse. }
    assert (Hv: VF_proper v).
    { clear - Hactive H.
      induction l as [|[b a] l IHl]; simpl in *; intuition.
      - inversion Hactive.
      - destruct a; simpl in *; auto.
        + apply IHl; auto. destruct l as [|[??]?]; simpl in *; intuition.
        + inversion Hactive; subst; simpl; auto.
          apply IHl; auto.
          destruct l as [|[??]?]; simpl in *; intuition. }
    assert (Hl: VF_proper (N (make_sparse l))).
    { apply make_sparse_proper; auto. }
    generalize (VF_compare_correct v (N (make_sparse l)) Hv Hl).
    destruct (VF_compare v (N (make_sparse l))); auto.
    + simpl; intros.
      apply make_sparse_eq; auto with ord.
    + simpl; intros; auto.
      rewrite H2.
      apply make_sparse_eq; auto with ord.
    + simpl; intros.
      elim (ord_lt_irreflexive (VF_denote v)).
      eapply ord_le_lt_trans; [ | apply H2].
      apply active_subterm_le; auto with ord.
  - simpl. apply make_sparse_eq; auto with ord.
Qed.

Lemma Nnorm_normal: forall l,
    each (fun x => VF_normal (fst x) /\ VF_normal (snd x)) l ->
    VF_matrix_proper l ->
    VF_normal (Nnorm l).
Proof.
  unfold Nnorm; simpl; intros.
  generalize (find_active_subterm_correct (make_sparse l)).
  case_eq (find_active_subterm (make_sparse l)); intros.
  - assert (Hv: VF_normal v).
    { clear -H H1.
      induction l as [|[??]?]; simpl in *; intuition; try discriminate.
      destruct v1; simpl in *; intuition.
      destruct (make_sparse l); auto.
      inversion  H1; subst.
      simpl; intuition. }
    assert (Hl: VF_matrix_proper (make_sparse l)).
    { apply make_sparse_proper; auto. }
    generalize (VF_compare_correct v (N (make_sparse l)) (VF_normal_proper _ Hv) Hl).
    destruct (VF_compare v (N (make_sparse l))); auto.
    rewrite VF_normal_alt; simpl; intuition.
    + apply make_sparse_is_sparse.
    + clear -H. induction l as [|[b a] l IHl]; simpl in *; intuition.
      destruct a; simpl; auto.
    + simpl in *.
      replace x with v; auto.
      eapply active_subterm_unique; eauto.
      apply H2; auto.
      apply make_sparse_is_sparse.
  - rewrite VF_normal_alt; simpl; intuition.
    + apply make_sparse_is_sparse.
    + apply make_sparse_proper; auto.
    + clear -H. induction l as [|[b a] l IHl]; simpl in *; intuition.
      destruct a; simpl; auto.
    + simpl in *.
      apply H2 in H3; [ discriminate |].
      apply make_sparse_is_sparse.
Qed.

Fixpoint VF_normalize (x:VForm) : VForm :=
  match x with
  | Z => Z
  | N l => Nnorm (map (fun x => (VF_normalize (fst x), VF_normalize (snd x))) l)
  end.

Lemma VF_normalize_correct: forall x,
    VF_proper x ->
    VF_denote (VF_normalize x) ≈ VF_denote x /\ VF_normal (VF_normalize x).
Proof.
  induction x using VForm_induction; simpl; intros; auto with ord.
  split.
  - rewrite Nnorm_eq.
    + simpl. rewrite map_map. simpl.
      assert (Hf: forall f,
                 normal_function f ->
                 schutte_matrix f
                   (map
                      (fun x : VForm * VForm =>
                         (VF_denote (VF_normalize (fst x)), VF_denote (VF_normalize (snd x))))
                      xs) 0
                   ≈ schutte_matrix f
                   (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) xs) 0).
      { induction xs as [|[b a] xs IHxs]; simpl in *; intuition auto with ord.
        rewrite H3; auto with ord.
        - split; apply schutte_matrix_monotone_func; auto with ord.
          + intros. apply schutte_column_monotone_full; auto with ord. apply H0. apply H4.
          + intros. apply schutte_column_monotone_full; auto with ord. apply H0. apply H4.
        - destruct xs as [|[??]?]; simpl in *; intuition.
      }
      apply Hf; auto.
    + induction xs as [|[b a] xs IHxs]; simpl in *; intuition auto with ord.
      destruct xs as [|[??]?]; simpl in *; intuition.
      rewrite H5. rewrite H0. auto.
  - apply Nnorm_normal; auto.
    rewrite each_map; auto.
    + induction xs as [|[b a] xs IHxs]; simpl in *; intuition.
      apply H3.
      destruct xs as [|[??]?]; simpl in *; intuition.
    + induction xs as [|[b a] xs IHxs]; simpl in *; intuition.
      destruct xs as [|[??]?]; simpl in *; intuition.
      rewrite H5. rewrite H0. auto.
Qed.


Lemma schutte_matrix_epsilon:  forall b a l,
    VF_denote a > 0 ->
    VF_denote b > 1 ->
    expOrd ω (schutte_matrix (addOrd 1) (matrix_denote ((b,a)::l)) 0) <= (schutte_matrix (addOrd 1) (matrix_denote ((b,a)::l)) 0).
Proof.
  simpl; intros.
  apply schutte_matrix_fixpoint1; auto with ord.
  intros.
  rewrite <- (schutte_column_fixpoint (VF_denote b) _ z (addOrd 1) 1 0) at 2; auto with ord.
  rewrite schutte_column_veblen; auto with ord.
  transitivity (veblen (addOrd 1) (schutte_column (addOrd 1) (VF_denote b) (VF_denote a) z) 0).
  + rewrite veblen_onePlus; auto with ord.
  + apply veblen_monotone_func; auto with ord.
    intros. rewrite schutte_column_arg0; auto with ord.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | N [] => [Z]
  | N ((b,a)::l) =>
      match b with
      | Z => Z :: VF_decompose a
      | N [] => a ::
                  match l with
                  | [] => []
                  | (_,x)::_ => VF_decompose x
                  end
      | _ => [N ((b,a)::l)]
      end
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | [x] =>
      match x with
      | Z => N []
      | N [] => N [(N [], x)]
      | N ((b,_)::_) =>
          match b with
          | Z => N [(N [], x)]
          | N [] => N [(N [], x)]
          | _ => x
          end
      end
  | Z::xs' => N [(Z, VF_recompose xs')]
  | x::xs' => N [(N [], x); (Z, VF_recompose xs')]
  end.

Lemma VF_decompose_correct:
  forall x,
    VF_normal x ->
    each VF_normal (VF_decompose x) /\
    cantor_ordered VF_denote (VF_decompose x) /\
    VF_denote x ≈ cantor_denote VF_denote (VF_decompose x).
Proof.
  induction x using VForm_induction.
  - simpl; intuition auto with ord.
  - induction xs as [|[b a] xs IHxs]; simpl; intuition.
    + rewrite expOrd_zero; auto with ord.
    + destruct b; simpl in *; intuition.
      destruct l as [|[b' a'] l]; simpl in *; intuition.
      destruct xs as [|[??]?]; simpl in *; intuition.
    + destruct b; simpl in *; intuition.
      * case_eq (VF_decompose a); simpl; intros; auto.
        destruct xs as [|[r s]?]; simpl in *; intuition.
        ** rewrite schutte_column0 in H1.
           destruct v; [ simpl; auto with ord |].
           rewrite H15 in H16. simpl in *.
           elim (ord_lt_irreflexive (expOrd ω (VF_denote (N l0)) + cantor_denote VF_denote l)).
           rewrite addOrd_zero_r in H1.
           rewrite H16 in H1.
           eapply ord_lt_le_trans; [ apply H1 |].
           rewrite addOrd_assoc; apply addOrd_monotone; auto with ord.
           apply additively_closed_collapse; auto with ord.
           apply expOmega_additively_closed; auto.
           apply ord_le_lt_trans with (expOrd ω 0); auto with ord.
           apply expOrd_increasing; simpl; auto with ord.
        ** intuition.
           elim (ord_lt_irreflexive (VF_denote r)).
           apply ord_lt_le_trans with 0; auto with ord.
      * destruct l as [|[b' a'] l]; simpl in *; intuition.
        ** destruct xs as [|[r s]?]; simpl in *; intuition.
           destruct xs as [|[??]?]; simpl in *; intuition.
           *** case_eq (VF_decompose s); simpl; intros; auto.
               rewrite H34 in H30. simpl in *; intuition.
               destruct (VF_dec_order v a) as [[Hlt|Heq]|Hgt]; [ auto | auto | auto with ord | apply Heq |].
               eelim ord_lt_irreflexive; eapply ord_lt_le_trans; [ apply H8 |].
               transitivity
                 (schutte_column (schutte_column (addOrd 1) 1 (VF_denote a))
                    0 (VF_denote s) 0).
               { apply schutte_column_monotone_full; auto with ord.
                 intros; apply schutte_column_monotoneβ; auto with ord.
                 rewrite addOrd_zero_r. auto with ord.
                 rewrite addOrd_zero_r in H3.
                 rewrite ord_lt_unfold in H3.
                 destruct H3 as [[] H3]. auto. }
               rewrite schutte_column0.
               rewrite schutte_column_veblen; auto with ord.
               rewrite veblen_onePlus; auto with ord.
               rewrite addOrd_zero_r.
               rewrite H35 at 1.
               rewrite H35 at 1.
               rewrite H34. simpl.
               rewrite addOrd_assoc.
               apply addOrd_monotone; auto with ord.
               apply additively_closed_collapse; auto with ord.
               apply expOmega_additively_closed; auto.
               apply expOrd_increasing; auto with ord.
           *** rewrite addOrd_zero_r in H3.
               elim (ord_lt_irreflexive (VF_denote v)).
               apply ord_lt_le_trans with (VF_denote r); auto.
               rewrite ord_lt_unfold in H3. destruct H3 as [[] H3].
               rewrite H3. simpl. auto with ord.
        ** destruct xs as [|[??]?]; simpl in *; intuition.

    + destruct b; simpl in *.
      * destruct xs as [|[r s]?]; simpl in *.
        2:{ intuition.
            elim (ord_lt_irreflexive (VF_denote r)).
            apply ord_lt_le_trans with 0; auto with ord. }
        rewrite schutte_column0.
        rewrite expOrd_zero.
        apply addOrd_eq_mor; auto with ord.
        rewrite addOrd_zero_r. simpl in *; intuition.
      * intuition.
        destruct l as [|[b' a'] l]; simpl in *.
        ** destruct xs as [|[r s]?]; simpl in *.
           { transitivity (schutte_column (addOrd 1) 1 (VF_denote a) 0).
             { split; apply schutte_column_monotoneβ; auto with ord.
               rewrite addOrd_zero_r; auto with ord. }
             rewrite schutte_column_veblen; auto with ord.
             rewrite veblen_onePlus; auto with ord. }
           intuition.
           rewrite addOrd_zero_r in H3.
           rewrite ord_lt_unfold in H3. destruct H3 as [[] H3]. simpl in H3.
           destruct xs as [|[r' s']?]; simpl in *.
           2:{ simpl in *; intuition.
               elim (ord_lt_irreflexive (VF_denote r')).
               apply ord_lt_le_trans with (VF_denote r); auto.
               rewrite H3. auto with ord. }
           transitivity (schutte_column (schutte_column (addOrd 1) 1 (VF_denote a)) 0 (VF_denote s) 0).
           { split; apply schutte_column_monotone_full; auto with ord.
             intros; apply schutte_column_monotoneβ; auto with ord.
             rewrite addOrd_zero_r; auto with ord.
             intros; apply schutte_column_monotoneβ; auto with ord. }
           rewrite schutte_column0.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           apply addOrd_eq_mor; auto with ord.
           rewrite addOrd_zero_r.
           auto.
        ** rewrite addOrd_zero_r.
           split. { simpl in *; intuition auto 50 with ord. }
           apply (schutte_matrix_epsilon (N ((b',a')::l)) a xs).
           rewrite VF_nonzero; auto.
           simpl.
           rewrite <- schutte_matrix_base; auto with ord.
           apply ord_le_lt_trans with (1+0).
           { rewrite addOrd_zero_r. auto with ord. }
           apply ord_le_lt_trans with (schutte_column (addOrd 1) (VF_denote b') 0 0).
           *** apply onePlus_least_normal with (f:=fun x => schutte_column _ _ x 0); auto with ord.
           *** apply normal_increasing with (f:=fun x => schutte_column _ _ x 0); auto with ord.
               rewrite VF_nonzero; intuition.
Qed.


Lemma expOmega_denote: forall x,
    expOrd ω (VF_denote x) ≈ VF_denote (N [(N [], x)]).
Proof.
  simpl; intros.
  transitivity (schutte_column (addOrd 1) 1 (VF_denote x) 0).
  - rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    repeat rewrite addOrd_zero_r.
    auto with ord.
  - split; apply schutte_column_monotoneβ; auto with ord.
    rewrite addOrd_zero_r. auto with ord.
Qed.

Lemma VF_recompose_correct:
  forall xs,
    each VF_normal xs ->
    cantor_ordered VF_denote xs ->
    VF_normal (VF_recompose xs) /\ cantor_denote VF_denote xs ≈ VF_denote (VF_recompose xs).
Proof.
  induction xs.

  (* nil case *)
  { simpl; intuition auto with ord. }

  destruct xs.
  (* singleton case *)
  { simpl; intuition auto with ord.
    + destruct a; simpl in *; intuition.
      destruct l as [|[r s]?]; simpl; intuition auto with ord; try discriminate.
      * apply ord_lt_le_trans with (schutte_column (addOrd 1) 1 1 0).
        ** rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           repeat rewrite addOrd_zero_r.
           rewrite expOrd_one; auto with ord.
           rewrite <- lub_le2.
           auto with ord.
        ** apply schutte_column_monotone_full; auto with ord.
      * simpl in *; intuition.
        case_eq r; intros.
        { subst. simpl; intuition; try discriminate.
          destruct l as [|[r' s']?]; simpl in *; auto.
          - rewrite schutte_column0 at 1.
            rewrite schutte_column0 in H6.
            apply ord_lt_le_trans with (schutte_column (addOrd 1) 1 (1 + VF_denote s) 0).
            + rewrite schutte_column_veblen; auto with ord.
              rewrite veblen_onePlus; auto with ord.
              repeat rewrite addOrd_zero_r.
              apply expOmega_additively_closed; auto with ord.
              * apply ord_lt_le_trans with ω; auto with ord.
                rewrite <- expOrd_one' at 1; auto with ord.
              * rewrite <- normal_inflationary; auto with ord.
                rewrite addOrd_zero_r in H6. auto.
            + apply schutte_column_monotone_full; auto with ord.
              rewrite schutte_column0.
              rewrite addOrd_zero_r.
              auto with ord.
          - elim (ord_lt_irreflexive (VF_denote r')).
            apply ord_lt_le_trans with 0; intuition auto with ord. }
        destruct l0.
        { subst r. simpl in *; intuition; try discriminate.
          destruct l as [|[??]?]; simpl in *; intuition.
          { apply normal_increasing with (f:=fun x => schutte_column _ _ x 0); auto with ord. }
          rewrite addOrd_zero_r in H12.
          rewrite ord_lt_unfold in H12.
          destruct H12 as [[] H12]. simpl in H12.
          destruct l as [|[r' s']?]; simpl in *.
          2:{ elim (ord_lt_irreflexive (VF_denote r')).
              apply ord_lt_le_trans with (VF_denote v); intuition auto with ord.
              rewrite H12; auto with ord. }
          apply ord_le_lt_trans with
            (schutte_column (schutte_column (addOrd 1) 1 (VF_denote s)) 0 (VF_denote v0) 0).
          { apply schutte_column_monotone_full; auto with ord.
            intros; apply schutte_column_monotone_full; auto with ord.
            rewrite addOrd_zero_r; auto with ord. }
          rewrite schutte_column0.
          rewrite schutte_column_veblen; auto with ord.
          rewrite veblen_onePlus; auto with ord.
          rewrite addOrd_zero_r.
          apply ord_lt_le_trans with
            (schutte_column (addOrd 1) 1
               (schutte_column (schutte_column (addOrd 1) 1 (VF_denote s))
                  0 (VF_denote v0) 0)
               0).
          2:{ apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone_full; auto with ord. }
          rewrite schutte_column_veblen; auto with ord.
          rewrite veblen_onePlus; auto with ord.
          rewrite schutte_column0.
          rewrite schutte_column_veblen; auto with ord.
          rewrite veblen_onePlus; auto with ord.
          repeat rewrite addOrd_zero_r.
          apply expOmega_additively_closed; auto with ord.
          * apply normal_increasing; auto with ord.
            eapply ord_lt_le_trans; [ apply H6 |].
            transitivity (schutte_column (schutte_column (addOrd 1) 1 (VF_denote s)) 0 (VF_denote v0) 0).
            { apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone_full; auto with ord.
              rewrite addOrd_zero_r. auto with ord. }
            rewrite schutte_column0.
            rewrite schutte_column_veblen; auto with ord.
            rewrite veblen_onePlus; auto with ord.
            rewrite addOrd_zero_r. auto with ord.
          * eapply ord_lt_le_trans; [ apply H11 |].
            transitivity (schutte_column (schutte_column (addOrd 1) 1 (VF_denote s)) 0 (VF_denote v0) 0).
            { apply schutte_column_monotone_full; auto with ord.
              intros; apply schutte_column_monotone_full; auto with ord.
              rewrite addOrd_zero_r. auto with ord. }
            rewrite schutte_column0.
            rewrite schutte_column_veblen; auto with ord.
            rewrite veblen_onePlus; auto with ord.
            rewrite addOrd_zero_r. auto with ord. }

        destruct p; subst r.
        simpl in *; intuition.

    + simpl in *; intuition; subst; simpl in *.
      destruct a; simpl in *; intuition.
      * repeat rewrite addOrd_zero_r.
        rewrite expOrd_zero. auto with ord.
      * rewrite addOrd_zero_r.
        generalize (expOmega_denote (N l)).
        destruct l as [|[b a]?]; [ simpl; auto |].
        destruct b as [|lb]; [ simpl; auto |].
        destruct lb as [|[b' a']?]; [ simpl; auto |].
        intros _.
        split; auto with ord.
        simpl in H4.

        apply (schutte_matrix_epsilon (N ((b',a')::lb)) a l).
        rewrite VF_nonzero; intuition.
        simpl.
        rewrite <- schutte_matrix_base; auto with ord.
        apply ord_le_lt_trans with (1+0).
        { rewrite addOrd_zero_r. auto with ord. }
        apply ord_le_lt_trans with (schutte_column (addOrd 1) (VF_denote b') 0 0).
        *** apply onePlus_least_normal with (f:=fun x => schutte_column _ _ x 0); auto with ord.
        *** apply normal_increasing with (f:=fun x => schutte_column _ _ x 0); auto with ord.
            rewrite VF_nonzero; simpl in *; intuition. }

  destruct a.
  (* a = Z case *)
  { simpl in *; intuition.
    - destruct v; try discriminate.
      destruct xs; try discriminate.
      destruct xs; try discriminate.
      destruct l as [|[??]l]; try discriminate.
      destruct v; try discriminate.
      destruct l0; try discriminate.
    - destruct v; simpl in *.
      + rewrite schutte_column0.
        rewrite <- H7.
        rewrite expOrd_zero.
        apply addOrd_increasing.
        rewrite addOrd_zero_r.
        clear H3 H7 H4.
        induction xs; simpl in *; intuition auto with ord.
        rewrite H2 at 1.
        rewrite expOrd_zero.
        apply addOrd_increasing.
        eapply ord_lt_le_trans; [ apply IHxs |]; auto.
        destruct xs; auto with ord.
        rewrite H3. auto.
        apply addOrd_monotone; auto with ord.
      + elim (ord_lt_irreflexive 0).
        rewrite <- H at 2.
        auto with ord.
    - rewrite schutte_column0.
      rewrite <- H7.
      rewrite addOrd_zero_r.
      rewrite expOrd_zero.
      auto with ord. }

  (* general case *)
  intros.
  simpl in *; intuition; try discriminate.
  - destruct v; try discriminate.
    destruct xs; try discriminate.
    destruct xs; try discriminate.
    destruct l0 as [|[??]?]; try discriminate.
    destruct v; try discriminate.
    destruct l1 as [|[??]?]; try discriminate.
  - rewrite addOrd_zero_r; auto with ord.
  - rewrite schutte_column0.
    apply ord_le_lt_trans with
      (schutte_column (addOrd 1) (1+0)
      (schutte_matrix (addOrd 1)
         (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) l) 0)
      0).
    { apply normal_inflationary with (f:=fun x => schutte_column _ _ x 0); auto with ord. }
    apply normal_increasing; auto with ord.
    rewrite <- H10.
    rewrite addOrd_zero_r.
    rewrite <- addOrd_le1.
    apply normal_nonzero; auto with ord.
  - rewrite schutte_column0.
    rewrite <- H10 at 1.
    apply ord_lt_le_trans with
      (schutte_column (addOrd 1) 1
         (schutte_matrix (addOrd 1)
            (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) l) 0)
         (expOrd ω (VF_denote v) + cantor_denote VF_denote xs)).
    2:{ apply schutte_column_monotone_full; auto with ord.
        rewrite <- H10. rewrite addOrd_zero_r.
        auto with ord. }
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    rewrite H at 1.
    apply  addOrd_increasing; auto with ord.
    clear - H2 H6.
    revert v H2.
    induction xs; simpl in *; intuition auto with ord.
    rewrite H2 at 1.
    apply addOrd_increasing; auto with ord.
    apply addOrd_complete; auto with ord.
    clear. induction xs; unfold cantor_denote; auto with ord.
    apply addOrd_complete; auto with ord.
    clear. induction xs; unfold cantor_denote; auto with ord.

  - rewrite schutte_column0.
    transitivity (schutte_column (addOrd 1) 1
      (schutte_matrix (addOrd 1)
         (map (fun x : VForm * VForm => (VF_denote (fst x), VF_denote (snd x))) l) 0)
      (expOrd ω (VF_denote v) + cantor_denote VF_denote xs)).
    + rewrite schutte_column_veblen; auto 50 with ord.
      rewrite veblen_onePlus; auto 50 with ord.
      apply addOrd_complete; auto with ord.
      clear. induction xs; unfold cantor_denote; auto with ord.
      apply addOrd_complete; auto with ord.
      clear. induction xs; unfold cantor_denote; auto with ord.
    + split; apply schutte_column_monotone_full; auto with ord.
      rewrite addOrd_zero_r. apply H10.
      rewrite addOrd_zero_r. auto with ord.
      rewrite addOrd_zero_r. apply H10.
Qed.

Definition VF_has_cantor_decomposition : has_cantor_decomposition VF_denote VF_normal :=
  Build_has_cantor_decomposition
    VF_denote
    VF_normal
    VF_compare
    VF_decompose
    VF_recompose
    VForm_complete
    (fun x y Hx Hy => VF_compare_correct x y (VF_normal_proper x Hx) (VF_normal_proper y Hy))
    VF_decompose_correct
    VF_recompose_correct.

Definition VF_succ := cantor_succ VF_has_cantor_decomposition.
Definition VF_add  := cantor_add VF_has_cantor_decomposition.
Definition VF_mul  := cantor_mul VF_has_cantor_decomposition.
Definition VF_exp  := cantor_exp VF_has_cantor_decomposition.

Theorem VF_succ_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD) succOrd VF_succ.
Proof.
  apply cantor_succ_reflects.
Qed.

Theorem VF_add_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) addOrd VF_add.
Proof.
  apply cantor_add_reflects.
Qed.

Theorem VF_mul_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) mulOrd VF_mul.
Proof.
  apply cantor_mul_reflects.
Qed.

Theorem VF_exp_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) expOrd VF_exp.
Proof.
  apply cantor_exp_reflects.
Qed.


Definition VF_one := N [].
Definition VF_two := N [(Z, VF_one)].
Definition VF_three := N [(Z, VF_two)].

Definition VF_omega := N[(VF_one, VF_one)].

Definition VF_SAO := N [(VF_two, VF_omega)].
Definition VF_LAO := N [(VF_three, VF_one)].
Definition VF_SVO := N [(VF_omega, VF_one)].

Fixpoint VF_nat (n:nat) : VForm :=
  match n with
  | O => Z
  | S O => N []
  | S n => N [(Z, VF_nat n)]
  end.

Lemma VF_nat_eq: forall n, VF_denote (VF_nat n) ≈ natOrdSize n.
Proof.
  induction n; simpl; intuition auto with ord.
  destruct n; simpl; auto with ord.
  { rewrite addOrd_zero_r; auto with ord. }
  rewrite schutte_column0.
  rewrite IHn.
  simpl.
  rewrite addOrd_zero_r.
  apply (onePlus_finite_succ (S n)).
Qed.

Lemma VF_nat_normal: forall n, VF_normal (VF_nat n).
Proof.
  induction n; simpl; intuition.
  destruct n; simpl in *; intuition.
  destruct n; discriminate.
  rewrite schutte_column0.
  rewrite (VF_nat_eq (S n)).
  simpl.
  rewrite addOrd_zero_r.
  rewrite (onePlus_finite_succ (S n)).
  auto with ord.
Qed.

Theorem VF_natOrdSize_reflects n : reflects VForm VF_denote VF_normal ORD (natOrdSize n) (VF_nat n).
Proof.
  simpl; intuition.
  symmetry. apply VF_nat_eq.
  apply VF_nat_normal.
Qed.

Lemma VF_SVO_eq:
  VF_denote VF_SVO ≈ SmallVeblenOrdinal.
Proof.
  rewrite SVO_alt.
  unfold VF_SVO; simpl.
  transitivity (schutte_column (addOrd 1) (schutte_column (addOrd 1) 1 1 0) 1 0).
  - split; apply schutte_column_monotone_full; repeat rewrite addOrd_zero_r; auto with ord.
    apply schutte_column_monotone_full; repeat rewrite addOrd_zero_r; auto with ord.
    apply schutte_column_monotone_full; repeat rewrite addOrd_zero_r; auto with ord.
  - split; apply schutte_column_monotone_full; repeat rewrite addOrd_zero_r; auto with ord.
    + rewrite schutte_column_veblen; auto with ord.
      rewrite veblen_onePlus; auto with ord.
      rewrite addOrd_zero_r.
      apply expOrd_one'; auto with ord.
    + rewrite schutte_column_veblen; auto with ord.
      rewrite veblen_onePlus; auto with ord.
      rewrite addOrd_zero_r.
      apply expOrd_one'; auto with ord.
Qed.

Lemma VF_SmallVeblenOrdinal:
  reflects VForm VF_denote VF_normal ORD SmallVeblenOrdinal VF_SVO.
Proof.
  hnf; intros; split.
  - symmetry. apply VF_SVO_eq.
  - assert (Hn: exists H, VF_dec_normal (VF_SVO) = left H).
    { simpl; eauto. }
    destruct Hn; auto.
Qed.

Lemma schutte_column_matrix_interpolants:
  forall (b : VForm) (xs : list (VForm * VForm)) (p: Ord),
    p <= LargeVeblenOrdinal ->
    VF_proper b ->
    has_interpolants VF_denote VF_normal (VF_denote b) ->
    VF_denote b < final_index p (matrix_denote xs) ->
    schutte_matrix_proper (matrix_denote xs) p LargeVeblenOrdinal ->
    each (fun x0 : VForm * VForm => VF_proper (fst x0) /\ VF_proper (snd x0)) xs ->
    let f := schutte_matrix (addOrd 1) (matrix_denote xs) in
    normal_function f ->
    (forall x : Ord,
        complete x ->
        has_interpolants VF_denote VF_normal x ->
        has_interpolants VF_denote VF_normal (f x)) ->
    (forall a : VForm,
      VF_proper a ->
      has_interpolants VF_denote VF_normal (VF_denote a) ->
      forall x : Ord,
        complete x ->
        has_interpolants VF_denote VF_normal x ->
        has_interpolants VF_denote VF_normal (schutte_column f (VF_denote b) (VF_denote a) x)) /\
      (forall a:Ord,
          complete a ->
          has_interpolants VF_denote VF_normal a ->
          has_interpolants VF_denote VF_normal (schutte_column f (VF_denote b) a 0)).
Proof.
  induction b as [b Hindb] using (size_induction VF).
  intros xs p Hp Hb1 Hb2 Hb3 Hxs1 Hxs2 f Hf1 Hf2.
  assert (main_lemma:
           forall a : VForm,
             VF_proper a ->
             has_interpolants VF_denote VF_normal (VF_denote a) ->
             forall x : Ord,
               complete x ->
               has_interpolants VF_denote VF_normal x ->
               has_interpolants VF_denote VF_normal (schutte_column f (VF_denote b) (VF_denote a) x)).
  { induction a as [a Hinda] using (size_induction VF_denote).
    intros Ha1 Ha2.
    induction x as [x Hindx] using ordinal_induction.
    intros Hx1 Hx2.
    rewrite schutte_column_unroll.
    apply has_interpolants_lub.
    { apply Hf2; auto with ord.
      destruct (VF_normalize_correct a Ha1) as [Ha3 Ha4].
      rewrite <- Ha3.
      apply has_interpolants_add with VF_add; auto with ord.
      apply VF_add_reflects.
      rewrite Ha3.
      auto. }

    rewrite has_interpolants_unfold; simpl.
    intros i Hi.
    apply sup_lt in Hi. destruct Hi as [b' Hi].
    apply sup_lt in Hi. destruct Hi as [a' Hi].
    rewrite has_interpolants_unfold in  Hb2.
    destruct (Hb2 b') as [bq Hbq]; auto with ord.
    rewrite has_interpolants_unfold in Ha2.
    destruct (Ha2 a') as [aq Haq]; auto with ord.

    set (lim := limOrd (fun j : x => schutte_column f (VF_denote b) (VF_denote a) (sz j))).
    assert (HlimInterp: has_interpolants VF_denote VF_normal lim).
    { subst lim.
      rewrite has_interpolants_unfold. intros j Hj.
      rewrite ord_lt_unfold in Hj. simpl in Hj.
      destruct Hj as [xi Hj].
      rewrite has_interpolants_unfold in Hx2.
      destruct (Hx2 xi) as [xq Hxq]; auto with ord.

      assert (Hy: exists y, VF_proper y /\
                 VF_denote y ≈ schutte_matrix (addOrd 1) (matrix_denote (xs ++ [(b,a);(Z,xq)])) 0).
      { assert (Hproper:
                 schutte_matrix_proper (matrix_denote (xs ++ [(b,a);(Z,xq)])) p LargeVeblenOrdinal).
          { rewrite matrix_denote_app.
            rewrite schutte_matrix_proper_app.
            simpl; intuition.
            apply VForm_bounded.
            eapply ord_le_lt_trans with (VF_denote bq); auto with ord.
            apply VForm_bounded. }

          exists (N (xs ++ [(b, a); (Z, xq)])).
          split.
          - rewrite VF_proper_eq.
            rewrite VF_matrix_proper_correct; simpl; intuition.
            + rewrite each_app; simpl; intuition.
            + rewrite matrix_denote_app.
              rewrite schutte_matrix_proper_app; simpl; intuition.
              revert Hxs1.
              apply schutte_matrix_proper_monotone; auto with ord.
              eapply ord_lt_le_trans; [ apply Hb3 |].
              apply final_index_monotone; auto with ord.
              apply VForm_bounded.
              eapply ord_le_lt_trans with (VF_denote bq); auto with ord.
              apply VForm_bounded.
          - simpl. auto with ord.
      }

      destruct Hy as [y [Hy1 Hy2]].
      destruct (VF_normalize_correct y Hy1) as [Hy3 Hy4].
      exists (VF_normalize y); intuition.
      + rewrite Hy3. rewrite Hy2.
        rewrite matrix_denote_app.
        rewrite schutte_matrix_app; simpl.
        rewrite Hj.
        rewrite schutte_column0.
        apply schutte_column_monotone; auto with ord.
        rewrite addOrd_zero_r. auto.
      + rewrite Hy3. rewrite Hy2.
        rewrite ord_lt_unfold in H7.
        destruct H7 as [xi' H7].
        rewrite ord_lt_unfold. exists xi'. simpl.
        rewrite matrix_denote_app.
        rewrite schutte_matrix_app; simpl.
        rewrite schutte_column0.
        apply schutte_column_monotone; auto with ord.
        rewrite addOrd_zero_r. auto.
      + rewrite Hy3. rewrite Hy2.
        rewrite matrix_denote_app.
        rewrite schutte_matrix_app; simpl.
        rewrite schutte_column0.
        apply Hindx; auto with ord.
        rewrite addOrd_zero_r. auto with ord.
        rewrite addOrd_zero_r. auto with ord.
    }

    assert (HfixInterp: has_interpolants VF_denote VF_normal
                          (fixOrd (fun δ : Ord =>
                                     schutte_column (schutte_column f (VF_denote b) (VF_denote aq))
                                       (VF_denote bq) δ 0)
                             lim)).
    { unfold fixOrd. apply has_interpolants_sup. intro k. induction k; simpl; auto.
      set (f' := schutte_matrix (addOrd 1) (matrix_denote (xs++[(b, aq)]))).
      cut (has_interpolants VF_denote VF_normal (schutte_column f' (VF_denote bq)
                                                   (iter_f
                                                      (fun δ : Ord =>
                                                         schutte_column
                                                           (schutte_column f (VF_denote b) (VF_denote aq))
                                                           (VF_denote bq) δ 0)
                                                      lim k)
                                                   0)).
        { apply has_interpolants_eq_mor. unfold f'.
          rewrite matrix_denote_app; simpl.
          split; apply schutte_column_monotone_func; intuition auto with ord.
          + apply normal_monotone; auto with ord.
            apply schutte_matrix_normal; auto with ord.
            rewrite all_complete_app; simpl; intuition.
          + rewrite schutte_matrix_app. simpl; auto with ord.
          + apply normal_monotone; auto with ord.
            apply schutte_matrix_normal; auto with ord.
            rewrite all_complete_app; simpl; intuition.
          + rewrite schutte_matrix_app. simpl; auto with ord. }

        destruct (Hindb bq) with (xs:=xs++[(b, aq)]) (p:=p) as [_ Hind]; intuition auto with ord.
        - rewrite matrix_denote_app. simpl.
          rewrite final_index_last. auto with ord.
        - rewrite matrix_denote_app. simpl.
          rewrite schutte_matrix_proper_app; simpl; intuition.
          apply VForm_bounded.
        - rewrite each_app; simpl; intuition.
        - intros. rewrite matrix_denote_app.
          rewrite schutte_matrix_app.
          simpl.
          apply Hinda; intuition auto with ord.
        - apply Hind; auto with ord.
          apply iter_f_complete; auto with ord.
          unfold lim. apply lim_complete; auto with ord.
          apply directed_monotone; auto with ord.
          destruct x; apply Hx1.
    }

    rewrite has_interpolants_unfold in HfixInterp.
    destruct (HfixInterp i) as [z Hz].
    { eapply ord_lt_le_trans; [ apply Hi |].
      apply fixOrd_monotone_func; auto with ord.
      intros. apply schutte_column_monotone_full; intuition auto with ord. }
    exists z. intuition.
    rewrite ord_lt_unfold in H4.
    destruct H4 as [b'' Hb''].
    rewrite <- (sup_le _ _ b'').
    rewrite ord_lt_unfold in H6.
    destruct H6 as [a'' Ha''].
    rewrite <- (sup_le _ _ a'').
    eapply ord_lt_le_trans; [ apply H7 |].
    apply fixOrd_monotone_func; auto with ord.
    intros; apply schutte_column_monotone_full; auto with ord.
  }

  split; auto.
  induction a as [a Hinda] using ordinal_induction.
  intros Ha1 Ha2.
  rewrite schutte_column_unroll.
  apply has_interpolants_lub.
  { apply Hf2; auto with ord.
    rewrite addOrd_zero_r; auto. }

  rewrite has_interpolants_unfold.
  intros i Hi.
  apply sup_lt in Hi. destruct Hi as [b' Hi].
  apply sup_lt in Hi. destruct Hi as [a' Hi].

  rewrite has_interpolants_unfold in  Hb2.
  destruct (Hb2 b') as [bq Hbq]; auto with ord.
  rewrite has_interpolants_unfold in Ha2.
  destruct (Ha2 a') as [aq Haq]; auto with ord.

  assert (Hfix: has_interpolants VF_denote VF_normal
                  (fixOrd (fun δ : Ord =>
                             schutte_column (schutte_column f (VF_denote b) (VF_denote aq))
                               (VF_denote bq) δ 0)
                     0)).
  { unfold fixOrd. apply has_interpolants_sup. intro k. induction k; simpl; auto.
    { rewrite has_interpolants_unfold. intros j Hj.
      rewrite ord_lt_unfold in Hj. destruct Hj as [[] _]. }
    set (f' := schutte_matrix (addOrd 1) (matrix_denote (xs++[(b, aq)]))).
    cut (has_interpolants VF_denote VF_normal (schutte_column f' (VF_denote bq)
                                                 (iter_f
                                                    (fun δ : Ord =>
                                                       schutte_column
                                                         (schutte_column f (VF_denote b) (VF_denote aq))
                                                         (VF_denote bq) δ 0)
                                                    0 k)
                                                 0)).
    { apply has_interpolants_eq_mor. unfold f'.
      rewrite matrix_denote_app; simpl.
      split; apply schutte_column_monotone_func; auto with ord.
      + intros. apply normal_monotone; auto.
        apply schutte_matrix_normal; auto with ord.
        rewrite all_complete_app; simpl; intuition; auto.
      + intros. rewrite schutte_matrix_app; simpl; auto with ord.
      + intros. apply normal_monotone; auto.
        apply schutte_matrix_normal; auto with ord.
        rewrite all_complete_app; simpl; intuition; auto.
      + intros. rewrite schutte_matrix_app; simpl; auto with ord. }

    destruct (Hindb bq) with (xs:=xs++[(b, aq)]) (p:=p) as [_ Hind]; intuition auto with ord.
    + rewrite matrix_denote_app. simpl.
      rewrite final_index_last.
      auto.
    + rewrite matrix_denote_app.
      rewrite schutte_matrix_proper_app; simpl; intuition.
      apply VForm_bounded.
    + rewrite each_app; simpl; intuition.
    + rewrite matrix_denote_app.
      rewrite schutte_matrix_app; simpl.
      apply main_lemma; auto.
    + apply Hind; auto with ord.
      apply iter_f_complete; auto with ord.
  }

  rewrite has_interpolants_unfold in Hfix.
  destruct (Hfix i) as [q Hq].
  { eapply ord_lt_le_trans; [ apply Hi |].
    eapply ord_le_trans with (fixOrd _ 0); [ apply fixOrd_monotone; auto with ord |].
    { apply limit_least; intros []. }
    apply fixOrd_monotone_func; auto with ord.
    intros. apply schutte_column_monotone_full; auto with ord.
    intros; apply schutte_column_monotone; intuition auto with ord.
    intuition auto with ord. }
  exists q; intuition.
  eapply ord_lt_le_trans; [ apply H7 |].
  rewrite ord_lt_unfold in H4.
  destruct H4 as [b'' H4].
  rewrite ord_lt_unfold in H6.
  destruct H6 as [a'' ?].
  rewrite <- (sup_le _ _ b'').
  rewrite <- (sup_le _ _ a'').
  eapply ord_le_trans with (fixOrd _ 0); [| apply fixOrd_monotone; auto with ord].
  apply fixOrd_monotone_func; auto with ord.
  intros; apply schutte_column_monotone_full; auto with ord.
Qed.

Lemma schutte_matrix_interpolants_aux:
  forall ys xs p,
    p <= LargeVeblenOrdinal ->
    schutte_matrix_proper (matrix_denote xs) p LargeVeblenOrdinal ->
    each (fun x0 : VForm * VForm => VF_proper (fst x0) /\ VF_proper (snd x0)) xs ->
    let f := schutte_matrix (addOrd 1) (matrix_denote xs) in
    (forall x,
        complete x ->
        has_interpolants VF_denote VF_normal x ->
        has_interpolants VF_denote VF_normal (f x)) ->
    schutte_matrix_proper (matrix_denote ys) (final_index p (matrix_denote xs)) LargeVeblenOrdinal ->
    each (fun x => VF_normal (fst x) /\ VF_normal (snd x)) ys ->
    each (fun x => has_interpolants VF_denote VF_normal (VF_denote (fst x)) /\
                   has_interpolants VF_denote VF_normal (VF_denote (snd x))) ys ->
    has_interpolants VF_denote VF_normal (schutte_matrix f (matrix_denote ys) 0).
Proof.
  induction ys as [|[b a] ys IHys]; intros xs p Hp Hxs1 Hxs2 f Hf.
  - simpl; intuition. apply Hf; auto with ord.
    rewrite has_interpolants_unfold.
    intros. rewrite ord_lt_unfold in H2. destruct H2 as [[] _].
  - simpl. intros [Hb1 [Ha1 Hys1]] [[Hb2 Ha2] Hys2] [[Hb3 Ha3] Hys3].
    set (f' := (schutte_matrix (addOrd 1) (matrix_denote (xs ++ [(b, a)])))).
    assert (Hf1: normal_function f).
    { unfold f. apply schutte_matrix_normal; auto with ord. }
    assert (Hf': normal_function f').
    { unfold f'. apply schutte_matrix_normal; auto with ord. }
    cut (has_interpolants VF_denote VF_normal (schutte_matrix f' (matrix_denote ys) 0)).
    { apply has_interpolants_eq_mor.
      unfold f' in *. rewrite matrix_denote_app.
      split; apply schutte_matrix_monotone_func; auto with ord.
      + intros; repeat rewrite schutte_matrix_app; simpl. auto with ord.
      + intros; repeat rewrite schutte_matrix_app; simpl. auto with ord.
      + intros; apply normal_monotone; auto with ord.
        apply schutte_matrix_normal. rewrite all_complete_app.
        simpl; intuition auto with ord. auto with ord.
      + intros; repeat rewrite schutte_matrix_app; simpl. auto with ord.
    }
    apply IHys with p; auto with ord; clear IHys.
    + rewrite matrix_denote_app.
      rewrite schutte_matrix_proper_app; simpl; intuition.
    + rewrite each_app; simpl; intuition.
    + intros x Hx1 Hx2.
      rewrite matrix_denote_app.
      rewrite schutte_matrix_app. fold f.
      simpl in *.
      apply schutte_column_matrix_interpolants with p; auto with ord.
    + rewrite matrix_denote_app. simpl.
      rewrite final_index_last. auto.
Qed.

Lemma schutte_matrix_interpolants:
  forall ys,
    VF_matrix_proper ys ->
    each (fun x => VF_normal (fst x) /\ VF_normal (snd x)) ys ->
    each (fun x => has_interpolants VF_denote VF_normal (VF_denote (fst x)) /\
                   has_interpolants VF_denote VF_normal (VF_denote (snd x))) ys ->
    has_interpolants VF_denote VF_normal (schutte_matrix (addOrd 1) (matrix_denote ys) 0).
Proof.
  intros.
  apply (schutte_matrix_interpolants_aux ys [] LargeVeblenOrdinal); simpl; intuition auto with ord.
  - intros. apply onePlus_interpolants with Z (VF_add VF_one); auto.
    + simpl; auto with ord.
    + apply (reflects_app ORD (ORD ==> ORD)).
      * apply VF_add_reflects.
      * simpl; intuition.
        rewrite addOrd_zero_r; auto with ord.
  - apply VF_matrix_proper_correct in H; intuition.
Qed.

Theorem schutte_matrix_has_all_interpolants:
  has_all_interpolants VF_denote VF_normal.
Proof.
  hnf.
  induction a as [a Hinda] using (size_induction VF). intro Ha.
  destruct a; simpl in *.
  { hnf; simpl; intuition.
    elim (ord_lt_irreflexive 0).
    eapply ord_le_lt_trans with i; auto with ord. }
  apply schutte_matrix_interpolants; intuition.
  cut (forall xs,
          each (fun x : VForm * VForm => VF_normal (fst x) /\ VF_normal (snd x)) xs ->
          each
            (fun x : VForm * VForm =>
               VF_denote (snd x) <
                 schutte_matrix (addOrd 1)
                   (map (fun x0 : VForm * VForm => (VF_denote (fst x0), VF_denote (snd x0))) l)
                   0)
            xs ->
          (forall b a, In (b,a) xs -> VF_denote b < schutte_matrix (addOrd 1) (matrix_denote l) 0) ->
          each (fun x : VForm * VForm =>
                  has_interpolants VF_denote VF_normal (VF_denote (fst x)) /\
                    has_interpolants VF_denote VF_normal (VF_denote (snd x)))
            xs).
  { intro Hxs. apply Hxs; auto.
    intros; apply matrix_index_lt with a; auto with ord.
    clear -H H2. rewrite VF_nonzero.
    induction l as [|[??]?]; simpl in *; subst; intuition.
    inversion H; subst. auto. }

  induction xs; simpl in *; intuition.
  - apply Hinda; auto with ord.
    apply H5 with (snd a); destruct a; auto.
  - apply H10; intuition.
    apply H5 with a0; auto.
Qed.

Definition VF_nadd := cantor_nadd VF_has_cantor_decomposition.

Theorem VF_reflects_nadd: reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) naddOrd VF_nadd.
Proof.
  apply cantor_nadd_reflects.
  apply schutte_matrix_has_all_interpolants.
Qed.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem VF_has_enough_notations (EM:excluded_middle) :
  forall x:Ord, x < LargeVeblenOrdinal -> exists! a:VForm, VF_normal a /\ VF_denote a ≈ x.
Proof.
  intros.
  destruct (LVO_proper_VForm x) as [a [Ha1 Ha2]]; auto.
  destruct (VF_normalize_correct a) as [Ha3 Ha4]; auto.
  assert (Hreplete: has_enough_notations VF_denote VF_normal).
  { apply has_interpolants_has_enough_notations with (A:=VForm) (f:=VF_denote) (P:=VF_normal); auto.
    apply schutte_matrix_has_all_interpolants. }
  destruct (Hreplete (VF_normalize a) x) as [c [Hc1 Hc2]]; auto.
  - rewrite Ha3. auto.
  - exists c; auto.
    hnf; intuition.
    apply VF_normal_form_unique; auto.
    rewrite Hc2. symmetry; auto.
Qed.
