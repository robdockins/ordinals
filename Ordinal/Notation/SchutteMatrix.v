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

Lemma VForm_le_LVO: LargeVeblenOrdinal <= VF.
Proof.
  rewrite LVO_alt.
  unfold fixOrd.
  apply sup_least. intro k.
  apply ord_lt_le.
  induction k; simpl; auto with ord.
  - rewrite ord_lt_unfold. exists Z; simpl; auto with ord.
  - rewrite ord_lt_unfold in IHk. destruct IHk as [v Hv].
    rewrite ord_lt_unfold.
    exists (N [(v, N [])]); simpl.
    apply schutte_column_monotone_full; auto with ord.
Qed.

Theorem VF_LVO : VF ≈ LargeVeblenOrdinal.
Proof.
  split.
  - apply limit_least. intro i. apply VForm_bounded.
  - apply VForm_le_LVO.
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
