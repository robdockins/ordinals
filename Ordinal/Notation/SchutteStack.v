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

Scheme All for list.

Inductive VForm :=
| Z
| N : list VForm -> VForm.

Fixpoint VF_termSize (x:VForm) : nat :=
  match x with
  | Z   => 0%nat
  | N l => 1%nat + fold_right (fun a b => 1 + a + b)%nat 0%nat (map VF_termSize l)
  end.

Definition VF_listSize (xs:list VForm) : nat :=
  fold_right (fun a b => 1 + a + b)%nat 0%nat (map VF_termSize xs).

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

Theorem VForm_complete: forall x:VForm, complete (VF_denote x).
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

Lemma VForm_list_complete: forall xs, list_complete (map VF_denote xs).
Proof.
  apply VForm_each_complete.
Qed.

Local Hint Resolve VForm_complete VForm_each_complete VForm_list_complete: core.

Lemma VF_listSize_app: forall xs ys,
    VF_listSize (xs++ys) = (VF_listSize xs + VF_listSize ys)%nat.
Proof.
  unfold VF_listSize.
  induction xs; simpl; intuition.
  rewrite IHxs; simpl; lia.
Qed.

Theorem VForm_bounded : forall x:VForm, VF_denote x < SmallVeblenOrdinal.
Proof.
  intro x.
  induction x using VForm_induction.

  - simpl. apply SVO_nonzero.
  - simpl.
    apply SVO_stack_unreachable'; auto with ord.
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

Inductive active_subterm : list VForm -> VForm -> Prop :=
| active_last : forall x xs,
    x <> Z ->
    each (fun x => x = Z) xs ->
    active_subterm (x::xs) x

| active_later: forall z x xs,
    active_subterm xs z ->
    active_subterm (x::xs) z.

Lemma active_subterm_nonzero: forall xs b,
    active_subterm xs b -> b <> Z.
Proof.
  induction xs; simpl; intros b Hactive.
  - inversion Hactive.
  - inversion Hactive; intuition; subst; auto.
    apply IHxs with Z; auto.
Qed.

Lemma active_subterm_all_zeros: forall xs b,
    each (fun x : VForm => x = Z) xs ->
    active_subterm xs b ->
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
  induction xs as [|x xs IHxs]; simpl; intros a b Ha Hb.
  - inversion Ha.
  - inversion Ha; subst; inversion Hb; subst; auto.
    elim (active_subterm_all_zeros xs b); auto.
    elim (active_subterm_all_zeros xs a); auto.
Qed.

Fixpoint sparse_stack (xs:list VForm) : list (nat * VForm) :=
  match xs with
  | [] => []
  | Z::xs => sparse_stack xs
  | x::xs => (length xs, x) :: sparse_stack xs
  end.

Fixpoint sparse_matrix (xs: list (nat * VForm)) : list (Ord * Ord) :=
  match xs with
  | [] => []
  | ((b,a)::xs) => (natOrdSize b, VF_denote a) :: sparse_matrix xs
  end.

Definition sparse_term_size (xs: list (nat * VForm)) : nat :=
  fold_right (fun a b => 1 + a + b)%nat 0%nat (map (fun x => VF_termSize (snd x)) xs).

Lemma sparse_matrix_eq: forall xs f x0,
    normal_function f ->
    complete x0 ->
    schutte_stack f (map VF_denote xs) x0 ≈ schutte_matrix f (sparse_matrix (sparse_stack xs)) x0.
Proof.
  induction xs as [|x xs IHxs]; simpl; intuition auto with ord.
  destruct x; simpl.
  - rewrite IHxs; auto with ord.
    split; apply schutte_matrix_monotone_func; auto with ord.
    + intros. rewrite schutte_column_arg0; auto with ord.
    + intros. rewrite schutte_column_arg0; auto with ord.
  - rewrite length_map.
    rewrite IHxs; auto with ord.
Qed.

Lemma sparse_matrix_size: forall xs,
    (sparse_term_size (sparse_stack xs) <= VF_listSize xs)%nat.
Proof.
  unfold VF_listSize, sparse_term_size.
  induction xs; simpl; intuition.
  destruct a; simpl in *; auto.
  lia.
Qed.

Fixpoint is_sparse (xs:list (nat * VForm)) :=
  match xs with
  | [] => True
  | ((b,a)::xs) => a <> Z /\ is_sparse xs
  end.

Lemma sparse_stack_is_sparse: forall xs, is_sparse (sparse_stack xs).
Proof.
  induction xs; simpl; intuition.
  destruct a; simpl; intuition.
  discriminate.
Qed.

Lemma all_zero_sparse_stack: forall xs,
    each (fun x : VForm => x = Z) xs <-> sparse_stack xs = [].
Proof.
  induction xs; simpl; intuition subst; auto.
  destruct a; intuition; discriminate.
  destruct a; intuition; discriminate.
Qed.

Lemma active_subterm_sparse:
  forall xs x,
    active_subterm xs x <-> exists l n, sparse_stack xs = (l ++ [(n,x)]).
Proof.
  induction xs; simpl; intuition.
  - inversion H.
  - firstorder.
    destruct x0; discriminate.
  - inversion H; subst.
    + exists [], (length xs).
      simpl.
      destruct x; intuition.
      apply all_zero_sparse_stack in H4. rewrite H4. auto.
    + rewrite IHxs in H3.
      destruct H3 as [l [n ?]].
      destruct a; simpl.
      * exists l. exists n. auto.
      * exists ((length xs, N l0)::l). exists n. simpl.
        rewrite H0.
        auto.
  - destruct H as [l [n ?]].
    destruct a; simpl in *.
    + apply active_later. rewrite IHxs. eauto.
    + destruct l; simpl in *; inversion H; subst.
      * apply active_last. discriminate.
        rewrite all_zero_sparse_stack. auto.
      * apply active_later. rewrite IHxs.
        inversion H; subst.
        eauto.
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


Fixpoint sparse_trivial (xs:list (nat * VForm)) :
  { trivial_matrix (sparse_matrix xs) } + { nontrivial_matrix (sparse_matrix xs) }.

  refine (
  match xs with
  | [] => left _
  | x::xs =>
      match x with
      | (_,Z) =>
          match sparse_trivial xs with
          | left H => left _
          | right H => right _
          end
      | (_,N _) => right _
      end
  end).

  - hnf; auto.
  - hnf; simpl; split; auto with ord.
  - hnf; simpl; auto.
  - hnf; simpl. left. auto with ord.
Defined.

Lemma all_complete_sparse_matrix: forall xs, all_complete (sparse_matrix xs).
Proof.
  induction xs as [|[n x] xs IHxs]; simpl; intuition.
Qed.

Lemma sparse_stack_proper: forall xs,
    schutte_matrix_proper (sparse_matrix (sparse_stack xs)) (natOrdSize (length xs)) SmallVeblenOrdinal.
Proof.
  induction xs as [|x xs IHxs]; simpl; intuition.
  destruct x; simpl; intuition auto with ord.
  - apply schutte_matrix_proper_monotone with (natOrdSize (length xs)) SmallVeblenOrdinal; auto with ord.
  - apply (VForm_bounded (N l)).
Qed.

Local Hint Resolve all_complete_sparse_matrix: core.

Lemma nontrivial_matrix_app: forall m n,
  nontrivial_matrix (m++n) <-> nontrivial_matrix m \/ nontrivial_matrix n.
Proof.
  induction m; simpl; intuition.
  - rewrite IHm in H0; intuition.
  - rewrite IHm; intuition.
  - rewrite IHm; intuition.
Qed.

Lemma sparse_matrix_app: forall m n,
    sparse_matrix (m++n) = sparse_matrix m ++ sparse_matrix n.
Proof.
  induction m; simpl; intuition.
  rewrite IHm; auto.
Qed.

Lemma is_sparse_app: forall m n,
    is_sparse (m++n) <-> is_sparse m /\ is_sparse n.
Proof.
  induction m; simpl; intuition.
  rewrite IHm in H1. intuition.
  rewrite IHm in H1. intuition.
  rewrite IHm; intuition.
Qed.


Section sparse_compare.
  Variable n:nat.
  Variable compare_rec :
    forall x y, (VF_termSize x + VF_termSize y < n)%nat -> { o | ordering_correct o (VF_denote x) (VF_denote y) }.

  Fixpoint check_lt xs ytop {struct xs} :
    (sparse_term_size xs + VF_termSize ytop < n)%nat ->
    { o | confirm_lt o (sparse_matrix xs) (VF_denote ytop) }.

    refine (
    match xs as xs' return
          (sparse_term_size xs' + VF_termSize ytop < n)%nat ->
          { o | confirm_lt o (sparse_matrix xs') (VF_denote ytop) }
    with
    | [] => fun H => exist _ LT _
    | (b,a)::xs =>
        fun H =>
          let (o, Hcomp) := compare_rec a ytop _ in
          match o as o' return ordering_correct o' (VF_denote a) (VF_denote ytop) -> _ with
          | LT =>
              fun Hcomp =>
                let (o, Hrec) := check_lt xs ytop _ in exist _ o _
          | EQ =>
              fun Hcomp =>
                if sparse_trivial xs then exist _ EQ _ else exist _ GT _
          | GT =>
              fun Hcomp => exist _ GT _
        end Hcomp
    end).

    - apply confirm_lt_nil.
    - unfold sparse_term_size in *; simpl in *. lia.
    - unfold sparse_term_size in *; simpl in *. lia.
    - simpl in *. apply confirm_lt_lt; auto.
    - simpl in *. apply confirm_lt_eq1; auto.
    - simpl in *. apply confirm_lt_eq2; auto.
    - simpl in *. apply confirm_lt_gt; auto.
  Defined.

  Fixpoint sparse_compare xtop xs ys ytop f (Hf: normal_function f):
    (sparse_term_size xs + sparse_term_size ys < n)%nat ->
    (sparse_term_size xs + VF_termSize ytop < n)%nat ->
    (sparse_term_size ys + VF_termSize xtop < n)%nat ->
    is_sparse xs ->
    is_sparse ys ->
    VF_denote xtop ≈ schutte_matrix f (sparse_matrix xs) 0 ->
    VF_denote ytop ≈ schutte_matrix f (sparse_matrix ys) 0 ->
    { o | schutte_matrix_compare o f (sparse_matrix xs) (sparse_matrix ys) }.

  refine (match xs as xs', ys as ys' return
    (sparse_term_size xs' + sparse_term_size ys' < n)%nat ->
    (sparse_term_size xs' + VF_termSize ytop < n)%nat ->
    (sparse_term_size ys' + VF_termSize xtop < n)%nat ->
    is_sparse xs' ->
    is_sparse ys' ->
    VF_denote xtop ≈ schutte_matrix f (sparse_matrix xs') 0 ->
    VF_denote ytop ≈ schutte_matrix f (sparse_matrix ys') 0 ->
    { o | schutte_matrix_compare o f (sparse_matrix xs') (sparse_matrix ys') }
  with
  | [], [] => fun _ _ _ _ _ _ _ => exist _ EQ _
  | [], (yb,ya)::_ => fun _ _ _ _ _ _ _ => exist _ LT _
  | (xb,xa)::_, [] => fun _ _ _ _ _ _ _ => exist _ GT _
  | (xb,xa)::xs, (yb,ya)::ys =>
      fun Hsz1 Hsz2 Hsz3 Hspx Hspy Hxeq Hyeq =>
        match Compare_dec.lt_eq_lt_dec xb yb with
        | inleft (left Hlt) => let (o, Hconfirm) := check_lt ((xb,xa)::xs) ytop _ in exist _ o _
        | inleft (right Heq) =>
            let (o, Hcomp) := compare_rec xa ya _ in
            match o as o' return ordering_correct o' (VF_denote xa) (VF_denote ya) -> _ with
            | LT => fun Hcomp => let (o, Hconfirm) := check_lt xs ytop _ in exist _ o _
            | EQ => fun Hcomp =>
                      let (o, Hcomp2) :=
                        sparse_compare xtop xs ys ytop (schutte_column f (natOrdSize xb) (VF_denote xa)) _ _ _ _ _ _ _ _                       in exist _ o _
            | GT => fun Hcomp => let (o, Hconfirm) := check_lt ys xtop _ in exist _ (ordering_swap o) _
            end Hcomp
        | inright Hgt => let (o, Hconfirm) := check_lt ((yb,ya)::ys) xtop _ in exist _ (ordering_swap o) _
        end
   end).

  - simpl. apply mat_comp_nil_nil.
  - apply mat_comp_nil_left.
    simpl in *; rewrite VF_nonzero; intuition.
  - apply mat_comp_nil_right.
    simpl in *; rewrite VF_nonzero; intuition.
  - simpl in *. lia.
  - simpl in *. apply mat_comp_index_lt; auto with ord.
    + apply natOrdSize_increasing; auto.
    + rewrite VF_nonzero; intuition.
    + simpl. rewrite <- Hyeq. auto.
  - unfold sparse_term_size in *. simpl in *. lia.
  - unfold sparse_term_size in *. simpl in *. lia.
  - simpl in *. apply mat_comp_arg_lt; subst; auto with ord.
    simpl. rewrite <- Hyeq; auto.
  - auto with ord.
  - unfold sparse_term_size in *. simpl in *. lia.
  - unfold sparse_term_size in *. simpl in *. lia.
  - unfold sparse_term_size in *. simpl in *. lia.
  - simpl in *; intuition.
  - simpl in *; intuition.
  - simpl in *; auto.
  - simpl in *. rewrite Hyeq. subst.
    split; apply schutte_matrix_monotone_func; auto with ord.
    + intros. apply schutte_column_monotone_full; auto with ord.
      apply Hcomp.
    + intros. apply schutte_column_monotone_full; auto with ord.
      apply Hcomp.
  - simpl in *. apply mat_comp_eq; subst; auto with ord.
  - unfold sparse_term_size in *. simpl in *. lia.
  - simpl in *. apply mat_comp_arg_gt; subst; auto with ord.
    simpl. rewrite ordering_swap_inv.
    rewrite <- Hxeq. auto.
  - simpl in *; lia.
  - simpl in *. apply mat_comp_index_gt; auto with ord.
    + apply natOrdSize_increasing; auto.
    + rewrite VF_nonzero; intuition.
    + simpl. rewrite ordering_swap_inv.
      rewrite <- Hxeq. auto.
  Defined.
End sparse_compare.

Fixpoint VF_compare_loop x y
  (Wf: Acc lt (VF_termSize x + VF_termSize y)%nat) {struct Wf} :
  { o | ordering_correct o (VF_denote x) (VF_denote y) }.

  refine (
  match Wf with
  | Acc_intro _ H =>
      match x as x', y as y'
            return x = x' -> y = y' -> { o | ordering_correct o (VF_denote x') (VF_denote y') }
      with
      | Z, Z => fun _ _ => exist _ EQ _
      | Z, N _ => fun _ _ => exist _ LT _
      | N _, Z => fun _ _ => exist _ GT _
      | N xs, N ys => fun Hx Hy =>
          let (o, Ho) :=
            sparse_compare
              ((VF_termSize x + VF_termSize y)%nat)
              (fun a b Hab => VF_compare_loop a b (H _ Hab))
              (N xs) (sparse_stack xs) (sparse_stack ys) (N ys)
              (addOrd 1) onePlus_normal
              _ _ _ _ _ _ _
          in exist _ o _
      end (eq_refl _) (eq_refl _)
  end).

  - simpl; auto with ord.
  - simpl; auto with ord.
  - simpl; auto with ord.
  - subst; simpl.
    generalize (sparse_matrix_size xs).
    generalize (sparse_matrix_size ys).
    unfold VF_listSize. simpl in *; lia.
  - subst; simpl.
    generalize (sparse_matrix_size xs).
    unfold VF_listSize. simpl in *; lia.
  - subst; simpl.
    generalize (sparse_matrix_size ys).
    unfold VF_listSize. simpl in *; lia.
  - apply sparse_stack_is_sparse.
  - apply sparse_stack_is_sparse.
  - simpl. apply sparse_matrix_eq; auto with ord.
  - simpl. apply sparse_matrix_eq; auto with ord.
  - simpl. repeat rewrite sparse_matrix_eq; auto with ord.
    eapply schutte_matrix_compare_correct; auto with ord.
    + apply sparse_stack_proper.
    + apply sparse_stack_proper.
Defined.

Definition VF_compare x y : ordering :=
  proj1_sig (VF_compare_loop x y (Wf_nat.lt_wf (VF_termSize x + VF_termSize y)%nat)).

Theorem VF_compare_correct :
  forall x y, ordering_correct (VF_compare x y) (VF_denote x) (VF_denote y).
Proof.
  intros. unfold VF_compare.
  destruct (VF_compare_loop x y (Wf_nat.lt_wf (VF_termSize x + VF_termSize y)%nat)).
  simpl; auto.
Qed.

Theorem VF_dec_order: forall x y,
    { VF_denote x < VF_denote y } + { VF_denote x ≈ VF_denote y } + { VF_denote x > VF_denote y }.
Proof.
  intros x y.
  generalize (VF_compare_correct x y).
  destruct (VF_compare x y); auto.
Defined.

Lemma each_lt_mono: forall (xs: list (nat * VForm)) p q,
    p <= q ->
    each (fun x => VF_denote (snd x) < p) xs ->
    each (fun x => VF_denote (snd x) < q) xs.
Proof.
  induction xs as [|[b a] xs IHxs]; simpl; intuition.
  - rewrite <- H. auto.
  - apply IHxs with p; auto.
Qed.

Lemma sparse_stack_eq_unique: forall xs ys f p q,
    normal_function f ->
    schutte_matrix f (sparse_matrix xs) 0 ≈ schutte_matrix f (sparse_matrix ys) 0 ->
    is_sparse xs ->
    is_sparse ys ->
    schutte_matrix_proper (sparse_matrix xs) p (schutte_matrix f (sparse_matrix xs) 0) ->
    schutte_matrix_proper (sparse_matrix ys) q (schutte_matrix f (sparse_matrix ys) 0) ->
    pairwise (fun x y => fst x = fst y /\ VF_denote (snd x) ≈ VF_denote (snd y)) xs ys.
Proof.
  induction xs as [|[xb xa] xs IHxs]; simpl; intros ys f p q Hf Heq Hxs1 Hys1 Hxs2 Hys2.
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

  assert (Hb: xb = yb).
  { destruct (Compare_dec.lt_eq_lt_dec xb yb) as [[Hlt|?]|Hgt]; [ exfalso | trivial | exfalso ].
    - eelim ord_lt_irreflexive. eapply ord_le_lt_trans; [ apply Heq |].
      apply schutte_matrix_lt1; intuition auto with ord.
      + simpl.
        revert H8; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq.
      + rewrite VF_nonzero; auto.
      + apply natOrdSize_increasing; auto.
      + simpl. rewrite <- Heq. auto.
    - eelim ord_lt_irreflexive. eapply ord_lt_le_trans; [| apply (ord_eq_sym _ _ Heq) ].
      apply schutte_matrix_lt1; intuition auto with ord.
      + simpl.
        revert H9; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq.
      + rewrite VF_nonzero; auto.
      + apply natOrdSize_increasing; auto.
      + simpl. rewrite Heq. auto. }
  subst.

  assert (Ha: VF_denote xa ≈ VF_denote ya).
  { destruct (VF_dec_order xa ya) as [[Hlt|?]|Hgt]; [ exfalso | trivial | exfalso ].
    - eelim ord_lt_irreflexive. eapply ord_le_lt_trans; [ apply Heq |].
      apply schutte_matrix_lt2; intuition auto with ord.
      + eauto.
      + simpl.
        revert H8; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq.
    - eelim ord_lt_irreflexive. eapply ord_lt_le_trans; [| apply (ord_eq_sym _ _ Heq) ].
      apply schutte_matrix_lt2; intuition auto with ord.
      + eauto.
      + simpl.
        revert H9; apply schutte_matrix_proper_monotone; auto with ord.
        apply Heq. }

  apply pairwise_cons; simpl; intuition.
  apply IHxs with (schutte_column f (natOrdSize yb) (VF_denote xa)) (natOrdSize yb) (natOrdSize yb);
    intuition auto with ord.
  - rewrite Heq. split; apply schutte_matrix_monotone_func; auto with ord.
    + intros; apply schutte_column_monotone; auto with ord. apply Ha.
    + intros; apply schutte_column_monotone; auto with ord. apply Ha.
  - revert H9; apply schutte_matrix_proper_monotone; auto with ord.
    apply schutte_matrix_monotone_func; auto with ord.
    intros; apply schutte_column_monotone; auto with ord. apply Ha.
Qed.

Lemma sparse_stack_length_lt: forall x l xs,
  x :: l = sparse_stack xs -> (fst x < length xs)%nat.
Proof.
  intros x l xs; induction xs; simpl; intuition.
  - discriminate.
  - destruct a; simpl.
    apply IHxs in H. lia.
    inversion H. subst. simpl.
    lia.
Qed.

Definition no_leading_zeros (l:list VForm) :=
  match l with
  | [] => True
  | x::_ => x <> Z
  end.

Fixpoint VF_normal (x:VForm) :=
  match x with
  | Z => True
  | N l => no_leading_zeros l /\ each VF_normal l /\ each (fun x => VF_denote x < VF_denote (N l)) l
  end.

Lemma sparse_subterm_lt:
  forall xs l n x f,
    normal_function f ->
    sparse_stack xs = (l ++ [(n,x)]) ->
    each (fun z => VF_denote (snd z) < schutte_matrix f (sparse_matrix (l ++ [(n,x)])) 0) l.
Proof.
  induction xs as [|x xs IHxs].
  - simpl. destruct l; discriminate.
  - simpl; intros.
    destruct x as [|xl].
    + apply IHxs; auto.
    + destruct l as [|[b a] l]; simpl in H0; inversion H0; subst.
      * rewrite H4. simpl; auto.
      * simpl; split; auto.
        apply (nontrivial_matrix_member_lt [] (sparse_matrix (l ++ [(n, x0)])) f (natOrdSize (length xs))); simpl; auto with ord.
        assert (x0 <> Z).
        { assert (Hsp: is_sparse (sparse_stack xs)) by apply sparse_stack_is_sparse.
          rewrite H4 in Hsp.
          rewrite is_sparse_app in Hsp. simpl in *; intuition. }
        rewrite sparse_matrix_app.
        rewrite nontrivial_matrix_app.
        simpl.
        rewrite VF_nonzero.
        auto.
Qed.

Lemma each_lt_sparse_stack: forall xs p q,
    0 < q ->
    p <= q ->
    each (fun z => VF_denote (snd z) < p) (sparse_stack xs) ->
    each (fun z => VF_denote z < q) xs.
Proof.
  induction xs; simpl; intuition.
  - destruct a; simpl in *; intuition.
    rewrite  <- H0. auto.
  - destruct a; simpl in *; intuition eauto.
Qed.

Lemma active_subterm_lt:
  forall xs,
    (forall x, active_subterm xs x -> VF_denote x < VF_denote (N xs)) ->
    each (fun x => VF_denote x < VF_denote (N xs)) xs.
Proof.
  intros xs Hactive.
  case_eq (sparse_stack xs).
  - intros.
    rewrite <- all_zero_sparse_stack in H.
    clear Hactive.
    generalize xs at 1.
    induction xs; simpl in *; intuition subst; simpl; auto with ord.
  - intros.
    assert (Hnil: sparse_stack xs <> nil).
    { rewrite H. discriminate. }
    apply exists_last in Hnil.
    destruct Hnil as [l' [[n x] Heq]].
    assert (Hactive': active_subterm xs x).
    { rewrite active_subterm_sparse. eauto. }
    assert (each (fun z => VF_denote (snd z) < schutte_matrix (addOrd 1) (sparse_matrix (l' ++ [(n,x)])) 0) l').
    { apply sparse_subterm_lt with xs; auto with ord. }
    assert (each (fun z => VF_denote (snd z) < schutte_matrix (addOrd 1) (sparse_matrix (l' ++ [(n,x)])) 0) (sparse_stack xs)).
    rewrite Heq. rewrite each_app; split; auto.
    simpl; split; auto.

    apply Hactive in Hactive'.
    eapply ord_lt_le_trans; [ apply Hactive' |].
    simpl.
    rewrite <- Heq.
    apply sparse_matrix_eq; auto with ord.
    eapply each_lt_sparse_stack; try eassumption; simpl; auto with ord.
    rewrite <- Heq.
    apply sparse_matrix_eq; auto with ord.
Qed.

Lemma active_subterm_lt':
  forall xs q,
    each (fun x => VF_denote x < q) xs ->
    (forall x, active_subterm xs x -> VF_denote x < q).
Proof.
  induction xs; simpl; intuition.
  - inversion H0.
  - inversion H; subst; auto.
Qed.

Lemma VF_normal_alt: forall l,
  VF_normal (N l) <->
    no_leading_zeros l /\ each VF_normal l /\ (forall x, active_subterm l x -> VF_denote x < VF_denote (N l)).
Proof.
  simpl; intuition.
  - eapply active_subterm_lt'; eauto.
  - apply active_subterm_lt; auto.
Qed.

Inductive redex : VForm -> VForm -> Prop :=
| redex_leading_zero: forall l,
    redex (N (Z :: l)) (N l)

| redex_fixpoint: forall l x,
    active_subterm l x ->
    VF_compare (N l) x = EQ ->
    redex (N l) x.

Lemma redex_sound: forall x y,
    redex x y ->
    VF_denote x ≈ VF_denote y.
Proof.
  intros x y H.
  inversion H; subst.
  - simpl VF_denote.
    split; apply schutte_stack_monotone_func; auto with ord.
    + intros; rewrite schutte_column_arg0; auto with ord.
    + intros; rewrite schutte_column_arg0; auto with ord.
  - generalize (VF_compare_correct (N l) y).
    rewrite H1.
    auto.
Qed.

Lemma redex_size: forall x y,
    redex x y ->
    (VF_termSize x > VF_termSize y)%nat.
Proof.
  intros x y H.
  inversion H; subst.
  - simpl. lia.
  - clear H H1. simpl.
    induction H0; simpl; lia.
Qed.

Inductive one_step_reduce: VForm -> VForm -> Prop :=
| reduce_redex: forall x y, redex x y -> one_step_reduce x y
| reduce_cong: forall x x' l1 l2, one_step_reduce x x' -> one_step_reduce (N (l1 ++ [x] ++ l2)) (N (l1 ++ [x'] ++ l2)).

Lemma schutte_stack_le_cong:
  forall l1 l2 f x x',
    each complete l1 ->
    normal_function f ->
    x ≤ x' ->
    schutte_stack f (l1 ++ x :: l2) 0 ≤ schutte_stack f (l1 ++ x' :: l2) 0.
Proof.
  induction l1; simpl; intuition.
  - apply schutte_stack_monotone_func; auto with ord.
  - repeat rewrite length_app; simpl.
    apply IHl1; auto with ord.
Qed.

Lemma one_step_reduce_sound: forall x y, one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H.
  - apply redex_sound; auto.
  - simpl.
    repeat rewrite map_app; simpl.
    destruct IHone_step_reduce.
    split; apply schutte_stack_le_cong; auto with ord.
Qed.

Theorem step_reduce_sound: forall x y,
    clos_refl_trans _ one_step_reduce x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H; auto with ord.
  - apply one_step_reduce_sound; auto.
  - transitivity (VF_denote y); auto.
Qed.

Lemma VF_normal_matrix_proper_aux : forall l p q f,
    normal_function f ->
    p <= q ->
    each (fun x : VForm => VF_denote x < p) l ->
    schutte_matrix_proper (stack_to_matrix (map VF_denote l)) (natOrdSize (length l)) q.
Proof.
  induction l; simpl; intros p q f Hf Hpq H; intuition auto with ord.
  - rewrite length_map. auto with ord.
  - rewrite <- Hpq; auto.
  - rewrite length_map. eapply IHl; eauto.
Qed.

Lemma VF_normal_matrix_proper: forall l,
    VF_normal (N l) ->
    schutte_matrix_proper (stack_to_matrix (map VF_denote l))
      (natOrdSize (length l))
      (schutte_matrix (addOrd 1) (stack_to_matrix (map VF_denote l)) 0).
Proof.
  simpl; intuition.
  eapply VF_normal_matrix_proper_aux; eauto.
  rewrite stack_to_matrix_eq; auto with ord.
Qed.

Lemma VF_normal_sparse_matrix_proper_aux : forall l p q f,
    normal_function f ->
    p <= q ->
    each (fun x : VForm => VF_denote x < p) l ->
    schutte_matrix_proper (sparse_matrix (sparse_stack l)) (natOrdSize (length l)) q.
Proof.
  induction l; simpl; intros p q f Hf Hpq H; intuition auto with ord.
  destruct a; simpl; intuition.
  - eapply schutte_matrix_proper_monotone; [ | | apply IHl with p f]; auto with ord.
  - auto with ord.
  - rewrite <- Hpq; auto.
  - eapply IHl; eauto.
Qed.

Lemma VF_normal_sparse_matrix_proper: forall l,
    VF_normal (N l) ->
    schutte_matrix_proper (sparse_matrix (sparse_stack l))
      (natOrdSize (length l))
      (schutte_matrix (addOrd 1) (sparse_matrix (sparse_stack l)) 0).
Proof.
  simpl; intuition.
  apply VF_normal_sparse_matrix_proper_aux with
    (schutte_stack (addOrd 1) (map VF_denote l) 0) (addOrd 1); auto with ord.
  apply sparse_matrix_eq; auto with ord.
Qed.

Lemma sparse_stack_pairwise_eq: forall xs ys,
  length xs = length ys ->
  pairwise (fun x y => fst x = fst y /\ VF_denote (snd x) ≈ VF_denote (snd y)) (sparse_stack xs) (sparse_stack ys) ->
  pairwise (fun x y => VF_denote x ≈ VF_denote y) xs ys.
Proof.
  induction xs as [|x xs IHxs].
  { simpl in *; intuition.
    destruct ys; try discriminate.
    apply pairwise_nil. }
  destruct ys as [|y ys].
  { simpl in *; intuition; discriminate. }
  simpl; intuition.
  destruct x as [|xl]; simpl in *.
  { destruct y as [|yl]; simpl in *.
    - apply pairwise_cons; auto with ord.
    - inversion H0; subst; simpl in *; intuition.
      assert (fst x < length xs)%nat.
      { eapply sparse_stack_length_lt; eauto. }
      lia. }
  destruct y as [|yl]; simpl in *.
  { inversion H0; subst; simpl in *; intuition.
    assert (fst y < length ys)%nat.
    { eapply sparse_stack_length_lt; eauto. }
    lia. }
  inversion  H0; subst; simpl in *.
  apply pairwise_cons; intuition auto with ord.
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
  simpl; intros y [Hx1 [Hx2 Hx3]] Hy Heq.
  destruct y as [|yl]; simpl in *.
  { elim (ord_lt_irreflexive (VF_denote (N xl))).
    rewrite Heq at 1. simpl.
    auto with ord. }
  f_equal.
  destruct Hy as [Hy1 [Hy2 Hy3]].
  assert (length xl = length yl).
  { destruct xl as [|x xl]; destruct yl as [|y yl]; simpl in *; auto.
    - destruct  Heq as [Heq1 Heq2].
      rewrite <- schutte_stack_base in Heq2; auto with ord.
      elim (ord_lt_irreflexive (1 + 0)).
      rewrite <- Heq2 at 2.
      rewrite schutte_column_unroll. rewrite <- lub_le1.
      apply addOrd_increasing.
      rewrite addOrd_zero_r.
      rewrite VF_nonzero; auto.
    - destruct  Heq as [Heq1 Heq2].
      rewrite <- schutte_stack_base in Heq1; auto with ord.
      elim (ord_lt_irreflexive (1 + 0)).
      rewrite <- Heq1 at 2.
      rewrite schutte_column_unroll. rewrite <- lub_le1.
      apply addOrd_increasing.
      rewrite addOrd_zero_r.
      rewrite VF_nonzero; auto.
    - f_equal.
      repeat rewrite length_map in Heq.
      repeat rewrite stack_to_matrix_eq in Heq.
      destruct (Compare_dec.lt_eq_lt_dec (length xl) (length yl)) as [[Hlt|?]|Hgt]; auto.
      + eelim ord_lt_irreflexive; eapply ord_lt_le_trans; [ | apply Heq].
        apply schutte_matrix_lt1; auto with ord.
        * rewrite stack_to_matrix_complete; auto with ord.
        * rewrite stack_to_matrix_complete; auto with ord.
        * simpl.
          eapply schutte_matrix_proper_monotone; [ reflexivity | apply Heq |].
          generalize (VF_normal_matrix_proper (x::xl)); simpl.
          repeat rewrite length_map in *.
          intuition.
        * rewrite VF_nonzero; auto.
        * apply natOrdSize_increasing; auto.
        * simpl. rewrite <- Heq.
          repeat rewrite length_map in *.
          rewrite stack_to_matrix_eq in *.
          intuition.
      + eelim ord_lt_irreflexive; eapply ord_le_lt_trans; [ apply (ord_eq_sym _ _ Heq) |].
        apply schutte_matrix_lt1; auto with ord.
        * rewrite stack_to_matrix_complete; auto with ord.
        * rewrite stack_to_matrix_complete; auto with ord.
        * simpl.
          eapply schutte_matrix_proper_monotone; [ reflexivity | apply Heq |].
          generalize (VF_normal_matrix_proper (y::yl)); simpl.
          repeat rewrite length_map in *.
          intuition.
        * rewrite VF_nonzero; auto.
        * apply natOrdSize_increasing; auto.
        * simpl. rewrite Heq.
          repeat rewrite length_map in *.
          rewrite stack_to_matrix_eq in *.
          intuition. }

  cut (pairwise (fun x y => VF_denote x ≈ VF_denote y) xl yl).
  { clear -IHx Hx2 Hy2.
    revert yl Hy2.
    induction xl; intros; inversion H; subst; simpl in *; auto.
    f_equal.
    - apply IHx; intuition auto with ord.
    - apply IHxl; intuition. }

  apply sparse_stack_pairwise_eq; auto.
  apply sparse_stack_eq_unique with (addOrd 1) (natOrdSize (length xl)) (natOrdSize (length yl)); auto with ord.
  - rewrite sparse_matrix_eq in Heq; auto.
    rewrite sparse_matrix_eq in Heq; auto.
  - apply sparse_stack_is_sparse.
  - apply sparse_stack_is_sparse.
  - apply VF_normal_sparse_matrix_proper; simpl; intuition.
  - apply VF_normal_sparse_matrix_proper; simpl; intuition.
Qed.

Lemma no_leading_zeros_dec: forall xs,
  { exists l, xs = Z::l } + { no_leading_zeros xs }.
Proof.
  intros. destruct xs; simpl; auto.
  destruct v; [ eauto | right; discriminate ].
Defined.

Lemma active_subterm_dec: forall xs,
    { x | active_subterm xs x } + { each (fun x => x = Z) xs }.
Proof.
  induction xs; simpl; intuition.
  - left.
    destruct a0 as [x H].
    exists x.
    apply active_later; auto.
  - destruct a; auto.
    left. exists (N l).
    apply active_last; auto.
    discriminate.
Defined.

Theorem VF_normal_dec: forall x, { VF_normal x } + { ~VF_normal x }.
Proof.
  induction x; [ simpl; auto |].
  destruct (no_leading_zeros_dec l).
  { right. intros [? [??]].
    destruct e as [l' ?]; subst. simpl in *. auto. }
  destruct (active_subterm_dec l).
  - destruct s as [x Hx].
    destruct (VF_dec_order (N l) x).
    + right. rewrite VF_normal_alt.
      intuition.
      * elim (ord_lt_irreflexive (VF_denote x)).
        etransitivity; [ | apply a ].
        apply H3; auto.
      * elim (ord_lt_irreflexive (VF_denote x)).
        eapply ord_lt_le_trans; [ | apply b ].
        apply H3; auto.
    + assert (Heach: { each VF_normal l } + { ~each VF_normal l }).
      { clear - H. induction l; simpl in *; intuition.
        inversion H; subst.
        destruct (IHl H3); intuition. }
      destruct Heach.
      * left. rewrite VF_normal_alt; intuition.
        replace x0 with x; auto.
        eapply active_subterm_unique; eauto.
      * right. rewrite VF_normal_alt; intuition.
  - destruct l.
    + left; simpl; intuition.
    + simpl in *; intuition.
Defined.

Lemma active_subterm_le:
  forall xs x,
    active_subterm xs x ->
    forall f,
      normal_function f ->
      VF_denote x <= schutte_stack f (map VF_denote xs) 0.
Proof.
  intros xs x H; induction H; simpl; intros.
  - rewrite <- schutte_stack_base; auto with ord.
    apply normal_inflationary with (f:= fun x => schutte_column _ _ x 0); auto with ord.
  - apply IHactive_subterm; auto with ord.
Qed.

Theorem VF_notIsNormal_redex: forall x, ~VF_normal x <-> exists y, one_step_reduce x y.
Proof.
  induction x using VForm_induction.
  - simpl. intuition. destruct H as [z H]. inversion H; subst. inversion H1.
  - rewrite VF_normal_alt; split.
    + intro H1.
      destruct (no_leading_zeros_dec xs) .
      { destruct e. subst.
        exists (N x).
        apply reduce_redex.
        apply redex_leading_zero. }
      intuition.
      cut (~each VF_normal xs -> exists y : VForm, one_step_reduce (N xs) y).
      { intro Hfinish.
        destruct (active_subterm_dec xs).
        * destruct s as [x Hx].
          destruct (VF_dec_order (N xs) x).
          ** exists x.

             apply reduce_redex.
             apply redex_fixpoint; auto with ord.
             generalize (VF_compare_correct (N xs) x).
             destruct (VF_compare (N xs) x); simpl in *; auto.
             *** intro Hlt.
                 elim (ord_lt_irreflexive (VF_denote x)).
                 eapply ord_le_lt_trans; [ | apply Hlt ].
                 apply active_subterm_le; auto.
             *** intro Hlt.
                 elim (ord_lt_irreflexive (VF_denote x)).
                 eapply ord_lt_le_trans; [ apply Hlt | ].
                 intuition auto with ord. apply b.
          ** apply Hfinish. intro.
             apply H0; auto.
             intros. replace x0 with x; auto.
             eapply active_subterm_unique; eauto.
        * apply Hfinish.
          intro. apply H0; auto.
          intros.
          elim (active_subterm_all_zeros xs x); auto.
      }

      intro Hnnorm.
      assert (exists l1, exists l2, exists x, exists x',
                 xs = l1 ++ x :: l2 /\
                   one_step_reduce x x').
      { clear - H Hnnorm.
        induction xs; simpl in *; intuition.
        destruct (VF_normal_dec a).
        - destruct H0 as [l1 [l2 [x [x' [??]]]]]; auto.
          exists (a::l1), l2, x, x'. simpl; subst; intuition.
        - destruct H as [x' ?]; auto.
          exists [], xs, a, x'; simpl; intuition. }
      destruct H1 as [l1 [l2 [x [x' [??]]]]]. subst.
      exists (N (l1 ++ x' :: l2)).
      apply reduce_cong; auto.

    + intros [y Hy] [H1 [H2 H3]].
      inversion Hy; subst.
      * inversion H0; subst; simpl in *; auto.
        generalize (VF_compare_correct (N xs) y).
        rewrite H6. simpl; intros.
        elim (ord_lt_irreflexive (VF_denote y)).
        rewrite <- H4 at 2.
        apply H3; auto.
      * repeat rewrite each_app in *; simpl in *; intuition eauto.
Qed.

Lemma VF_normal_no_redex: forall x, VF_normal x <-> ~exists y, one_step_reduce x y.
Proof.
  intros x.
  generalize (VF_notIsNormal_redex x).
  destruct (VF_normal_dec x); intuition.
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

Lemma one_step_reduce_size: forall x y,
    one_step_reduce x y ->
    (VF_termSize x > VF_termSize y)%nat.
Proof.
  intros x y H. induction H.
  - apply redex_size; auto.
  - unfold VF_termSize; fold VF_termSize.
    induction l1; simpl in *; intuition; try lia.
Qed.

Theorem normalizes_eq: forall x y, normalizes x y -> VF_denote x ≈ VF_denote y.
Proof.
  intros x y H. induction H; auto with ord.
  transitivity (VF_denote y); auto with ord.
  apply one_step_reduce_sound; auto.
Qed.

Theorem normalizes_normal: forall x y, normalizes x y -> VF_normal y.
Proof.
  intros x y H. induction H; auto with ord.
  rewrite VF_normal_no_redex; auto.
Qed.

Theorem strongly_normalizing: forall x, exists! y, normalizes x y.
Proof.
  induction x as [x Hind] using (well_founded_induction (Wf_nat.well_founded_ltof _ VF_termSize)).
  destruct (VF_normal_dec x).
  - eexists.
    split.
    apply normal_normalizing; auto.
    + apply VF_normal_no_redex; auto.
    + intros x' Hx.
      inversion Hx; subst; auto.
      apply VF_normal_no_redex in v.
      elim v. eauto.

  - assert (exists y, one_step_reduce x y).
    { rewrite <- VF_notIsNormal_redex. auto. }
    destruct H as [y Hy].
    destruct (Hind y) as [z [Hz1 Hz2]]; auto.
    { red. apply one_step_reduce_size; auto. }
    exists z.
    split.
    + apply step_normalizing with y; auto.
    + intros q Hq.
      apply VF_normal_form_unique; auto.
      eapply normalizes_normal; eauto.
      eapply normalizes_normal; eauto.
      transitivity (VF_denote x).
      * symmetry. transitivity (VF_denote y).
        ** apply one_step_reduce_sound; auto.
        ** apply normalizes_eq; auto.
      * apply normalizes_eq; auto.
Qed.

Fixpoint delete_leading_zeros xs :=
  match xs with
  | [] => []
  | Z::xs => delete_leading_zeros xs
  | xs => xs
  end.

Lemma delete_leading_zeros_correct: forall xs,
    VF_denote (N (delete_leading_zeros xs)) ≈ VF_denote (N xs) /\
      no_leading_zeros (delete_leading_zeros xs).
Proof.
  induction xs; simpl; intuition auto with ord.
  - destruct a; auto with ord.
    rewrite H. symmetry; apply schutte_stack_leading_zero; auto with ord.
  - destruct a; simpl; auto with ord.
    discriminate.
Qed.

Fixpoint find_active_subterm (r:option VForm) (xs: list VForm) : option VForm :=
  match xs with
  | [] => r
  | Z::xs => find_active_subterm r xs
  | x::xs => find_active_subterm (Some x) xs
  end.

Definition is_active_subterm (r: option VForm) (xs: list VForm) :=
  match r with
  | None => each (fun x => x = Z) xs
  | Some x => active_subterm xs x
  end.

Lemma active_subterm_app: forall xs ys x,
  active_subterm ys x ->
  active_subterm (xs++ys) x.
Proof.
  induction xs; simpl; intros; auto.
  apply active_later; auto.
Qed.

Lemma active_subterm_last_Z: forall xs x,
    active_subterm xs x ->
    active_subterm (xs ++ [Z]) x.
Proof.
  intros xs x H. induction H; simpl.
  - apply active_last; auto.
    rewrite each_app; simpl; intuition.
  - apply active_later; auto.
Qed.

Lemma active_subterm_last_N: forall xs l,
    active_subterm (xs ++ [N l]) (N l).
Proof.
  induction xs; simpl; intros.
  - apply active_last; simpl; auto. discriminate.
  - apply active_later; auto.
Qed.

Lemma find_active_subterm_correct_aux: forall ys xs r,
    is_active_subterm r xs ->
    is_active_subterm (find_active_subterm r ys) (xs++ys).
Proof.
  induction ys; simpl; intuition.
  - rewrite app_nil_r; auto.
  - destruct a; simpl; auto with ord.
    + replace (xs ++ Z :: ys) with ((xs ++ [Z]) ++ ys) by (rewrite <- app_assoc; simpl; auto).
      apply IHys.
      destruct r; simpl in *; auto.
      * apply active_subterm_last_Z; auto.
      * rewrite each_app; simpl; auto.
    + replace (xs ++ N l :: ys) with ((xs ++ [N l]) ++ ys) by (rewrite <- app_assoc; simpl; auto).
      apply IHys. simpl.
      apply active_subterm_last_N.
Qed.

Lemma find_active_subterm_correct: forall xs,
    is_active_subterm (find_active_subterm None xs) xs.
Proof.
  intros.
  apply (find_active_subterm_correct_aux xs [] None); simpl; auto.
Qed.

Definition Nnorm (l:list VForm) : VForm :=
    let l' := delete_leading_zeros l in
    match find_active_subterm None l' with
    | None => N l'
    | Some x =>
        match VF_compare x (N l') with
        | LT => N l'
        | _ => x
        end
    end.

Lemma Nnorm_eq: forall l,
    VF_denote (Nnorm l) ≈ VF_denote (N l).
Proof.
  intros; unfold Nnorm.
  generalize (find_active_subterm_correct (delete_leading_zeros l)).
  case_eq (find_active_subterm None (delete_leading_zeros l)); intros.
  - simpl in *.
    generalize (VF_compare_correct v (N (delete_leading_zeros l))).
    destruct (VF_compare v (N (delete_leading_zeros l))); auto.
    + simpl; intros.
      apply delete_leading_zeros_correct.
    + simpl; intros; auto.
      rewrite H1.
      apply delete_leading_zeros_correct.
    + simpl; intros.
      elim (ord_lt_irreflexive (VF_denote v)).
      eapply ord_le_lt_trans; [ | apply H1].
      apply active_subterm_le; auto with ord.
  - simpl. apply delete_leading_zeros_correct.
Qed.

Lemma Nnorm_normal: forall l,
    each VF_normal l ->
    VF_normal (Nnorm l).
Proof.
  unfold Nnorm; simpl; intros.
  generalize (find_active_subterm_correct (delete_leading_zeros l)).
  case_eq (find_active_subterm None (delete_leading_zeros l)); intros.
  - assert (VF_normal v).
    { simpl in H1. clear H0.
      induction l; simpl in *; intuition.
      inversion H1.
      destruct a; auto.
      inversion H1; subst; auto.
      clear -H2 H6.
      induction H6; simpl in *; intuition. }
    generalize (VF_compare_correct v (N (delete_leading_zeros l))).
    destruct (VF_compare v (N (delete_leading_zeros l))); auto.
    rewrite VF_normal_alt; simpl; intuition.
    + apply delete_leading_zeros_correct.
    + clear -H. induction l; simpl in *; intuition.
      destruct a; simpl; auto.
    + simpl in *.
      replace x with v; auto.
      eapply active_subterm_unique; eauto.
  - rewrite VF_normal_alt; simpl; intuition.
    + apply delete_leading_zeros_correct.
    + clear -H. induction l; simpl in *; intuition.
      destruct a; simpl; auto.
    + simpl in *.
      elim (active_subterm_all_zeros (delete_leading_zeros l) x); auto.
Qed.

Fixpoint VF_normalize (x:VForm) : VForm :=
  match x with
  | Z => Z
  | N l => Nnorm (map VF_normalize l)
  end.

Lemma VF_normalize_normal: forall x, VF_normal (VF_normalize x).
Proof.
  induction x using VForm_induction; simpl; auto.
  apply Nnorm_normal; auto.
  rewrite each_map; auto.
Qed.

Lemma VF_normalize_eq: forall x, VF_denote (VF_normalize x) ≈ VF_denote x.
Proof.
  induction x using VForm_induction; simpl; auto with ord.
  rewrite Nnorm_eq. simpl.
  assert (Hf: forall f, normal_function f ->
            schutte_stack f (map VF_denote (map VF_normalize xs)) 0
              ≈ schutte_stack f (map VF_denote xs) 0).
  { induction xs; simpl in *; intuition auto with ord.
    rewrite H; auto with ord.
    repeat rewrite length_map.
    split; apply schutte_stack_monotone_func; auto with ord.
    - intros. apply schutte_column_monotone; auto with ord. apply H0.
    - intros. apply schutte_column_monotone; auto with ord. apply H0. }
  apply Hf; auto.
Qed.


Lemma schutte_stack_epsilon:  forall l,
  no_leading_zeros l ->
  (length l > 2)%nat ->
  expOrd ω (VF_denote (N l)) <= VF_denote (N l).
Proof.
  simpl; intros.
  rewrite sparse_matrix_eq at 1; auto with ord.
  rewrite sparse_matrix_eq at 1; auto with ord.
  destruct l; simpl in *; [ simpl in *; lia |].
  destruct v; [ elim H; auto |]. simpl in *.
  apply schutte_matrix_fixpoint1; auto with ord.
  intros.
  rewrite <- (schutte_column_fixpoint (natOrdSize (length l)) _ z (addOrd 1) 1 0) at 2; auto with ord.
  - rewrite schutte_column_veblen; auto with ord.
    transitivity (veblen (addOrd 1)
      (schutte_column (addOrd 1) (natOrdSize (length l))
         (schutte_stack (addOrd 1) (map VF_denote l0) 0) z)
      0).
    + rewrite veblen_onePlus; auto with ord.
    + apply veblen_monotone_func; auto with ord.
      intros. rewrite schutte_column_arg0; auto with ord.
  - apply (natOrdSize_increasing 1 (length l)). lia.
Qed.

Fixpoint VF_decompose (x:VForm) : list VForm :=
  match x with
  | Z => []
  | N [] => [Z]
  | N [x] => Z :: VF_decompose x
  | N [x;y] => x :: VF_decompose y
  | N l => [N l]
  end.

Fixpoint VF_recompose (xs:list VForm) : VForm :=
  match xs with
  | [] => Z
  | [x] =>
      match x with
      | Z => N []
      | N [] => N [x; Z]
      | N [_] => N [x; Z]
      | N [_; _] => N [x; Z]
      | _ => x
      end
  | Z::xs' => N [VF_recompose xs']
  | x::xs' => N [x; VF_recompose xs']
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
  - induction xs; simpl; intuition.
    + rewrite expOrd_zero; auto with ord.
    + destruct xs; simpl in *; intuition.
      * destruct xs; simpl in *; intuition.
    + destruct xs; simpl in *; intuition.
      * case_eq (VF_decompose a); auto.
        simpl; intros.
        rewrite H7 in H8.
        rewrite H7 in H.
        simpl in *.
        rewrite H8 in H0 at 1.
        rewrite schutte_column0 in H0.
        rewrite H8 in H0.
        destruct v; [ simpl; auto with ord |].
        elim (ord_lt_irreflexive (expOrd ω (VF_denote (N l0)) + cantor_denote VF_denote l)).
        eapply ord_lt_le_trans; [ apply H0 |].
        rewrite addOrd_zero_r.
        rewrite addOrd_assoc; apply addOrd_monotone; auto with ord.
        apply additively_closed_collapse; auto with ord.
        apply expOmega_additively_closed; auto.
        apply ord_le_lt_trans with (expOrd ω 0); auto with ord.
        apply expOrd_increasing; simpl; auto with ord.
      * destruct xs; simpl in *; intuition.
        rewrite schutte_column0 in H4.
        rewrite schutte_column_veblen in H4; auto with ord.
        rewrite veblen_onePlus in H4; auto with ord.
        rewrite addOrd_zero_r in H4.
        case_eq (VF_decompose v); intros; auto.
        rewrite H12 in H13.
        rewrite H12 in H10.
        simpl in *; intuition.
        rewrite H13 in H4.
        destruct (VF_dec_order v0 a) as [[Hlt|Heq]|Hgt]; [ auto with ord | apply Heq |].
        eelim ord_lt_irreflexive; eapply ord_lt_le_trans; [ apply H4 |].
        rewrite addOrd_assoc.
        apply addOrd_monotone; auto with ord.
        apply additively_closed_collapse; auto with ord.
        apply expOmega_additively_closed; auto.
        apply expOrd_increasing; auto with ord.
    + destruct xs; simpl.
      * rewrite schutte_column0.
        rewrite expOrd_zero.
        apply addOrd_eq_mor; auto with ord.
        rewrite addOrd_zero_r. simpl in *; intuition.
      * destruct xs; simpl.
        ** rewrite schutte_column0.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           apply addOrd_eq_mor; auto with ord.
           rewrite addOrd_zero_r.
           simpl in *; intuition auto with ord.
        ** rewrite addOrd_zero_r.
           split. { simpl in *; intuition auto 50 with ord. }
           apply (schutte_stack_epsilon (a::v::v0::xs)); simpl; auto.
           lia.
Qed.

Lemma expOmega_denote: forall x,
    expOrd ω (VF_denote x) ≈ VF_denote (N [x; Z]).
Proof.
  simpl; intros.
  rewrite schutte_column0.
  rewrite schutte_column_veblen; auto with ord.
  rewrite veblen_onePlus; auto with ord.
  repeat rewrite addOrd_zero_r.
  auto with ord.
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
      destruct l; simpl; intuition auto with ord; try discriminate.
      * rewrite schutte_column0.
        rewrite schutte_column_veblen; auto with ord.
        rewrite veblen_onePlus; auto with ord.
        repeat rewrite addOrd_zero_r.
        rewrite expOrd_one; auto with ord.
        rewrite <- lub_le2.
        auto with ord.
      * simpl in *; intuition.
        destruct l; simpl; intuition auto with ord; try discriminate.
        ** rewrite schutte_column0 at 1.
           rewrite schutte_column0 at 1.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           rewrite schutte_column0.
           repeat rewrite addOrd_zero_r.
           simpl in *.
           rewrite schutte_column0 in H1.
           rewrite addOrd_zero_r in H1.
           apply ord_le_lt_trans with (expOrd ω (VF_denote v)).
           2: { apply expOrd_increasing; auto with ord. }
           transitivity (1 + expOrd ω (VF_denote v)).
           { apply addOrd_monotone; auto with ord. }
           apply additively_closed_collapse; auto with ord.
           apply expOmega_additively_closed; auto.
           apply ord_le_lt_trans with (expOrd ω 0); auto with ord.
           apply expOrd_increasing; auto with ord.
           rewrite VF_nonzero; auto.
        ** auto 50 with ord.
        ** destruct l; simpl in *; intuition auto 50 with ord; try discriminate.
           rewrite schutte_column0 at 1.
           rewrite schutte_column0 at 1.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           repeat rewrite addOrd_zero_r.
           rewrite schutte_column0 at 1.
           rewrite schutte_column_veblen; auto with ord.
           rewrite veblen_onePlus; auto with ord.
           rewrite addOrd_zero_r.
           rewrite schutte_column0 in H8.
           rewrite schutte_column_veblen in H8; auto with ord.
           rewrite veblen_onePlus in H8; auto with ord.
           rewrite schutte_column0 in H1.
           rewrite schutte_column_veblen in H1; auto with ord.
           rewrite veblen_onePlus in H1; auto with ord.
           repeat rewrite addOrd_zero_r in *.
           apply expOmega_additively_closed; auto with ord.
           apply expOrd_increasing; auto with ord.
           rewrite <- normal_inflationary; auto with ord.

    + simpl in *; intuition; subst; simpl in *.
      destruct a; simpl in *; intuition.
      * repeat rewrite addOrd_zero_r.
        rewrite expOrd_zero. auto with ord.
      * rewrite addOrd_zero_r.
        generalize (expOmega_denote (N l)).
        destruct l; [ simpl; auto |].
        destruct l; [ simpl; auto |].
        destruct l; [ simpl; auto |].
        intros _.
        split; auto with ord.
        simpl in H4.
        apply (schutte_stack_epsilon (v::v0::v1::l)); simpl; auto.
        lia.
  }

  simpl.
  destruct a.

  (* a = Z case *)
  { simpl in *; intuition.
    - destruct v; try discriminate.
      destruct xs; try discriminate.
      destruct xs; try discriminate.
      destruct l; try discriminate.
      destruct l; try discriminate.
      destruct l; try discriminate.
    - destruct v; simpl in *.
      + rewrite schutte_column0.
        rewrite <- H7.
        rewrite expOrd_zero.
        apply addOrd_increasing.
        clear H3 H7 H4.
        induction xs; simpl in *; intuition auto with ord.
        rewrite H2 at 1.
        rewrite expOrd_zero.
        rewrite addOrd_zero_r.
        apply addOrd_increasing.
        eapply ord_lt_le_trans; [ apply IHxs |]; auto.
        destruct xs; auto with ord.
        rewrite H3. auto.
        rewrite addOrd_zero_r.
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
  simpl in *; intuition; try discriminate.
  - rewrite schutte_column0.
    rewrite schutte_column_veblen; auto 50 with ord.
    rewrite veblen_onePlus; auto 50 with ord.
    rewrite <- H9.
    apply ord_le_lt_trans with (expOrd ω (schutte_stack (addOrd 1) (map VF_denote l) 0) + 0).
    { rewrite addOrd_zero_r. auto with ord. }
    apply addOrd_increasing.
    rewrite addOrd_zero_r. auto with ord.
  - rewrite schutte_column0.
    rewrite schutte_column_veblen; auto 50 with ord.
    rewrite veblen_onePlus; auto 50 with ord.
    rewrite <- H9.
    rewrite H at 1.
    apply  addOrd_increasing; auto with ord.
    rewrite addOrd_zero_r.
    clear - H2 H6.
    revert v H2.
    induction xs; simpl in *; intuition auto with ord.
    rewrite H2 at 1.
    apply addOrd_increasing; auto with ord.
  - rewrite schutte_column0.
    rewrite schutte_column_veblen; auto 50 with ord.
    rewrite veblen_onePlus; auto 50 with ord.
    rewrite <- H9.
    rewrite addOrd_zero_r.
    auto with ord.
Qed.

Definition VF_has_cantor_decomposition : has_cantor_decomposition VF_denote VF_normal :=
  Build_has_cantor_decomposition
    VF_denote
    VF_normal
    VF_compare
    VF_decompose
    VF_recompose
    VForm_complete
    (fun x y Hx Hy => VF_compare_correct x y)
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
Definition VF_two := N [N []].

Definition VF_powOmega x := Nnorm [x; Z].
Definition VF_omega := VF_powOmega VF_one.
Definition VF_epsilon x := Nnorm [VF_one; Z; x].
Definition VF_gamma x := Nnorm [VF_two; Z; x].
Definition VF_ackermann a x := Nnorm [a; Z; x].

Definition VF_SAO := N [VF_omega; Z; Z].
Definition VF_LAO := N [VF_one; Z; Z; Z].

Theorem VF_powOmega_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD) powOmega VF_powOmega.
Proof.
  unfold VF_powOmega.
  hnf; simpl; intuition.
  - rewrite Nnorm_eq; simpl.
    rewrite schutte_column0.
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    repeat rewrite addOrd_zero_r.
    split; apply expOrd_monotone; apply H0.
  - apply Nnorm_normal; simpl; auto.
Qed.

Theorem VF_omega_reflects: reflects VForm VF_denote VF_normal ORD ω VF_omega.
Proof.
  hnf; simpl; intuition; try discriminate.
  - rewrite schutte_column0.
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    repeat rewrite addOrd_zero_r.
    rewrite expOrd_one'; auto with ord.
  - rewrite schutte_column0.
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_onePlus; auto with ord.
    repeat rewrite addOrd_zero_r.
    rewrite expOrd_one'; auto with ord.
  - auto with ord.
Qed.

Theorem VF_epsilon_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD) ε VF_epsilon.
Proof.
  unfold VF_epsilon.
  hnf; simpl; intuition.
  - rewrite Nnorm_eq; simpl.
    rewrite schutte_column0.
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_zero.
    transitivity (schutte_column (addOrd 1) 2 1 (VF_denote a)).
    2: { split; apply schutte_column_monotone; try rewrite addOrd_zero_r; auto with ord. }
    transitivity (ε (VF_denote a)).
    { unfold ε. split; apply enum_fixpoints_monotone; auto with ord; apply H0. }
    symmetry. apply schutte_column_2_1; auto with ord.
  - apply Nnorm_normal; simpl; auto.
Qed.

Theorem VF_gamma_reflects: reflects VForm VF_denote VF_normal (ORD ==> ORD) Γ VF_gamma.
Proof.
  unfold VF_gamma.
  hnf; simpl; intuition.
  - rewrite Nnorm_eq; simpl.
    rewrite schutte_column0.
    rewrite schutte_column_veblen; auto with ord.
    rewrite veblen_zero.
    transitivity (schutte_column (addOrd 1) 2 2 (VF_denote a)).
    2: { split; apply schutte_column_monotone; try rewrite addOrd_zero_r; auto with ord.
         - rewrite schutte_column0. repeat rewrite addOrd_zero_r.
           rewrite addOrd_succ. rewrite addOrd_zero_r. auto with ord.
         - rewrite schutte_column0. repeat rewrite addOrd_zero_r.
           rewrite addOrd_succ. rewrite addOrd_zero_r. auto with ord. }
    transitivity (Γ (VF_denote a)).
    { unfold Γ. split; apply enum_fixpoints_monotone; auto with ord; apply H0. }
    symmetry. apply schutte_column_2_2; auto with ord.
  - apply Nnorm_normal; simpl; intuition; try discriminate.
    rewrite schutte_column0.
    repeat rewrite addOrd_zero_r.
    rewrite addOrd_succ; auto with ord.
Qed.

Theorem VF_ackermann_tower_reflects:
  reflects VForm VF_denote VF_normal (ORD ==> ORD ==> ORD) (ackermann_tower (addOrd 1)) VF_ackermann.
Proof.
  unfold VF_ackermann.
  hnf; simpl; intuition.
  - rewrite Nnorm_eq; simpl.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    rewrite schutte_column_2_ackermann_tower; auto with ord.
    split; apply ackermann_tower_monotone; auto with ord;
      try rewrite addOrd_zero_r;
      try apply H0;
      try apply H2.
  - apply Nnorm_normal; simpl; auto.
Qed.

Theorem VF_SmallAckermannOrdinal:
  reflects VForm VF_denote VF_normal ORD SmallAckermannOrdinal VF_SAO.
Proof.
  unfold VF_SAO.
  hnf; intros.
  split.
  - rewrite SmallAckermannOrdinal_alt.
    simpl.
    rewrite schutte_column0.
    rewrite schutte_column_arg0; auto with ord.
    rewrite schutte_column_2_ackermann_tower; auto with ord.
    split; apply ackermann_tower_monotone; auto with ord.
    + apply VF_omega_reflects.
    + apply VF_omega_reflects.
    + rewrite addOrd_zero_r. auto with ord.
  - assert (exists H, VF_normal_dec VF_SAO = left H).
    { eexists. reflexivity. }
    destruct H; auto.
Qed.

Lemma VF_LAO_eq:
  VF_denote VF_LAO ≈ schutte_column (addOrd 1) 3 1 0.
Proof.
  simpl.
  rewrite schutte_column0.
  rewrite schutte_column_arg0; auto with ord.
  rewrite schutte_column_arg0; auto with ord.
  split; apply schutte_column_monotone; auto with ord; rewrite addOrd_zero_r; reflexivity.
Qed.

Theorem VF_LargeAckermannOrdinal:
  reflects VForm VF_denote VF_normal ORD LargeAckermannOrdinal VF_LAO.
Proof.
  hnf; intros.
  split.
  - rewrite VF_LAO_eq.
    split.
    + apply normal_fix_least; auto 50 with ord.
      rewrite <- (schutte_column_fixpoint 3 1 0 _ 2 0) at 2; auto with ord.
      rewrite schutte_column_2_ackermann_tower; auto 50 with ord.
      apply ackermann_tower_monotone_func; auto 50 with ord.
      intros. rewrite schutte_column_arg0; auto with ord.
    + rewrite schutte_column_gt0; auto with ord.
      apply sup_least; intros [].
      apply sup_least; intros [].
      simpl.
      apply normal_fix_least; auto 50 with ord.
      * unfold LargeAckermannOrdinal.
        apply normal_fix_complete; auto with ord.
        intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
      * apply limit_least; intros [].
      * unfold LargeAckermannOrdinal.
        rewrite normal_fixpoint at 2; auto with ord.
        rewrite schutte_column_2_ackermann_tower; auto with ord.
        apply ackermann_tower_monotone_func; auto with ord.
        ** apply normal_fix_complete; auto with ord.
           intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
        ** intros. rewrite schutte_column_arg0; auto with ord.
        ** apply normal_fix_complete; auto with ord.
           intros. apply normal_inflationary with (f:=fun x => ackermann_tower _ x 0); auto with ord.
  - assert (exists H, VF_normal_dec VF_LAO = left H).
    { eexists. reflexivity. }
    destruct H; auto.
Qed.
