Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import Program.Wf.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.

Require Import List.
Import ListNotations.
Open Scope list.

Section VeblenSymbol.
  Variable Idx : Type.
  Variable idx_lt : Idx -> Idx -> Prop.
  Variable idx_zero : Idx.
  Variable idx_succ : Idx -> Idx.

  Hypothesis idx_lt_trans: forall x y z, idx_lt x y -> idx_lt y z -> idx_lt x z.
  Hypothesis idx_lt_wf : well_founded idx_lt.
  Hypothesis idx_succ_lt : forall x, idx_lt x (idx_succ x).

  Definition idx_le i j := forall x, idx_lt x i -> idx_lt x j.

  Fixpoint well_formed_tail i (ls:list (Idx * Ord)) : Prop :=
    match ls with
    | [] => True
    | ((j,x) :: ls') => idx_lt i j /\ well_formed_tail j ls'
    end.

  Definition well_formed_symbol (ls:list (Idx * Ord)) : Prop :=
    match ls with
    | [] => True
    | ((i,x) :: ls') => well_formed_tail i ls'
    end.

  Lemma well_formed_tail_symbol i ls : well_formed_tail i ls -> well_formed_symbol ls.
  Proof.
    destruct ls; simpl in *; intuition.
    destruct p. intuition.
  Qed.

  Fixpoint indices_bounded (ls:list (Idx * Ord)) (i:Idx) : Prop :=
    match ls with
    | [] => True
    | ((j,x) :: ls') => idx_lt j i /\ indices_bounded ls' i
    end.

  Lemma well_formed_symbols_bounded : forall ls, well_formed_symbol ls -> exists i, indices_bounded ls i.
  Proof.
    intros ls. destruct ls.
    - exists idx_zero. simpl. auto.
    - destruct p as [j x].
      simpl.
      clear x.
      revert j.
      induction ls.
      + simpl; intros.
        exists (idx_succ j). split; auto.
      + intros.
        destruct a as [k y].
        simpl in *.
        destruct H as [Hk H].
        destruct (IHls k H) as [i [??]].
        exists i; intuition.
        apply idx_lt_trans with k; auto.
  Qed.

  Lemma is_well_formed_tail a xs : well_formed_symbol (a::xs) -> well_formed_symbol xs.
  Proof.
    destruct a. simpl. destruct xs; intuition.
    apply well_formed_tail_symbol with i; auto.
  Qed.

  Lemma is_well_formed_cons j y i x x' ls :
    idx_lt j i ->
    well_formed_symbol ((i,x)::ls) ->
    well_formed_symbol ((j,y)::(i,x')::ls).
  Proof.
    simpl; intros. split; auto.
  Qed.

  Lemma is_well_formed_prefix : forall xs ys, well_formed_symbol (xs ++ ys) -> well_formed_symbol xs.
  Proof.
    destruct xs; simpl; auto.
    destruct p as [i _].
    revert i; induction xs; simpl; intuition; eauto.
  Qed.

  Lemma well_formed_tail_bounded : forall xs i j o ys,
      well_formed_tail i (xs ++ (j,o) :: ys) -> idx_lt i j /\ indices_bounded xs j.
  Proof.
    induction xs; simpl.
    - intuition.
    - destruct a as [k _]. simpl; intros i j o ys [H1 H2].
      apply IHxs in H2.
      intuition.
      apply idx_lt_trans with k; auto.
  Qed.

  Lemma well_formed_bounded : forall xs j o ys,
      well_formed_symbol (xs ++ (j,o) :: ys) -> indices_bounded xs j.
  Proof.
    destruct xs; simpl.
    - intuition.
    - destruct p as [k _].
      apply well_formed_tail_bounded.
  Qed.

  Definition VeblenSymbol := { ls:list (Idx*Ord) | well_formed_symbol ls }.

  Inductive symbol_lt : list (Idx*Ord) -> list (Idx*Ord) -> Prop :=
  | symbol_lt_drop : forall i x ls, symbol_lt ls ((i,x)::ls)
  | symbol_lt_ord  : forall i x x' ls ys,
      x' < x ->
      indices_bounded ys i ->
      symbol_lt (ys ++ ((i,x')::ls)) ((i,x)::ls).

  Definition VeblenSymbol_lt (xs ys : VeblenSymbol) : Prop :=
    symbol_lt (proj1_sig xs) (proj1_sig ys).

  Lemma symbol_lt_append_Acc : forall a,
    Acc symbol_lt a ->
    forall b, Acc symbol_lt b ->
    Acc symbol_lt (a ++ b).
  Proof.
    intros a Ha. induction Ha.
    intros b Hb.
    destruct x as [|[j o] x].
    - simpl; auto.
    - simpl.
      constructor. simpl; intros.
      inversion H1; subst.
      + apply H0; auto.
        apply symbol_lt_drop.
      + cut (Acc symbol_lt ((ys ++ ((j,x') :: x)) ++ b)).
        { rewrite <- app_assoc. auto. }
        apply H0; auto.
        apply symbol_lt_ord; auto.
  Qed.

  Theorem symbol_lt_bounded_Acc : forall i xs, indices_bounded xs i -> Acc symbol_lt xs.
  Proof.
    induction i as [i Hind_i] using (well_founded_induction idx_lt_wf).
    induction xs; intros.
    - constructor. intros ys Hys.
      inversion Hys.
    - destruct a as [j x]. simpl in *. destruct H.
      induction x as [x Hind_x] using ordinal_induction.
      constructor. intros ys. intro Hys.
      inversion Hys; subst.
      + apply IHxs; auto.
      + apply symbol_lt_append_Acc.
        * apply (Hind_i j); auto.
        * apply Hind_x; auto.
  Qed.

  Theorem symbol_lt_well_formed_Acc : forall xs, well_formed_symbol xs -> Acc symbol_lt xs.
  Proof.
    intros.
    destruct (well_formed_symbols_bounded xs H) as [i Hi].
    apply (symbol_lt_bounded_Acc i xs Hi).
  Qed.

  Section MultiVeblen.
    Variable f : Ord -> Ord.

    Lemma step_down i (j:{ j:Idx | idx_lt j i}) A g ai y ls :
      symbol_lt ((proj1_sig j,y)::(i,g ai)::ls) ((i,ord A g)::ls).
    Proof.
      apply (symbol_lt_ord i (ord A g) (g ai) ls [(proj1_sig j,y)]).
      - apply (index_lt (ord A g) ai).
      - simpl; split; auto. apply (proj2_sig j).
    Qed.

    Fixpoint MultiVeblen (xs : list (Idx*Ord)) (HAcc : Acc symbol_lt xs) {struct HAcc} : Ord -> Ord :=
      fix inner (x:Ord) : Ord :=
        match xs as xs' return Acc symbol_lt xs' -> Ord with
        | [] => fun _ => f x
        | ((i,ord A g)::ls) => fun HAcc' =>
            match HAcc' with
            | Acc_intro _ Hsub =>
              MultiVeblen ls (Hsub ls (symbol_lt_drop i (ord A g) ls)) x ⊔
              match x with
              | ord X h =>
                @supOrd A (fun ai =>
                   fixOrd (MultiVeblen ((i,g ai)::ls) (Hsub _ (symbol_lt_ord i (ord A g) (g ai) ls nil (index_lt (ord A g) ai) I)))
                              (ord X (fun xi => inner (h xi)))
                   ⊔
                @supOrd { j:Idx | idx_lt j i} (fun j =>
                   fixOrd (fun y => MultiVeblen ((proj1_sig j,y)::(i,g ai)::ls) (Hsub _ (step_down i j A g ai y ls)) zeroOrd)
                       (ord X (fun xi => inner (h xi)))
                   ))
              end
        end
      end HAcc.

   End MultiVeblen.
End VeblenSymbol.

Definition nat_symbol := list (nat*Ord).

Require Import Lia.

Lemma nat_symbol_bounded : forall (x:nat_symbol), exists i, indices_bounded nat lt x i.
Proof.
  induction x; simpl.
  - exists O. auto.
  - destruct IHx as [i Hi].
    destruct a as [j _]; simpl.
    exists (Peano.max i (S j)).
    split; [ lia | ].
    induction x; simpl.
    + auto.
    + destruct a as [k y]; simpl in *.
      split; [ lia | intuition ].
Qed.

Require Import Wf_nat.

Lemma nat_symbol_lt_wf : well_founded (symbol_lt nat lt).
Proof.
  intro x.
  destruct (nat_symbol_bounded x) as [i Hi].
  apply symbol_lt_bounded_Acc with i; auto.
  apply lt_wf.
Qed.

Definition nth_veblen (n:nat) : Ord -> Ord :=
  MultiVeblen nat lt powOmega [(n,1)] (nat_symbol_lt_wf [(n,1)]).

Definition SmallVeblenOrdinal : Ord := ord nat (fun n => nth_veblen n 0).
