Require Import Setoid.
Require Import Morphisms.
Require Import Coq.Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.

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
      symbol_lt (ys ++ ((i,x')::ls)) ((i,x)::ls).

  Definition VeblenSymbol_lt (xs ys : VeblenSymbol) : Prop :=
    symbol_lt (proj1_sig xs) (proj1_sig ys).

  Lemma symbol_lt_eq_Acc : forall a,
    Acc (fun xs0 ys : VeblenSymbol => symbol_lt (proj1_sig xs0) (proj1_sig ys)) a ->
    forall b,
      proj1_sig a = proj1_sig b ->
      Acc (fun xs0 ys : VeblenSymbol => symbol_lt (proj1_sig xs0) (proj1_sig ys)) b.
  Proof.
    intros a Ha; induction Ha.
    destruct x as [x Hx].
    intros [y Hy]. simpl. intros. subst y.
    constructor. simpl.
    intros [z Hz] Hlt; simpl in *.
    apply (H (exist _ z Hz) Hlt).
  Qed.

  Lemma symbol_lt_append_Acc : forall a,
    Acc (fun xs0 ys : VeblenSymbol => symbol_lt (proj1_sig xs0) (proj1_sig ys)) a ->
    forall b,
    Acc (fun xs0 ys : VeblenSymbol => symbol_lt (proj1_sig xs0) (proj1_sig ys)) b ->
    forall c,
    proj1_sig a ++ proj1_sig b = proj1_sig c ->
    Acc (fun xs0 ys : VeblenSymbol => symbol_lt (proj1_sig xs0) (proj1_sig ys)) c.
  Proof.
    intros a Ha. induction Ha.
    intros b Hb c Hc.
    constructor. intros [y Hy_f].
    destruct c as [c Hc_f]. simpl.
    intros Hlt. simpl in *.
    destruct x as [x Hx_f]. simpl in *.
    destruct x as [|[j o]].
    - simpl in *. subst c.
      destruct b as [b Hb_f].
      simpl in *.
      inversion Hb. simpl in *.
      apply H1; simpl; auto.
    - inversion Hlt; subst.
      + simpl in H2.
        inversion H2; subst.
        simpl in Hx_f.
        assert (Hx_f' : well_formed_symbol x).
        { apply well_formed_tail_symbol with j; auto. }
        apply H0 with (exist _ x Hx_f') b; auto.
        simpl. apply symbol_lt_drop.
      + simpl in H3.
        inversion H3; subst.
        assert (Hprefix : well_formed_symbol (ys ++ (j,x') :: x)).
        { eapply is_well_formed_prefix with (proj1_sig b).
          rewrite <- app_assoc. auto.
        }
        apply H0 with (exist _ (ys ++ (j,x') :: x) Hprefix) b; auto.
        apply symbol_lt_ord; auto.
        simpl.
        rewrite <- app_assoc. simpl; auto.
  Qed.

  Theorem VeblenSymbol_lt_wf : well_founded VeblenSymbol_lt.
  Proof.
    unfold VeblenSymbol_lt.
    intros [xs Hxs].
    destruct (well_formed_symbols_bounded xs Hxs) as [i Hi].
    revert xs Hxs Hi.
    induction i as [i Hind_i] using (well_founded_induction idx_lt_wf).
    induction xs.
    - constructor. intros [ys Hys]; simpl. intro H.
      inversion H.
    - destruct a as [j x]. simpl in *.
      induction x as [x Hind_x] using ordinal_induction.
      intros Hxs [Hj Hi].
      constructor. intros [ys Hys]; simpl. intro H.
      inversion H; subst.
      + apply IHxs; auto.
      + assert (Hy_f : well_formed_symbol ys0).
        { apply is_well_formed_prefix with ((j,x') :: xs); auto. }
        assert (Hx_f' : well_formed_symbol ((j,x') :: xs)).
        { simpl; auto. }
        apply symbol_lt_append_Acc with (exist _ ys0 Hy_f) (exist _ ((j,x')::xs) Hx_f'); simpl.
        * apply (Hind_i j); auto.
          eapply well_formed_bounded. apply Hys.
        * apply Hind_x; auto.
        * auto.
  Qed.

  Section MultiVeblen.
    Variable f : Ord -> Ord.
    Require Import Program.Wf.
    Require Import Veblen.

    Fixpoint MultiVeblen (xs : VeblenSymbol) (HAcc : Acc VeblenSymbol_lt xs) {struct HAcc} : Ord -> Ord :=
      fix inner (x:Ord) : Ord :=
        match xs as xs' return Acc VeblenSymbol_lt xs' -> Ord with
        | exist _ [] _ => fun _ => f x
        | exist _ ((i,ord A g)::ls) H => fun HAcc' =>
            match HAcc' with
            | Acc_intro _ Hsub =>
              MultiVeblen (exist _ ls (is_well_formed_tail (i,ord A g) ls H)) (Hsub (exist _ ls (is_well_formed_tail (i,ord A g) ls H)) (symbol_lt_drop i (ord A g) ls)) x ⊔
              match x with
              | ord X h =>
                @supOrd A (fun ai =>
                @supOrd { j:Idx | idx_lt j i} (fun j =>
                   normal_fix (fun y => MultiVeblen (exist _ ((proj1_sig j,y)::(i,g ai)::ls) (is_well_formed_cons (proj1_sig j) y i x (g ai) ls (proj2_sig j) H)) (Hsub (exist _ ((proj1_sig j,y)::(i,g ai)::ls) (is_well_formed_cons (proj1_sig j) y i x (g ai) ls (proj2_sig j) H)) (symbol_lt_ord i (ord A g) (g ai) ls [(proj1_sig j,y)] (index_lt (ord A g) ai))) zeroOrd)
                       (ord X (fun xi => inner (h xi)))
                   ))
              end
        end
      end HAcc.
   End MultiVeblen.
End VeblenSymbol.
