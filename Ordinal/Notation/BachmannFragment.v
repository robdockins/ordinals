From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.
From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannAssoc.
From Ordinal Require Import BachmannPower.
From Ordinal Require Import BachmannCfe.
From Ordinal Require Import BachmannNormal.
From Ordinal Require Import BachmannAgree.
From Ordinal Require Import BachmannFacts.
From Ordinal Require Import BachmannEnumeration.
From Ordinal Require Import Notation.SchutteMatrix.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorProduct.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.

From Ordinal Require Import Notation.BachmannNotation.

Open Scope ord_scope.
Open Scope bool_scope.

(** Part of the notation system up to the Bachmann–Howard ordinal; see @BachmannNotation.v@ for an overview. *)

(** ** Embedding Schütte's Klammersymbols

A matrix with columns (β₁,α₁), …, (βₙ,αₙ) of decreasing heights
denotes @schutte_matrix (addOrd 1) _ 0@.  A column of height β = 1+ζ
corresponds to the index summand Ω^ζ·α, by @bach_bexpΩ_rep@; a column
of height 0 (necessarily the last) is the argument. *)

(** 1+ζ = s: undo a leading 1+ when there is one. *)
Definition BS_pred1 (s:BSmall) : BSmall :=
  match s with
  | BN BIZ s' => s'
  | _ => s
  end.

Fixpoint Kl (x:VForm) : BSmall :=
  match x with
  | Z => BZ
  | N l =>
      BN ((fix cols (l:list (VForm * VForm)) : BIdx :=
             match l with
             | [] => BIZ
             | (b, a) :: l' =>
                 match b with
                 | Z => cols l'
                 | _ => BIC (idx_small (BS_pred1 (Kl b))) (Kl a) (cols l')
                 end
             end) l)
         ((fix arg (l:list (VForm * VForm)) : BSmall :=
             match l with
             | [] => BZ
             | (b, a) :: l' =>
                 match b with
                 | Z => Kl a
                 | _ => arg l'
                 end
             end) l)
  end.

Fixpoint Kidx (l:list (VForm * VForm)) : BIdx :=
  match l with
  | [] => BIZ
  | (b, a) :: l' =>
      match b with
      | Z => Kidx l'
      | _ => BIC (idx_small (BS_pred1 (Kl b))) (Kl a) (Kidx l')
      end
  end.

Fixpoint Karg (l:list (VForm * VForm)) : BSmall :=
  match l with
  | [] => BZ
  | (b, a) :: l' =>
      match b with
      | Z => Kl a
      | _ => Karg l'
      end
  end.

Lemma Kl_N l : Kl (N l) = BN (Kidx l) (Karg l).
Proof. reflexivity. Qed.

Lemma Kidx_shape l : idx_shape (Kidx l).
Proof.
  induction l as [|[b a] l IH]; simpl; auto.
  destruct b; simpl; auto. split; auto. discriminate.
Qed.

Lemma Kl_pos a : a <> Z -> 0 < BS_denote (Kl a).
Proof. destruct a as [|l]; [ tauto | intros _; rewrite Kl_N; apply BS_pos ]. Qed.

Lemma Kidx_head_pos l e c r : is_sparse l -> Kidx l = BIC e c r -> 0 < BS_denote c.
Proof.
  induction l as [|[b a] l IH]; simpl; [ discriminate | ].
  intros [Ha Hl]. destruct b as [|lb].
  - apply IH; auto.
  - intro E. injection E as _ <- _. apply Kl_pos; auto.
Qed.

(** The column height β is 1 + (the exponent we assign to it). *)
Lemma pred1_correct b : b <> Z -> VF_normal b -> VF_denote b ≈ BS_denote (Kl b) ->
  1 + BS_denote (BS_pred1 (Kl b)) ≈ VF_denote b.
Proof.
  destruct b as [|l]; [ tauto | ]. intros _ Hn Heq.
  rewrite Heq. rewrite Kl_N in *.
  destruct (Kidx l) as [|e c r] eqn:E.
  - simpl BS_pred1. symmetry. apply BS_denote_onePlus.
  - simpl BS_pred1. apply BS_denote_absorb.
    apply (Kidx_head_pos l e c r); auto. apply Hn.
Qed.

(** Reading a proper matrix as columns (1+ζ, α) followed by an argument. *)
Lemma Kmatrix l : forall G, (forall x y, x ≤ y -> G x ≤ G y) ->
  VF_matrix_proper l -> is_sparse l ->
  each (fun p => VF_normal (fst p) /\ VF_normal (snd p)) l ->
  each (fun p => VF_denote (fst p) ≈ BS_denote (Kl (fst p)) /\
                 VF_denote (snd p) ≈ BS_denote (Kl (snd p))) l ->
  schutte_matrix G (matrix_denote l) 0 ≈ schutte_matrix G (ocols (olist (Kidx l))) (BS_denote (Karg l)).
Proof.
  induction l as [|[b a] l IH]; intros G HG Hp Hs Hn Heq; simpl; [ reflexivity | ].
  simpl in Hp, Hs, Hn, Heq.
  destruct Hn as [[Hnb Hna] Hn]. destruct Heq as [[Eb Ea] Heq]. destruct Hs as [Ha Hs].
  destruct b as [|lb].
  - destruct l as [|[b2 a2] l].
    + simpl. rewrite schutte_column0. split; apply HG; rewrite addOrd_zero_r; apply Ea.
    + destruct Hp as [_ [_ [Hlt _]]].
      elim (ord_lt_irreflexive 0). apply ord_le_lt_trans with (VF_denote b2); [ apply zero_least | exact Hlt ].
  - assert (Hζ : 1 + BS_denote (BS_pred1 (Kl (N lb))) ≈ VF_denote (N lb)).
    { apply pred1_correct; auto. discriminate. }
    assert (Hl : VF_matrix_proper l).
    { destruct l as [|[b2 a2] l]; simpl; auto. apply Hp. }
    assert (HG1 : forall x y, x ≤ y -> schutte_column G (VF_denote (N lb)) (VF_denote a) x
                                       ≤ schutte_column G (VF_denote (N lb)) (VF_denote a) y).
    { intros x y Hxy. apply schutte_column_monotone; auto with ord. }
    change (schutte_matrix (schutte_column G (VF_denote (N lb)) (VF_denote a)) (matrix_denote l) 0
            ≈ schutte_matrix (schutte_column G (1 + BS_denote (BS_pred1 (Kl (N lb)))) (BS_denote (Kl a)))
                             (ocols (olist (Kidx l))) (BS_denote (Karg l))).
    rewrite (IH _ HG1 Hl Hs Hn Heq).
    split; apply schutte_matrix_monotone_func; auto;
      try (intros x y Hxy; apply schutte_column_monotone; auto with ord);
      intro x; apply schutte_column_monotone_full; auto with ord;
      first [ apply (proj1 Hζ) | apply (proj2 Hζ) | apply (proj1 Ea) | apply (proj2 Ea) ].
Qed.

(** An index below Ω^Ω represents the Klammersymbol whose columns are
    (1+ζ, c) for its summands Ω^ζ·c. *)
Lemma BI_rep T : idx_shape T ->
  BRep (addOrd 1) (BI_denote T) (schutte_matrix (addOrd 1) (ocols (olist T))).
Proof.
  intro HT.
  assert (Hc : each (fun p => complete (fst p) /\ complete (snd p)) (olist T)).
  { clear HT. induction T as [|e _ c r IH]; simpl; auto.
    split; auto using BS_complete. }
  apply BRep_bequiv with (ofold bzero (olist T)).
  - apply normal_monotone, onePlus_normal.
  - eapply bequiv_trans; [ apply ofold_osum | ].
    eapply bequiv_trans; [ apply bequiv_badd_zero_l | ].
    apply bequiv_sym, BI_osum; auto.
  - apply bfam_ofold, bfam_bzero.
  - apply BI_bfam.
  - apply ofold_rep; auto using bfam_bzero.
    + apply normal_monotone, onePlus_normal.
    + apply bach_zero_rep, onePlus_normal.
Qed.

(** Every Klammersymbol in normal form denotes the same ordinal as its
    translation; in particular Bachmann's φ (at the base 1+x) computes
    the Klammersymbol, by @BS_denote_bach@. *)
Theorem Kl_correct : forall x, VF_normal x -> VF_denote x ≈ BS_denote (Kl x).
Proof.
  induction x as [|l IHl] using VForm_induction; intro Hn.
  - reflexivity.
  - rewrite Kl_N.
    destruct Hn as [Hs [Hp [Hn Hlt]]].
    assert (Heq : each (fun p => VF_denote (fst p) ≈ BS_denote (Kl (fst p)) /\
                                 VF_denote (snd p) ≈ BS_denote (Kl (snd p))) l).
    { clear -IHl Hn. induction l as [|[b a] l IH]; simpl in *; auto. intuition. }
    rewrite BS_denote_bach.
    change (schutte_matrix (addOrd 1) (matrix_denote l) 0
            ≈ bach (addOrd 1) (BI_denote (Kidx l)) (BS_denote (Karg l))).
    rewrite (Kmatrix l (addOrd 1)); auto.
    + symmetry. apply (BI_rep (Kidx l) (Kidx_shape l)). apply BS_complete.
    + apply normal_monotone, onePlus_normal.
Qed.

(** * Sanity check: the fragment below Ω^Ω reaches the Large Veblen Ordinal

The notations whose exponents are all small denote exactly the values
of Schütte's Klammersymbols: @Kl@ translates Klammersymbols into the
fragment, and @Kinv@ translates back, both preserving denotation.  So
the fragment's order type is the Large Veblen Ordinal, as for
@SchutteMatrix@. *)

Fixpoint BS_frag (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y => BI_frag T /\ BS_frag y
  end
with BI_frag (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r =>
      match e with
      | BIZ => True
      | BIC BIZ s BIZ => BS_frag s
      | _ => False
      end /\ BS_frag c /\ BI_frag r
  end.

Lemma BI_frag_shape T : BI_frag T -> idx_shape T.
Proof.
  induction T as [|e _ c r IH]; simpl; auto.
  intros [He [_ Hr]]. split; auto.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl in *; try contradiction; discriminate.
Qed.

Lemma frag_pred1 u : BS_frag u -> BS_frag (BS_pred1 u).
Proof. destruct u as [|[|e c r] y]; simpl; intuition. Qed.

Lemma Kidx_frag l : each (fun p => BS_frag (Kl (fst p)) /\ BS_frag (Kl (snd p))) l ->
  BI_frag (Kidx l) /\ BS_frag (Karg l).
Proof.
  induction l as [|[b a] l IH]; [ simpl; auto | ].
  intros [[Hb Ha] Hl]. destruct (IH Hl) as [H1 H2].
  destruct b as [|lb].
  - change (BI_frag (Kidx l) /\ BS_frag (Kl a)). split; auto.
  - change (BI_frag (BIC (idx_small (BS_pred1 (Kl (N lb)))) (Kl a) (Kidx l)) /\ BS_frag (Karg l)).
    split; auto.
    split; [ change (BS_frag (BS_pred1 (Kl (N lb)))); apply frag_pred1; auto | split; auto ].
Qed.

Lemma Kl_frag : forall x, BS_frag (Kl x).
Proof.
  induction x as [|l IHl] using VForm_induction; [ simpl; auto | ].
  rewrite Kl_N. apply Kidx_frag; auto.
Qed.

Fixpoint Kinv (x:BSmall) : VForm :=
  match x with
  | BZ => Z
  | BN T y => N (Kinv_cols T ++ [(Z, Kinv y)])
  end
with Kinv_cols (T:BIdx) : list (VForm * VForm) :=
  match T with
  | BIZ => []
  | BIC e c r => (Kinv_exp e, Kinv c) :: Kinv_cols r
  end
with Kinv_exp (e:BIdx) : VForm :=
  match e with
  | BIC BIZ s BIZ => N [(Z, Kinv s)]
  | _ => N []
  end.

Lemma VF_onePlus v : VF_denote (N [(Z, v)]) ≈ 1 + VF_denote v.
Proof.
  change (schutte_column (addOrd 1) 0 (VF_denote v) 0 ≈ 1 + VF_denote v).
  rewrite schutte_column0. rewrite addOrd_zero_r. reflexivity.
Qed.

Theorem Kinv_correct :
  (forall x, BS_frag x -> VF_denote (Kinv x) ≈ BS_denote x) /\
  (forall T, BI_frag T -> meq (matrix_denote (Kinv_cols T)) (ocols (olist T))).
Proof.
  apply BNotation_mut.
  - intros _. reflexivity.
  - intros T IHT y IHy [HT Hy].
    assert (HM := IHT HT).
    assert (Hv := IHy Hy).
    destruct (BI_rep T (BI_frag_shape T HT)) as [HG [Hrep _]].
    change (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T ++ [(Z, Kinv y)])) 0
            ≈ BS_denote (BN T y)).
    unfold matrix_denote. rewrite map_app. rewrite schutte_matrix_app.
    change (schutte_column (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T))) 0 (VF_denote (Kinv y)) 0
            ≈ BS_denote (BN T y)).
    transitivity (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T)) (VF_denote (Kinv y) + 0));
      [ apply schutte_column0 | ].
    transitivity (schutte_matrix (addOrd 1) (ocols (olist T)) (VF_denote (Kinv y) + 0)).
    { apply schutte_matrix_meq; auto. apply normal_monotone, onePlus_normal. }
    transitivity (schutte_matrix (addOrd 1) (ocols (olist T)) (BS_denote y)).
    { apply ord_eq_normal; auto. rewrite addOrd_zero_r. auto. }
    rewrite BS_denote_bach. symmetry. apply Hrep, BS_complete.
  - intros _. constructor.
  - intros e IHe c IHc r IHr [He [Hc Hr]]. simpl.
    constructor; auto.
    destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl in He; try contradiction.
    + unfold exp_s, exp_small. simpl. reflexivity.
    + assert (H := IHe (conj I (conj He I))). simpl in H.
      inversion H as [|b0 a0 m0 b0' a0' m0' Hb0 Ha0 Hm0]; subst.
      unfold exp_s, exp_small. simpl Kinv_exp.
      rewrite VF_onePlus. split; apply addOrd_monotone; auto with ord; apply Ha0.
Qed.

Theorem frag_bounded x : BS_frag x -> BS_denote x < LargeVeblenOrdinal.
Proof.
  intro Hx. rewrite <- (proj1 Kinv_correct x Hx). apply VForm_bounded.
Qed.

Definition FragOrd : Ord := ord {x:BSmall | BS_frag x} (fun x => BS_denote (proj1_sig x)).

Theorem FragOrd_LVO : FragOrd ≈ LargeVeblenOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. intros [x Hx]. simpl. apply frag_bounded; auto.
  - rewrite ord_le_unfold. intro a.
    destruct (LVO_proper_VForm (LargeVeblenOrdinal a)) as [y [Hp Hle]].
    { apply index_lt. }
    destruct (VF_normalize_correct y Hp) as [Heq Hn].
    rewrite ord_lt_unfold.
    exists (exist _ (Kl (VF_normalize y)) (Kl_frag _)). simpl.
    rewrite Hle, <- Heq. apply Kl_correct; auto.
Qed.
