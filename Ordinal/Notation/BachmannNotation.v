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
From Ordinal Require Import BachmannNormal.
From Ordinal Require Import BachmannFacts.
From Ordinal Require Import Notation.SchutteMatrix.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorProduct.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.

Open Scope ord_scope.
Open Scope bool_scope.
Open Scope ord_scope.

(** * A notation system up to the Bachmann–Howard ordinal

A small notation is 0 or φ_T(y), where y is a small notation and T is
an index.  An index is 0 or Ω^e·c + r, where the exponent e and the
rest r are indices and the coefficient c is a small notation; in
normal form the exponents strictly decrease, so an index is an
Ω-Cantor normal form.  Indices denote canonical index trees, built
from @embed@, @badd@, @bmul@ and @bexpΩ@; φ is taken at the base 1+x.

We denote φ_T(y) by the provably normal hierarchy @bphi@, whose values
are complete; Bachmann's φ (@bach@) agrees with it on every notation
(@BS_denote_bach@).  The argument y cannot be folded into the index:
@bach f (T + ξ) 0@ is @veblen G ξ 0@, not @G ξ@. *)

Inductive BSmall : Set :=
| BZ : BSmall
| BN : BIdx -> BSmall -> BSmall
with BIdx : Set :=
| BIZ : BIdx
| BIC : BIdx -> BSmall -> BIdx -> BIdx.

Scheme BSmall_mut := Induction for BSmall Sort Prop
with BIdx_mut := Induction for BIdx Sort Prop.
Combined Scheme BNotation_mut from BSmall_mut, BIdx_mut.

Fixpoint BS_denote (x:BSmall) : Ord :=
  match x with
  | BZ => 0
  | BN T y => bphi (addOrd 1) (BI_denote T) (BS_denote y)
  end
with BI_denote (T:BIdx) : BOrd :=
  match T with
  | BIZ => bzero
  | BIC e c r => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)
  end.

(** ** Denotations are complete, canonical and directed *)

Definition idx_ok (T:BOrd) : Prop := bcd T /\ bsdirH T.

Lemma bcd_bzero : bcd bzero.
Proof. split; [ apply bcanon_bzero | apply bdec_bzero ]. Qed.

Lemma idx_ok_bzero : idx_ok bzero.
Proof. split; [ apply bcd_bzero | apply bsdirH_bzero ]. Qed.

Lemma idx_ok_term e c : idx_ok e -> complete c -> idx_ok (bmul (bexpΩ e) (embed c)).
Proof.
  intros [He1 He2] Hc. split.
  - apply bcd_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ.
  - apply bsdirH_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ, bsdirH_embed.
    apply bsdirH_bexpΩ; auto.
Qed.

Lemma idx_ok_badd x y : idx_ok x -> idx_ok y -> idx_ok (badd x y).
Proof. intros [H1 H2] [H3 H4]. split; [ apply bcd_badd | apply bsdirH_badd ]; auto. Qed.

Theorem BNotation_ok :
  (forall x, complete (BS_denote x)) /\ (forall T, idx_ok (BI_denote T)).
Proof.
  apply BNotation_mut; simpl.
  - apply zero_complete.
  - intros T [HT1 HT2] y Hy.
    apply normal_complete; auto. apply bcanon_normal; auto. apply onePlus_normal.
  - apply idx_ok_bzero.
  - intros e He c Hc r Hr. apply idx_ok_badd; auto. apply idx_ok_term; auto.
Qed.

Lemma BS_complete x : complete (BS_denote x).
Proof. apply BNotation_ok. Qed.

Lemma BI_ok T : idx_ok (BI_denote T).
Proof. apply BNotation_ok. Qed.

Lemma BI_bfam T : bfam (BI_denote T).
Proof. apply bcanon_bfam, BI_ok. Qed.

Lemma BI_good T : bgood (addOrd 1) (BI_denote T).
Proof.
  destruct (BI_ok T) as [[H1 H2] _].
  apply (bcanon_good (addOrd 1) onePlus_normal); auto.
Qed.

(** For each index, ξ ↦ φ_T(ξ) is a normal function. *)
Theorem BI_normal T : normal_function (bphi (addOrd 1) (BI_denote T)).
Proof. apply bcanon_normal; [ apply onePlus_normal | apply BI_ok ]. Qed.

(** Bachmann's φ, one component at a time, agrees with the denotation. *)
Theorem BS_denote_bach T y : BS_denote (BN T y) ≈ bach (addOrd 1) (BI_denote T) (BS_denote y).
Proof.
  symmetry.
  destruct (BI_ok T) as [H1 H2].
  apply (bach_bphi_canon (addOrd 1) onePlus_normal _ H1 H2). apply BS_complete.
Qed.

Corollary BS_denote_bach0 T : BS_denote (BN T BZ) ≈ bach (addOrd 1) (BI_denote T) 0.
Proof. apply BS_denote_bach. Qed.

(** ** Basic calibrations *)

Lemma BS_denote_onePlus y : BS_denote (BN BIZ y) ≈ 1 + BS_denote y.
Proof. apply (bphi_bzero (addOrd 1) onePlus_normal). Qed.

Lemma BS_pos T y : 0 < BS_denote (BN T y).
Proof. apply (bphi_nonzero (addOrd 1) onePlus_normal). Qed.

Lemma badd_inh_l x y : inhabited (bsmall x + bbig x) -> inhabited (bsmall (badd x y) + bbig (badd x y)).
Proof.
  intros [[a|c]].
  - destruct (badd_small_l x y a) as [a' _]. exact (inhabits (inl a')).
  - destruct (badd_big_l x y c) as [c' _]. exact (inhabits (inr c')).
Qed.

(** A leading summand with positive coefficient gives the index a component. *)
Lemma BI_inh e c r : 0 < BS_denote c -> inhabited (bsmall (BI_denote (BIC e c r)) + bbig (BI_denote (BIC e c r))).
Proof.
  intro Hc. simpl. apply badd_inh_l.
  destruct (BS_denote c) as [X k].
  rewrite ord_lt_unfold in Hc. destruct Hc as [x _].
  destruct (bexpΩ_small_zero (BI_denote e)) as [t0 _].
  destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (k x))) (bexpΩ (BI_denote e)) t0) as [s _].
  destruct (bmul_small_r (bexpΩ (BI_denote e)) (embed (ord X k)) x s) as [t _].
  exact (inhabits (inl t)).
Qed.

(** With a nonempty index of positive leading coefficient, φ_T(y) is
    infinite, i.e., absorbs 1+. *)
Lemma BS_denote_absorb e c r y : 0 < BS_denote c ->
  1 + BS_denote (BN (BIC e c r) y) ≈ BS_denote (BN (BIC e c r) y).
Proof.
  intro Hc.
  exact (bphi_onePlus_absorb (BI_denote (BIC e c r)) (BS_denote y) (BI_good _) (BI_inh e c r Hc) (BS_complete y)).
Qed.

(** ** Indices below Ω^Ω

An exponent is small when it is 0 or Ω^0·s; the index then lies below
Ω^Ω and corresponds to a list of (exponent, coefficient) pairs of
ordinals. *)

Definition exp_small (e:BIdx) : option BSmall :=
  match e with
  | BIZ => Some BZ
  | BIC BIZ s BIZ => Some s
  | _ => None
  end.

Definition exp_s (e:BIdx) : BSmall :=
  match exp_small e with Some s => s | None => BZ end.

(** The exponent Ω^0·s. *)
Definition idx_small (s:BSmall) : BIdx := BIC BIZ s BIZ.

Lemma bequiv_bzero_embed0 : bequiv bzero (embed 0).
Proof. split; apply bsub_intro; intros []. Qed.

Lemma exp_equiv e s : exp_small e = Some s -> bequiv (BI_denote e) (embed (BS_denote s)).
Proof.
  destruct e as [|[|e1 c1 r1] s0 [|e2 c2 r2]]; simpl; intro H; try discriminate.
  - injection H as <-. apply bequiv_bzero_embed0.
  - injection H as <-.
    eapply bequiv_trans; [ apply bequiv_badd_zero_r | apply bequiv_one_mul ].
Qed.

Fixpoint olist (T:BIdx) : list (Ord * Ord) :=
  match T with
  | BIZ => []
  | BIC e c r => (BS_denote (exp_s e), BS_denote c) :: olist r
  end.

Fixpoint idx_shape (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => exp_small e <> None /\ idx_shape r
  end.

Lemma BI_osum T : idx_shape T -> bequiv (BI_denote T) (osum (olist T)).
Proof.
  induction T as [|e _ c r IH]; simpl; auto.
  - intros _. apply bequiv_refl.
  - intros [He Hr].
    apply bequiv_badd; auto.
    unfold oterm; simpl. apply bequiv_bmul; [ | apply bequiv_refl ].
    apply bequiv_bexpΩ. unfold exp_s.
    destruct (exp_small e) eqn:E; [ apply exp_equiv; auto | tauto ].
Qed.

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

Lemma ord_eq_normal G : normal_function G -> forall x y, x ≈ y -> G x ≈ G y.
Proof. intros HG x y [H1 H2]; split; apply normal_monotone; auto. Qed.

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

(** * Normal forms and comparison

φ_T(y) is normal when T is a normal Ω-Cantor normal form (exponents
strictly decreasing in the index order, coefficients positive), the
argument is not a fixpoint (y < φ_T(y)), and every coefficient
occurring in T, at any depth, lies below φ_T(y).  Comparison is
Bachmann's rule: for T < T', φ_T(a) < φ_{T'}(b) iff a and every
coefficient of T lie below φ_{T'}(b), because then φ_{T'}(b) is a
fixpoint of φ_T (the nesting theorem @nest@). *)

(** ** The order on indices *)

Inductive ieq : BIdx -> BIdx -> Prop :=
| ieq_nil : ieq BIZ BIZ
| ieq_cons : forall e c r e' c' r', ieq e e' -> BS_denote c ≈ BS_denote c' -> ieq r r' ->
    ieq (BIC e c r) (BIC e' c' r').

Inductive ilt : BIdx -> BIdx -> Prop :=
| ilt_nil : forall e c r, ilt BIZ (BIC e c r)
| ilt_exp : forall e c r e' c' r', ilt e e' -> ilt (BIC e c r) (BIC e' c' r')
| ilt_coef : forall e c r e' c' r', ieq e e' -> BS_denote c < BS_denote c' -> ilt (BIC e c r) (BIC e' c' r')
| ilt_tail : forall e c r e' c' r', ieq e e' -> BS_denote c ≈ BS_denote c' -> ilt r r' ->
    ilt (BIC e c r) (BIC e' c' r').

Lemma ieq_sym T T' : ieq T T' -> ieq T' T.
Proof. intro H. induction H; constructor; auto. symmetry; auto. Qed.

Lemma ieq_bequiv T T' : ieq T T' -> bequiv (BI_denote T) (BI_denote T').
Proof.
  intro H. induction H as [|e c r e' c' r' He IHe Hc Hr IHr]; simpl; [ apply bequiv_refl | ].
  apply bequiv_badd; auto. apply bequiv_bmul; [ apply bequiv_bexpΩ; auto | apply bequiv_embed; auto ].
Qed.

(** Every coefficient, at any depth, lies below z. *)
Fixpoint Klt (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => Klt z e /\ BS_denote c < z /\ Klt z r
  end.

(** Some coefficient, at some depth, is at least z. *)
Fixpoint Kge (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC e c r => Kge z e \/ z ≤ BS_denote c \/ Kge z r
  end.

Lemma Kge_lt z w T : Kge z T -> Klt w T -> z < w.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [H1 [H2 H3]]; auto. eapply ord_le_lt_trans; eauto.
Qed.

Definition lead_below (r e:BIdx) : Prop :=
  match r with
  | BIZ => True
  | BIC e2 _ _ => ilt e2 e
  end.

Fixpoint BS_nf (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y =>
      BI_nf T /\ BS_nf y /\
      BS_denote y < BS_denote (BN T y) /\ Klt (BS_denote (BN T y)) T
  end
with BI_nf (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => BI_nf e /\ BS_nf c /\ 0 < BS_denote c /\ BI_nf r /\ lead_below r e
  end.

(** ** Sizes *)

Fixpoint BS_size (x:BSmall) : nat :=
  match x with
  | BZ => 1
  | BN T y => S (BI_size T + BS_size y)
  end
with BI_size (T:BIdx) : nat :=
  match T with
  | BIZ => 1
  | BIC e c r => S (BI_size e + BS_size c + BI_size r)
  end.

(** ** The nesting theorem

A smaller normal index, whose coefficients all lie below an infinite z,
is z-reachably below a larger one; and an index whose leading exponent
is z-reachably below a lies z-reachably below Ω^a. *)

Lemma term_pos e c : 0 < BS_denote c -> bpos (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))).
Proof.
  intro Hc. apply bslt_bsub_r with (bexpΩ (BI_denote e)); [ apply bpos_bexpΩ | apply bsub_P_Pz; auto ].
Qed.

Lemma lead_pos e c r : 0 < BS_denote c -> bpos (BI_denote (BIC e c r)).
Proof. intro Hc. simpl. apply bslt_bsub_r with (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))); [ apply term_pos; auto | apply bsub_le_badd ]. Qed.

Theorem nest z : oinf z -> forall n T, (BI_size T < n)%nat -> BI_nf T -> Klt z T ->
  (forall T', BI_nf T' -> ilt T T' -> zlt z (BI_denote T) (BI_denote T')) /\
  (forall a, match T with BIZ => True | BIC e _ _ => zlt z (BI_denote e) a end ->
             zlt z (BI_denote T) (bexpΩ a)).
Proof.
  intros Hz n. induction n as [|n IH]; intros T Hsz HT HK; [ lia | ].
  assert (B : forall a, match T with BIZ => True | BIC e _ _ => zlt z (BI_denote e) a end ->
                        zlt z (BI_denote T) (bexpΩ a)).
  { intros a Ha. destruct T as [|e c r]; [ apply zlt_bslt, bpos_bexpΩ | ].
    simpl in Hsz. destruct HT as [He [_ [Hc0 [Hr Hlead]]]]. destruct HK as [HKe [Hcz HKr]].
    assert (Hrb : zlt z (BI_denote r) (bexpΩ (BI_denote e))).
    { apply (proj2 (IH r ltac:(lia) Hr HKr)).
      destruct r as [|e2 c2 r2]; auto.
      simpl in Hlead. destruct Hr as [He2 _]. simpl in HKr.
      apply (proj1 (IH e2 ltac:(simpl in Hsz; lia) He2 (proj1 HKr))); auto. }
    simpl. apply zlt_bleZ with (bmul (bexpΩ (BI_denote e)) (embed z)); [ | apply zlt_exp; auto ].
    apply zlt_mono_r with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (bexpΩ (BI_denote e))).
    - apply zlt_shift; auto.
    - eapply bsub_trans; [ apply bsub_mul_succ | ].
      apply bsub_bmul_r, bsub_embed, succ_least; auto. }
  split; auto.
  intros T' HT' Hlt.
  destruct Hlt as [e' c' r' | e c r e' c' r' Hee | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr].
  - apply zlt_bslt, lead_pos. apply HT'.
  - simpl in Hsz. destruct HT as [He _]. destruct HK as [HKe _].
    apply zlt_mono_r with (bexpΩ (BI_denote e')).
    + apply B. apply (proj1 (IH e ltac:(lia) He HKe)); auto. apply HT'.
    + simpl. eapply bsub_trans; [ apply bsub_P_Pz, HT' | apply bsub_le_badd ].
  - simpl in Hsz. destruct HT as [He [_ [_ [Hr Hlead]]]]. destruct HK as [_ [Hcz HKr]].
    assert (Hrb : zlt z (BI_denote r) (bexpΩ (BI_denote e))).
    { apply (proj2 (IH r ltac:(lia) Hr HKr)).
      destruct r as [|e2 c2 r2]; auto.
      simpl in Hlead. destruct Hr as [He2 _]. simpl in HKr.
      apply (proj1 (IH e2 ltac:(simpl in Hsz; lia) He2 (proj1 HKr))); auto. }
    simpl. apply zlt_mono_r with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (bexpΩ (BI_denote e))).
    + apply zlt_shift; auto.
    + eapply bsub_trans; [ apply bsub_mul_succ | ].
      eapply bsub_trans; [ | apply bsub_le_badd ].
      eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, succ_least, Hcc | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee).
  - simpl in Hsz. destruct HT as [_ [_ [_ [Hr _]]]]. destruct HK as [_ [_ HKr]].
    destruct HT' as [_ [_ [_ [Hr' _]]]].
    simpl. apply zlt_mono_r with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r')).
    + apply zlt_shift. apply (proj1 (IH r ltac:(lia) Hr HKr)); auto.
    + apply bsub_badd_l. eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, Hcc | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee).
Qed.

(** ** Semantic cases of the comparison *)

Lemma BN_inf T y : BI_nf T -> T <> BIZ -> oinf (BS_denote (BN T y)).
Proof.
  intros HT Hne. destruct T as [|e c r]; [ tauto | ].
  exact (bphi_value_inf (addOrd 1) onePlus_normal (BI_denote (BIC e c r)) (BS_denote y)
           (fun x => addOrd_le2 1 x) (fun x _ => ord_le_refl _) (BI_good _)
           (BI_inh e c r (proj1 (proj2 (proj2 HT)))) (BS_complete y)).
Qed.

(** Bachmann's rule for distinct indices. *)
Lemma nest_lt T a T' b :
  BS_nf (BN T a) -> BS_nf (BN T' b) -> ilt T T' ->
  BS_denote a < BS_denote (BN T' b) -> Klt (BS_denote (BN T' b)) T ->
  BS_denote (BN T a) < BS_denote (BN T' b).
Proof.
  intros [HT _] [HT' _] Hlt Ha Hc.
  set (z := BS_denote (BN T' b)) in *.
  assert (Hne : T' <> BIZ) by (intro E; subst; inversion Hlt).
  assert (Hz : zlt z (BI_denote T) (BI_denote T')).
  { apply (proj1 (nest z (BN_inf T' b HT' Hne) (S (BI_size T)) T ltac:(lia) HT Hc)); auto. }
  assert (Hi : inhabited (bsmall (BI_denote T') + bbig (BI_denote T'))).
  { destruct T' as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HT'. }
  assert (Hfix := zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b)
                    Hz (BI_good T') (BI_bfam T') Hi (BS_complete b)).
  eapply ord_lt_le_trans; [ | exact Hfix ].
  apply normal_increasing; auto using BI_normal.
  apply (BS_complete (BN T' b)).
Qed.

Lemma bphi_ieq T T' y : ieq T T' ->
  bphi (addOrd 1) (BI_denote T) y ≈ bphi (addOrd 1) (BI_denote T') y.
Proof.
  intro H. apply bphi_bequiv; auto using BI_bfam, ieq_bequiv.
  apply normal_monotone, onePlus_normal.
Qed.


(** ** The comparison algorithm *)

Definition isLT (o:ordering) : bool := match o with LT => true | _ => false end.

Fixpoint cmpS (n:nat) (x y:BSmall) {struct n} : ordering :=
  match n with
  | O => EQ
  | S n' =>
    match x, y with
    | BZ, BZ => EQ
    | BZ, BN _ _ => LT
    | BN _ _, BZ => GT
    | BN T a, BN T' b =>
      let fix below (T:BIdx) (z:BSmall) : bool :=
          match T with
          | BIZ => true
          | BIC e c r => below e z && isLT (cmpS n' c z) && below r z
          end in
      match cmpI n' T T' with
      | EQ => cmpS n' a b
      | LT => if isLT (cmpS n' a y) && below T y then LT else GT
      | GT => if isLT (cmpS n' b x) && below T' x then GT else LT
      end
    end
  end
with cmpI (n:nat) (T T':BIdx) {struct n} : ordering :=
  match n with
  | O => EQ
  | S n' =>
    match T, T' with
    | BIZ, BIZ => EQ
    | BIZ, BIC _ _ _ => LT
    | BIC _ _ _, BIZ => GT
    | BIC e c r, BIC e' c' r' =>
      match cmpI n' e e' with
      | LT => LT
      | GT => GT
      | EQ => match cmpS n' c c' with
              | LT => LT
              | GT => GT
              | EQ => cmpI n' r r'
              end
      end
    end
  end.

Definition coefs_below (n:nat) : BIdx -> BSmall -> bool :=
  fix below (T:BIdx) (z:BSmall) : bool :=
    match T with
    | BIZ => true
    | BIC e c r => below e z && isLT (cmpS n c z) && below r z
    end.

Lemma cmpS_BN n T a T' b : cmpS (S n) (BN T a) (BN T' b) =
  match cmpI n T T' with
  | EQ => cmpS n a b
  | LT => if isLT (cmpS n a (BN T' b)) && coefs_below n T (BN T' b) then LT else GT
  | GT => if isLT (cmpS n b (BN T a)) && coefs_below n T' (BN T a) then GT else LT
  end.
Proof. reflexivity. Qed.

Definition cmpI_ok (o:ordering) (T T':BIdx) : Prop :=
  match o with
  | LT => ilt T T'
  | EQ => ieq T T'
  | GT => ilt T' T
  end.

Lemma isLT_spec o a b : ordering_correct o a b ->
  (isLT o = true -> a < b) /\ (isLT o = false -> b ≤ a).
Proof.
  destruct o; simpl; intro H; split; intro E; try discriminate; auto.
  - apply H.
  - apply ord_lt_le; auto.
Qed.

Lemma coefs_below_spec n y : forall T,
  (forall c, (BS_size c <= BI_size T)%nat -> BS_nf c -> ordering_correct (cmpS n c y) (BS_denote c) (BS_denote y)) ->
  BI_nf T ->
  (coefs_below n T y = true -> Klt (BS_denote y) T) /\
  (coefs_below n T y = false -> Kge (BS_denote y) T).
Proof.
  induction T as [|e IHe c r IHr]; intros Hc HT; [ simpl; split; auto; discriminate | ].
  simpl in Hc. destruct HT as [He [Hcn [_ [Hr _]]]].
  destruct (IHe (fun c0 H => Hc c0 ltac:(lia)) He) as [E1 E2].
  destruct (IHr (fun c0 H => Hc c0 ltac:(lia)) Hr) as [R1 R2].
  destruct (isLT_spec _ _ _ (Hc c ltac:(lia) Hcn)) as [S1 S2].
  change ((coefs_below n e y && isLT (cmpS n c y) && coefs_below n r y = true ->
           Klt (BS_denote y) e /\ BS_denote c < BS_denote y /\ Klt (BS_denote y) r) /\
          (coefs_below n e y && isLT (cmpS n c y) && coefs_below n r y = false ->
           Kge (BS_denote y) e \/ BS_denote y ≤ BS_denote c \/ Kge (BS_denote y) r)).
  destruct (coefs_below n e y); destruct (isLT (cmpS n c y)); destruct (coefs_below n r y); simpl;
    split; intro H; try discriminate; intuition.
Qed.

Theorem cmp_correct n :
  (forall x y, (BS_size x + BS_size y < n)%nat -> BS_nf x -> BS_nf y ->
               ordering_correct (cmpS n x y) (BS_denote x) (BS_denote y)) /\
  (forall T T', (BI_size T + BI_size T' < n)%nat -> BI_nf T -> BI_nf T' -> cmpI_ok (cmpI n T T') T T').
Proof.
  induction n as [|n [IHS IHI]]; [ split; intros; lia | ].
  split.
  - intros x y Hsz Hx Hy.
    destruct x as [|T a]; destruct y as [|T' b].
    + simpl. reflexivity.
    + apply BS_pos.
    + apply BS_pos.
    + rewrite cmpS_BN. simpl in Hsz.
      assert (Hx' := Hx). assert (Hy' := Hy).
      destruct Hx' as [HT [Ha [Hax Hcx]]]. destruct Hy' as [HT' [Hb [Hby Hcy]]].
      assert (HI := IHI T T' ltac:(lia) HT HT').
      destruct (cmpI n T T') eqn:EI; simpl in HI.
      * destruct (isLT_spec _ _ _ (IHS a (BN T' b) ltac:(simpl; lia) Ha Hy)) as [A1 A2].
        destruct (coefs_below_spec n (BN T' b) T
                    (fun c Hc Hcn => IHS c (BN T' b) ltac:(simpl; lia) Hcn Hy) HT) as [C1 C2].
        destruct (isLT (cmpS n a (BN T' b))) eqn:E1; destruct (coefs_below n T (BN T' b)) eqn:E2; simpl.
        -- apply nest_lt; auto.
        -- apply (Kge_lt _ _ T); auto.
        -- apply ord_le_lt_trans with (BS_denote a); auto.
        -- apply ord_le_lt_trans with (BS_denote a); auto.
      * assert (Heq := bphi_ieq T T' (BS_denote b) HI).
        assert (Hab := IHS a b ltac:(lia) Ha Hb).
        change (ordering_correct (cmpS n a b) (bphi (addOrd 1) (BI_denote T) (BS_denote a))
                                 (bphi (addOrd 1) (BI_denote T') (BS_denote b))).
        rewrite <- Heq.
        destruct (cmpS n a b); simpl in *.
        -- apply normal_increasing; auto using BI_normal, BS_complete.
        -- apply ord_eq_normal; auto using BI_normal.
        -- apply normal_increasing; auto using BI_normal, BS_complete.
      * destruct (isLT_spec _ _ _ (IHS b (BN T a) ltac:(simpl; lia) Hb Hx)) as [A1 A2].
        destruct (coefs_below_spec n (BN T a) T'
                    (fun c Hc Hcn => IHS c (BN T a) ltac:(simpl; lia) Hcn Hx) HT') as [C1 C2].
        destruct (isLT (cmpS n b (BN T a))) eqn:E1; destruct (coefs_below n T' (BN T a)) eqn:E2; simpl.
        -- apply nest_lt; auto.
        -- apply (Kge_lt _ _ T'); auto.
        -- apply ord_le_lt_trans with (BS_denote b); auto.
        -- apply ord_le_lt_trans with (BS_denote b); auto.
  - intros T T' Hsz HT HT'.
    destruct T as [|e c r]; destruct T' as [|e' c' r']; simpl.
    + constructor.
    + constructor.
    + constructor.
    + simpl in Hsz. destruct HT as [He [Hc [_ [Hr _]]]]. destruct HT' as [He' [Hc' [_ [Hr' _]]]].
      assert (HE := IHI e e' ltac:(lia) He He').
      destruct (cmpI n e e'); simpl in HE.
      * apply ilt_exp; auto.
      * assert (HC := IHS c c' ltac:(lia) Hc Hc').
        destruct (cmpS n c c'); simpl in HC.
        -- apply ilt_coef; auto.
        -- assert (HR := IHI r r' ltac:(lia) Hr Hr').
           destruct (cmpI n r r'); simpl in HR.
           ++ apply ilt_tail; auto.
           ++ apply ieq_cons; auto.
           ++ apply ilt_tail; auto; [ apply ieq_sym; auto | symmetry; auto ].
        -- apply ilt_coef; auto. apply ieq_sym; auto.
      * apply ilt_exp; auto.
Qed.

Definition BS_compare (x y:BSmall) : ordering := cmpS (S (BS_size x + BS_size y)) x y.

Theorem BS_compare_correct x y : BS_nf x -> BS_nf y ->
  ordering_correct (BS_compare x y) (BS_denote x) (BS_denote y).
Proof. intros Hx Hy. apply cmp_correct; auto. Qed.

Theorem BS_decide_order x y : BS_nf x -> BS_nf y ->
  {BS_denote x < BS_denote y} + {BS_denote y ≤ BS_denote x}.
Proof.
  intros Hx Hy. assert (H := BS_compare_correct x y Hx Hy).
  destruct (BS_compare x y); simpl in H; [ left; auto | right; apply H | right; apply ord_lt_le; auto ].
Defined.

(** ** Uniqueness of normal forms *)

Theorem cmp_eq n :
  (forall x y, (BS_size x + BS_size y < n)%nat -> BS_nf x -> BS_nf y -> cmpS n x y = EQ -> x = y) /\
  (forall T T', (BI_size T + BI_size T' < n)%nat -> BI_nf T -> BI_nf T' -> cmpI n T T' = EQ -> T = T').
Proof.
  induction n as [|n [IHS IHI]]; [ split; intros; lia | ].
  split.
  - intros x y Hsz Hx Hy.
    destruct x as [|T a]; destruct y as [|T' b]; [ auto | simpl; discriminate | simpl; discriminate | ].
    rewrite cmpS_BN. simpl in Hsz.
    destruct Hx as [HT [Ha _]]. destruct Hy as [HT' [Hb _]].
    destruct (cmpI n T T') eqn:EI.
    + destruct (_ && _); discriminate.
    + intro E. f_equal; [ apply IHI | apply IHS ]; auto; lia.
    + destruct (_ && _); discriminate.
  - intros T T' Hsz HT HT'.
    destruct T as [|e c r]; destruct T' as [|e' c' r']; simpl; try discriminate; auto.
    simpl in Hsz. destruct HT as [He [Hc [_ [Hr _]]]]. destruct HT' as [He' [Hc' [_ [Hr' _]]]].
    destruct (cmpI n e e') eqn:E1; try discriminate.
    destruct (cmpS n c c') eqn:E2; try discriminate.
    intro E3. f_equal; [ apply IHI | apply IHS | apply IHI ]; auto; lia.
Qed.

Theorem BS_nf_unique x y : BS_nf x -> BS_nf y -> BS_denote x ≈ BS_denote y -> x = y.
Proof.
  intros Hx Hy Heq.
  assert (H := BS_compare_correct x y Hx Hy).
  destruct (BS_compare x y) eqn:E; simpl in H.
  - elim (ord_lt_irreflexive (BS_denote x)).
    apply ord_lt_le_trans with (BS_denote y); [ exact H | apply Heq ].
  - apply (proj1 (cmp_eq (S (BS_size x + BS_size y)))); auto.
  - elim (ord_lt_irreflexive (BS_denote y)).
    apply ord_lt_le_trans with (BS_denote x); [ exact H | apply Heq ].
Qed.

(** ** Examples, by computation *)

Definition BS_one : BSmall := BN BIZ BZ.                   (* 1 *)
Definition BI_one : BIdx := BIC BIZ BS_one BIZ.            (* the index 1 *)
Definition BI_Ω : BIdx := BIC BI_one BS_one BIZ.            (* the index Ω *)
Definition BI_ΩΩ : BIdx := BIC BI_Ω BS_one BIZ.             (* the index Ω^Ω *)

(** Γ₀ = φ_Ω(0) lies below the Large Veblen Ordinal φ_{Ω^Ω}(0). *)
Example compare_Γ0_LVO : BS_compare (BN BI_Ω BZ) (BN BI_ΩΩ BZ) = LT.
Proof. reflexivity. Qed.

(** Γ₁ = φ_Ω(1) lies above Γ₀, and φ_1(0) = ω below it. *)
Example compare_Γ1 : BS_compare (BN BI_Ω BS_one) (BN BI_Ω BZ) = GT.
Proof. reflexivity. Qed.

Example compare_ω_Γ0 : BS_compare (BN BI_one BZ) (BN BI_Ω BZ) = LT.
Proof. reflexivity. Qed.

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

(** * Cantor decomposition

With base 1+x, φ_∅(y) = 1 + y and φ_{Ω^0·a}(y) = ω^a + y, while a
value whose index has a nonzero leading exponent is an ε-number:
ω^v = v.  So a normal form decomposes as a sum of powers of ω whose
exponents are again normal forms, and the generic Cantor arithmetic
applies. *)

(** ** Generic facts about Cantor sums *)

Section cantor_sums.
  Variable A : Type.
  Variable f : A -> Ord.
  Hypothesis Hf : forall x, complete (f x).

  Lemma cantor_lt_succ : forall xs a, cantor_ordered f (a :: xs) ->
    cantor_denote f (a :: xs) < expOrd ω (succOrd (f a)).
  Proof.
    induction xs as [|b xs IH]; intros a Hord; simpl in *.
    - rewrite addOrd_zero_r. apply expOrd_increasing; [ apply omega_gt1 | apply succ_lt ].
    - destruct Hord as [Hab Hord].
      apply expOmega_additively_closed; [ apply succ_complete; auto | | ].
      + apply expOrd_increasing; [ apply omega_gt1 | apply succ_lt ].
      + eapply ord_lt_le_trans; [ apply (IH b Hord) | ].
        apply expOrd_monotone. apply succ_least.
        apply ord_le_lt_trans with (f a); [ exact Hab | apply succ_lt ].
  Qed.

  Lemma cantor_lt_shift : forall xs a, cantor_ordered f xs ->
    match xs with [] => True | b :: _ => f b ≤ a end ->
    cantor_denote f xs < expOrd ω a + cantor_denote f xs.
  Proof.
    induction xs as [|b xs IH]; intros a Hord Hb; simpl in *.
    - rewrite addOrd_zero_r. apply expOrd_nonzero.
    - destruct Hord as [Hhead Hord].
      apply ord_lt_le_trans with (expOrd ω (f b) + (expOrd ω (f b) + cantor_denote f xs)).
      + apply addOrd_increasing. apply IH; auto.
      + apply addOrd_monotone; [ apply expOrd_monotone; auto | reflexivity ].
  Qed.
End cantor_sums.

(** u + (ω^b + r) = ω^b + r whenever u < ω^b. *)
Lemma lead_absorb u b r : complete b -> u < expOrd ω b -> u + (expOrd ω b + r) ≈ expOrd ω b + r.
Proof.
  intros Hb Hu. rewrite addOrd_assoc. split; [ | apply addOrd_monotone; [ apply addOrd_le2 | reflexivity ] ].
  apply addOrd_monotone; [ | reflexivity ].
  apply additively_closed_collapse; auto. apply expOmega_additively_closed; auto.
Qed.

(** ** The values of the three shapes *)

Lemma BS_denote_small a y : BS_denote (BN (BIC BIZ a BIZ) y) ≈ expOrd ω (BS_denote a) + BS_denote y.
Proof.
  transitivity (bphi (addOrd 1) (embed (BS_denote a)) (BS_denote y)).
  - apply (bphi_bequiv (addOrd 1) (normal_monotone _ onePlus_normal) _ _ _
             (exp_equiv (BIC BIZ a BIZ) a eq_refl) (BI_bfam _) (bfam_embed _)).
  - apply bphi_onePlus_embed; auto using BS_complete.
Qed.

(** A value whose index has a nonzero leading exponent is an ε-number:
    the family ξ ↦ Ω^0·ξ = ξ is reachable from Ω^e at the argument v
    itself, so φ_{Ω^0·v}(0) = ω^v lies below v. *)
Lemma BN_eps e c r y : BS_nf (BN (BIC e c r) y) -> e <> BIZ ->
  expOrd ω (BS_denote (BN (BIC e c r) y)) ≤ BS_denote (BN (BIC e c r) y).
Proof.
  intros Hx He.
  set (v := BS_denote (BN (BIC e c r) y)).
  destruct Hx as [HT [_ [_ _]]].
  assert (Hv : oinf v) by (apply BN_inf; auto; discriminate).
  assert (Hc : 0 < BS_denote c) by apply HT.
  assert (Hepos : bpos (BI_denote e)).
  { destruct e as [|e1 c1 r1]; [ tauto | ]. apply lead_pos. apply HT. }
  assert (HZ : bleZ v (bmul (bexpΩ bzero) (embed v)) (BI_denote (BIC e c r))).
  { eapply bleZ_mono_r; [ apply zlt_exp; [ apply zlt_bslt, Hepos | exact Hv ] | ].
    simpl. eapply bsub_trans; [ apply bsub_P_Pz, Hc | apply bsub_le_badd ]. }
  assert (Hfix : bphi (addOrd 1) (bmul (bexpΩ bzero) (embed v)) 0 ≤ v).
  { apply (bleZ_sound (addOrd 1) onePlus_normal v _ _ HZ (BI_denote (BIC e c r)) (bsub_refl _));
      auto using BI_good, BI_bfam.
    - apply (BS_complete (BN (BIC e c r) y)).
    - exact (bfix_value_full (addOrd 1) onePlus_normal (BI_denote (BIC e c r)) (BS_denote y)
               (BI_good _) (BI_inh e c r Hc) (BS_complete y)). }
  eapply ord_le_trans; [ | exact Hfix ].
  transitivity (bphi (addOrd 1) (embed v) 0).
  - transitivity (expOrd ω v + 0); [ apply addOrd_le1 | ].
    apply (bphi_onePlus_embed v 0 (BS_complete (BN (BIC e c r) y)) zero_complete).
  - apply (bphi_bequiv (addOrd 1) (normal_monotone _ onePlus_normal) _ _ _
             (bequiv_sym _ _ (bequiv_one_mul v)) (bfam_embed _)
             (bfam_bmul _ _ (bfam_bexpΩ _ bfam_bzero) (bfam_embed _))).
Qed.

(** ** Decomposition *)

Fixpoint BS_decompose (x:BSmall) : list BSmall :=
  match x with
  | BZ => []
  | BN BIZ y => BZ :: BS_decompose y
  | BN (BIC BIZ a BIZ) y => a :: BS_decompose y
  | _ => [x]
  end.

Definition head_le (z:Ord) (xs:list BSmall) : Prop :=
  match xs with [] => True | b :: _ => BS_denote b ≤ z end.


Theorem decompose_correct : forall x, BS_nf x ->
  each BS_nf (BS_decompose x) /\ cantor_ordered BS_denote (BS_decompose x) /\
  BS_denote x ≈ cantor_denote BS_denote (BS_decompose x).
Proof.
  induction x as [|T y IHy]; intro Hx; [ simpl; split; [ exact I | split; [ exact I | reflexivity ] ] | ].
  assert (Hx' := Hx). destruct Hx' as [HT [Hy [Hlt HK]]].
  destruct (IHy Hy) as [Hall [Hord Heq]].
  destruct T as [|[|e1 c1 r1] c r].
  - (* 1 + y *)
    simpl BS_decompose. split; [ split; [ exact I | exact Hall ] | split ].
    + split; auto.
      destruct (BS_decompose y) as [|b bs] eqn:E; auto.
      destruct b as [|Tb yb]; [ simpl; reflexivity | exfalso ].
      simpl in Heq.
      assert (Hb := BS_pos Tb yb).
      assert (Habs : 1 + (expOrd ω (BS_denote (BN Tb yb)) + cantor_denote BS_denote bs)
                     ≈ expOrd ω (BS_denote (BN Tb yb)) + cantor_denote BS_denote bs).
      { apply lead_absorb; [ apply BS_complete | ].
        apply ord_le_lt_trans with (expOrd ω 0); [ apply (proj2 (expOrd_zero ω)) | ].
        apply expOrd_increasing; auto. apply omega_gt1. }
      apply (ord_lt_irreflexive (BS_denote y)).
      eapply ord_lt_le_trans; [ exact Hlt | ].
      rewrite BS_denote_onePlus. rewrite Heq at 1. rewrite Habs. apply Heq.
    + simpl cantor_denote. rewrite BS_denote_onePlus. rewrite expOrd_zero. rewrite <- Heq. reflexivity.
  - destruct r as [|e2 c2 r2].
    + (* ω^c + y *)
      simpl BS_decompose.
      assert (Hc : BS_nf c) by apply HT.
      split; [ split; [ exact Hc | exact Hall ] | split ].
      * split; auto.
        destruct (BS_decompose y) as [|b bs] eqn:E; auto.
        destruct Hall as [Hb _].
        destruct (BS_decide_order c b Hc Hb) as [Hcb|Hbc]; auto.
        exfalso. simpl in Heq.
        assert (Habs : expOrd ω (BS_denote c) + (expOrd ω (BS_denote b) + cantor_denote BS_denote bs)
                       ≈ expOrd ω (BS_denote b) + cantor_denote BS_denote bs).
        { apply lead_absorb; [ apply BS_complete | ].
          apply expOrd_increasing; auto. apply omega_gt1. }
        apply (ord_lt_irreflexive (BS_denote y)).
        eapply ord_lt_le_trans; [ exact Hlt | ].
        rewrite BS_denote_small. rewrite Heq at 1. rewrite Habs. apply Heq.
      * simpl cantor_denote. rewrite BS_denote_small. rewrite <- Heq. reflexivity.
    + exfalso. destruct HT as [_ [_ [_ [_ Hl]]]]. inversion Hl.
  - (* an ε-number *)
    set (X := BN (BIC (BIC e1 c1 r1) c r) y).
    change (each BS_nf [X] /\ cantor_ordered BS_denote [X] /\
            BS_denote X ≈ expOrd ω (BS_denote X) + 0).
    split; [ split; [ exact Hx | exact I ] | split; [ simpl; auto | ] ].
    split.
    + transitivity (expOrd ω (BS_denote X)); [ | apply addOrd_le1 ].
      apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    + apply ord_le_trans with (expOrd ω (BS_denote X)); [ apply addOrd_zero_r | ].
      apply BN_eps; auto. discriminate.
Qed.

(** A normal form that is not an ε-number lies below its ω-power. *)
Lemma not_eps_lt x :
  BS_nf x -> match x with BZ => False | BN (BIC (BIC _ _ _) _ _) _ => False | _ => True end ->
  BS_denote x < expOrd ω (BS_denote x).
Proof.
  intros Hx Hs.
  destruct (decompose_correct x Hx) as [_ [Hord Heq]].
  destruct x as [|T y]; [ contradiction | ].
  assert (Hx' := Hx). destruct Hx' as [HT [_ [_ HK]]].
  assert (Hhead : exists h rest, BS_decompose (BN T y) = h :: rest /\
                                 BS_denote h < BS_denote (BN T y)).
  { destruct T as [|[|e1 c1 r1] c r]; [ | | contradiction ].
    - exists BZ, (BS_decompose y). split; auto. apply BS_pos.
    - destruct r as [|e2 c2 r2]; [ | destruct HT as [_ [_ [_ [_ Hl]]]]; inversion Hl ].
      exists c, (BS_decompose y). split; auto. apply HK. }
  destruct Hhead as [h [rest [E Hh]]]. rewrite E in Hord, Heq.
  eapply ord_le_lt_trans; [ apply Heq | ].
  eapply ord_lt_le_trans; [ apply (cantor_lt_succ BSmall BS_denote BS_complete rest h Hord) | ].
  apply expOrd_monotone, succ_least; auto.
Qed.

(** ** Recomposition *)

Fixpoint BS_recompose (xs:list BSmall) : BSmall :=
  match xs with
  | [] => BZ
  | e :: xs' =>
      match e with
      | BZ => BN BIZ (BS_recompose xs')
      | BN (BIC (BIC _ _ _) _ _) _ =>
          match xs' with
          | [] => e
          | _ :: _ => BN (BIC BIZ e BIZ) (BS_recompose xs')
          end
      | _ => BN (BIC BIZ e BIZ) (BS_recompose xs')
      end
  end.

Lemma small_nf e r : BS_nf e -> 0 < BS_denote e -> BS_nf r ->
  BS_denote r < expOrd ω (BS_denote e) + BS_denote r ->
  BS_denote e < expOrd ω (BS_denote e) + BS_denote r ->
  BS_nf (BN (BIC BIZ e BIZ) r).
Proof.
  intros He He0 Hr H1 H2.
  split; [ simpl; auto | split; [ auto | split ] ].
  - eapply ord_lt_le_trans; [ exact H1 | apply BS_denote_small ].
  - simpl. split; auto. split; auto.
    eapply ord_lt_le_trans; [ exact H2 | apply BS_denote_small ].
Qed.

Theorem recompose_correct : forall xs, each BS_nf xs -> cantor_ordered BS_denote xs ->
  BS_nf (BS_recompose xs) /\ cantor_denote BS_denote xs ≈ BS_denote (BS_recompose xs).
Proof.
  induction xs as [|e xs IH]; [ simpl; split; [ exact I | reflexivity ] | ].
  intros [He Hall] [Hhead Hord].
  destruct (IH Hall Hord) as [Hr Heq].
  assert (Hshift := cantor_lt_shift BSmall BS_denote xs (BS_denote e) Hord Hhead).
  assert (Hshift' : BS_denote (BS_recompose xs) < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs)).
  { rewrite <- Heq. exact Hshift. }
  (* the general case Ω^0·e *)
  assert (Hgen : 0 < BS_denote e -> BS_denote e < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs) ->
                 BS_nf (BN (BIC BIZ e BIZ) (BS_recompose xs)) /\
                 cantor_denote BS_denote (e :: xs) ≈ BS_denote (BN (BIC BIZ e BIZ) (BS_recompose xs))).
  { intros He0 Hlt. split; [ apply small_nf; auto | ].
    simpl cantor_denote. rewrite BS_denote_small. rewrite Heq. reflexivity. }
  (* when the tail is nonempty, e lies below ω^e + rest *)
  assert (Hne : xs <> [] -> BS_denote e < expOrd ω (BS_denote e) + BS_denote (BS_recompose xs)).
  { intro Hxs. destruct xs as [|b bs]; [ tauto | ].
    apply ord_le_lt_trans with (expOrd ω (BS_denote e) + 0).
    - rewrite addOrd_zero_r. apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    - apply addOrd_increasing. rewrite <- Heq. simpl.
      eapply ord_lt_le_trans; [ apply expOrd_nonzero | apply addOrd_le1 ]. }
  destruct e as [|T y].
  - (* 1 + rest *)
    simpl BS_recompose. split.
    + split; [ exact I | split; [ auto | split; [ | exact I ] ] ].
      eapply ord_lt_le_trans; [ exact Hshift' | ].
      rewrite BS_denote_onePlus. rewrite expOrd_zero. reflexivity.
    + simpl cantor_denote. rewrite BS_denote_onePlus. rewrite expOrd_zero. rewrite Heq. reflexivity.
  - destruct xs as [|b bs].
    + destruct T as [|[|e1 c1 r1] c r].
      * apply Hgen; [ apply BS_pos | ].
        apply ord_lt_le_trans with (expOrd ω (BS_denote (BN BIZ y))); [ | apply addOrd_le1 ].
        apply not_eps_lt; auto.
      * apply Hgen; [ apply BS_pos | ].
        apply ord_lt_le_trans with (expOrd ω (BS_denote (BN (BIC BIZ c r) y))); [ | apply addOrd_le1 ].
        apply not_eps_lt; auto.
      * set (X := BN (BIC (BIC e1 c1 r1) c r) y).
        change (BS_nf X /\ expOrd ω (BS_denote X) + 0 ≈ BS_denote X).
        split; auto. split.
        -- apply ord_le_trans with (expOrd ω (BS_denote X)); [ apply addOrd_zero_r | ].
           apply BN_eps; auto. discriminate.
        -- transitivity (expOrd ω (BS_denote X)); [ | apply addOrd_le1 ].
           apply (normal_inflationary powOmega powOmega_normal), BS_complete.
    + destruct T as [|[|e1 c1 r1] c r];
        (apply Hgen; [ apply BS_pos | apply Hne; discriminate ]).
Qed.

(** ** The Cantor decomposition and the derived arithmetic *)

Definition BS_has_cantor_decomposition : has_cantor_decomposition BS_denote BS_nf :=
  {| cantor_decomp_compare := BS_compare
   ; cantor_decompose := BS_decompose
   ; cantor_recompose := BS_recompose
   ; cantor_decomp_complete := BS_complete
   ; cantor_decomp_compare_correct := BS_compare_correct
   ; cantor_decompose_correct := decompose_correct
   ; cantor_recompose_correct := recompose_correct
   |}.

Definition BS_succ := cantor_succ BS_has_cantor_decomposition.
Definition BS_add  := cantor_add BS_has_cantor_decomposition.
Definition BS_mul  := cantor_mul BS_has_cantor_decomposition.
Definition BS_exp  := cantor_exp BS_has_cantor_decomposition.
Definition BS_nadd := cantor_nadd BS_has_cantor_decomposition.

Theorem BS_succ_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD) succOrd BS_succ.
Proof. apply cantor_succ_reflects. Qed.

Theorem BS_add_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) addOrd BS_add.
Proof. apply cantor_add_reflects. Qed.

Theorem BS_mul_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) mulOrd BS_mul.
Proof. apply cantor_mul_reflects. Qed.

Theorem BS_exp_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) expOrd BS_exp.
Proof. apply cantor_exp_reflects. Qed.

Theorem BS_nadd_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) naddOrd BS_nadd.
Proof. apply cantor_nadd_reflects. Qed.

(** * The upper bound: every normal form lies below the Bachmann–Howard ordinal

At the base 1+x the Bachmann–Howard ordinal is BHO₁ = φ_{ε_{Ω+1}}(0).
Every normal index is reachable below some level Ω+1, Ω^(Ω+1), … of the
tower whose limit is ε_{Ω+1}, relative to any infinite z above its
coefficients; this is part (B) of @nest@ applied along leading
exponents.  Since BHO₁ is a common fixpoint of the components of
ε_{Ω+1}, it is a fixpoint of every φ_T, and the bound follows by
induction on notations. *)

Definition BHO1 : Ord := bphi (addOrd 1) bεΩ1 0.

Lemma bεΩ1_inh : inhabited (bsmall bεΩ1 + bbig bεΩ1).
Proof. exact (inhabits (inl 0%nat)). Qed.

Lemma bεΩ1_good : bfam bεΩ1 /\ bgood (addOrd 1) bεΩ1.
Proof. apply (bcanon_good (addOrd 1) onePlus_normal); [ apply bcanon_bεΩ1 | apply bdec_bεΩ1 ]. Qed.

Lemma BHO1_complete : complete BHO1.
Proof. apply bphi_complete; [ apply onePlus_normal | apply bεΩ1_good | apply zero_complete ]. Qed.

Lemma BHO1_inf : oinf BHO1.
Proof.
  apply (bphi_value_inf (addOrd 1) onePlus_normal); auto using zero_complete, bεΩ1_inh.
  - intro; apply addOrd_le2.
  - intros; reflexivity.
  - apply bεΩ1_good.
Qed.

(** Every normal index is z-reachably below some level of the tower. *)
Lemma idx_height z : oinf z -> forall T, BI_nf T -> Klt z T -> exists n, zlt z (BI_denote T) (btower n).
Proof.
  intros Hz T. induction T as [|e IHe c r IHr]; intros HT HK.
  - exists 0%nat. apply zlt_bslt. change (bslt bzero (bsucc bOmega)).
    apply (bslt_small bzero (bsucc bOmega) tt), bsub_bzero_l.
  - destruct (IHe (proj1 HT) (proj1 HK)) as [m Hm].
    exists (S m).
    exact (proj2 (nest z Hz (S (BI_size (BIC e c r))) (BIC e c r) ltac:(lia) HT HK) (btower m) Hm).
Qed.

Lemma zlt_tower_top z x n : zlt z x (btower n) -> zlt z x bεΩ1.
Proof.
  intros [D [H1 H2]]. exists D. split; auto.
  apply (LZ_small z D bεΩ1 (n : bsmall bεΩ1)). exact H2.
Qed.

(** BHO₁ is a fixpoint of φ_T for every normal index whose coefficients lie below it. *)
Lemma BHO1_fix T : BI_nf T -> Klt BHO1 T -> bphi (addOrd 1) (BI_denote T) BHO1 ≤ BHO1.
Proof.
  intros HT HK.
  destruct (idx_height BHO1 BHO1_inf T HT HK) as [n Hn].
  apply (zlt_value (addOrd 1) onePlus_normal (BI_denote T) bεΩ1 0); auto using zero_complete, bεΩ1_inh.
  - apply (zlt_tower_top _ _ n Hn).
  - apply bεΩ1_good.
  - apply bεΩ1_good.
Qed.

Theorem BNotation_bounded :
  (forall x, BS_nf x -> BS_denote x < BHO1) /\ (forall T, BI_nf T -> Klt BHO1 T).
Proof.
  apply BNotation_mut.
  - intros _. apply (bphi_nonzero (addOrd 1) onePlus_normal).
  - intros T IHT y IHy [HT [Hy _]].
    eapply ord_lt_le_trans; [ | apply (BHO1_fix T HT (IHT HT)) ].
    apply normal_increasing; auto using BI_normal, BHO1_complete.
  - intros _. exact I.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]]. simpl. auto.
Qed.

(** Every normal form denotes an ordinal below the Bachmann–Howard
    ordinal (at the base 1+x). *)
Corollary BS_bounded x : BS_nf x -> BS_denote x < BHO1.
Proof. apply BNotation_bounded. Qed.

(** * Dominance: coefficients lie at or below φ_T(0)

Every coefficient k of a normal index T, at any depth, sits in a
strict context C with C k ⊑ ⟦T⟧ (@bctx@): the hole runs through the
right summand of an addition, the coefficient of Ω^e·_, or an
exponent.  So k ≤ φ_{C k}(0) ≤ φ_T(0).  Equality can occur, e.g.
φ_{Ω^d}(0) = d for d the Large Veblen Ordinal. *)

Lemma idx_term_bcd e c : bcd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))).
Proof. apply (proj1 (idx_ok_term _ _ (BI_ok e) (BS_complete c))). Qed.

(** All coefficients, at any depth, are positive. *)
Fixpoint BI_pos (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => BI_pos e /\ 0 < BS_denote c /\ BI_pos r
  end.

Lemma BI_nf_pos T : BI_nf T -> BI_pos T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [_ [Hc [Hr _]]]]. auto.
Qed.

Lemma Kge_ctx : forall T, BI_pos T -> forall z, Kge z T ->
  exists C ζ, bctx C /\ complete ζ /\ z ≤ ζ /\ bsub (C ζ) (BI_denote T).
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [He [Hc0 Hr]] z [Hz|[Hz|Hz]].
  - destruct (IHe He z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
    exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
    eapply bsub_trans; [ apply bsub_bexpΩ, Hsub | ].
    eapply bsub_trans; [ apply bsub_P_Pz, Hc0 | apply bsub_le_badd ].
  - exists (fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ)), (BS_denote c).
    split; [ | split; [ apply BS_complete | split; [ auto | apply bsub_le_badd ] ] ].
    apply bctx_mul; [ apply bcd_bexpΩ, BI_ok | apply bpos_bexpΩ | apply bctx_embed ].
  - destruct (IHr Hr z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
    exists (fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ)), ζ.
    split; [ apply bctx_add; [ apply idx_term_bcd | auto ] | split; [ auto | split; [ auto | ] ] ].
    apply bsub_badd_r; auto.
Qed.

Theorem dominance T y z : BI_pos T -> Kge z T -> z ≤ BS_denote (BN T y).
Proof.
  intros HT Hz.
  destruct (Kge_ctx T HT z Hz) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
  transitivity ζ; auto.
  transitivity (bphi (addOrd 1) (C ζ) 0); [ apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ) | ].
  transitivity (bphi (addOrd 1) (BI_denote T) 0).
  - apply (proj2 (bphi_mono_index (addOrd 1) (normal_monotone _ onePlus_normal) _ (BI_bfam T))); auto.
  - simpl. apply normal_monotone; auto using BI_normal, zero_least.
Qed.

(** * Normalization by rewriting

Terms are required to be proper: indices are Ω-Cantor normal forms
(exponents strictly decreasing, coefficients positive), hereditarily.
As with @SchutteMatrix@'s properness, this is a precondition rather
than something to rewrite: with tree semantics, an index such as
Ω^0·c + Ω does not denote the same hierarchy as Ω, so absorption of
summands is not sound.  On proper terms there are two redexes, both
collapsing φ_T(y) to a proper subterm:

 - the argument is a fixpoint: φ_T(y) ≤ y, so φ_T(y) = y;
 - a coefficient k of T dominates: φ_T(y) ≤ k, so (by @dominance@)
   φ_T(y) = k.

Every reduction step strictly decreases size, so the system is
strongly normalizing, and its normal forms are exactly @BS_nf@. *)

(** ** Proper terms *)

Fixpoint BS_proper (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y => BI_proper T /\ BS_proper y
  end
with BI_proper (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => BI_proper e /\ BS_proper c /\ 0 < BS_denote c /\ BI_proper r /\ lead_below r e
  end.

Lemma BI_proper_pos T : BI_proper T -> BI_pos T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [_ [Hc [Hr _]]]]. auto.
Qed.

Lemma nf_proper : (forall x, BS_nf x -> BS_proper x) /\ (forall T, BI_nf T -> BI_proper T).
Proof.
  apply BNotation_mut; simpl; auto.
  - intros T IHT y IHy [HT [Hy _]]. auto.
  - intros e IHe c IHc r IHr [He [Hc [Hc0 [Hr Hl]]]]. auto 10.
Qed.

(** Coefficient occurrences, at any depth. *)
Fixpoint Kin (k:BSmall) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC e c r => Kin k e \/ k = c \/ Kin k r
  end.

Lemma Kin_Kge k T : Kin k T -> Kge (BS_denote k) T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]]; [ left; auto | subst; right; left; reflexivity | right; right; auto ].
Qed.

Lemma Kin_proper k T : Kin k T -> BI_proper T -> BS_proper k.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [He [Hc [_ [Hr _]]]]; [ auto | subst; auto | auto ].
Qed.

Lemma Kin_size k T : Kin k T -> (BS_size k < BI_size T)%nat.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]]; [ specialize (IHe H) | subst | specialize (IHr H) ]; lia.
Qed.

(** ** The index equivalence *)

Lemma ieq_refl T : ieq T T.
Proof. induction T as [|e IHe c r IHr]; constructor; auto. reflexivity. Qed.

Lemma ieq_trans a b c : ieq a b -> ieq b c -> ieq a c.
Proof.
  intro H. revert c. induction H as [|e x r e' x' r' He IHe Hx Hr IHr]; intros c Hbc; inversion Hbc; subst; constructor; auto.
  transitivity (BS_denote x'); auto.
Qed.

Lemma ilt_ieq : forall a b, ilt a b -> forall a' b', ieq a a' -> ieq b b' -> ilt a' b'.
Proof.
  intros a b H. induction H as [e c r | e c r e' c' r' Hee IH | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr IH];
    intros a' b' Ha Hb.
  - inversion Ha; inversion Hb; subst. constructor.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_exp. apply IH; auto.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_coef.
    + apply ieq_trans with e; [ apply ieq_sym; exact He1 | apply ieq_trans with e'; auto ].
    + rewrite <- Hc1, <- Hc2. auto.
  - inversion Ha as [|? ? ? e1 c1 r1 He1 Hc1 Hr1]; inversion Hb as [|? ? ? e2 c2 r2 He2 Hc2 Hr2]; subst.
    apply ilt_tail.
    + apply ieq_trans with e; [ apply ieq_sym; exact He1 | apply ieq_trans with e'; auto ].
    + rewrite <- Hc1, <- Hc2. auto.
    + apply IH; auto.
Qed.

(** ** The rewrite relation *)

Inductive redex : BSmall -> BSmall -> Prop :=
| redex_arg : forall T y, BS_denote (BN T y) ≤ BS_denote y -> redex (BN T y) y
| redex_coef : forall T y k, Kin k T -> BS_denote (BN T y) ≤ BS_denote k -> redex (BN T y) k.

Inductive red_S : BSmall -> BSmall -> Prop :=
| red_top : forall x x', redex x x' -> red_S x x'
| red_idx : forall T T' y, red_I T T' -> red_S (BN T y) (BN T' y)
| red_arg : forall T y y', red_S y y' -> red_S (BN T y) (BN T y')
with red_I : BIdx -> BIdx -> Prop :=
| red_exp : forall e e' c r, red_I e e' -> red_I (BIC e c r) (BIC e' c r)
| red_coef : forall e c c' r, red_S c c' -> red_I (BIC e c r) (BIC e c' r)
| red_rest : forall e c r r', red_I r r' -> red_I (BIC e c r) (BIC e c r').

Scheme red_S_mut := Induction for red_S Sort Prop
with red_I_mut := Induction for red_I Sort Prop.
Combined Scheme red_mut from red_S_mut, red_I_mut.

Lemma redex_sound x x' : redex x x' -> BS_proper x -> BS_denote x ≈ BS_denote x'.
Proof.
  intros H Hx. destruct H as [T y H | T y k Hk H]; split; auto.
  - apply normal_inflationary; auto using BI_normal, BS_complete.
  - destruct Hx as [HT _]. apply dominance; auto using BI_proper_pos, Kin_Kge.
Qed.

Theorem red_sound :
  (forall x x', red_S x x' -> BS_proper x -> BS_denote x ≈ BS_denote x') /\
  (forall T T', red_I T T' -> BI_proper T -> ieq T T').
Proof.
  apply red_mut.
  - intros x x' H Hx. apply redex_sound; auto.
  - intros T T' y H IH [HT _]. apply bphi_ieq; auto.
  - intros T y y' H IH [_ Hy]. apply ord_eq_normal; auto using BI_normal.
  - intros e e' c r H IH [He _]. constructor; auto using ieq_refl. reflexivity.
  - intros e c c' r H IH [_ [Hc _]]. constructor; auto using ieq_refl.
  - intros e c r r' H IH [_ [_ [_ [Hr _]]]]. constructor; auto using ieq_refl. reflexivity.
Qed.

Lemma lead_below_ieq r r' e e' : ieq r r' -> ieq e e' -> lead_below r e -> lead_below r' e'.
Proof.
  intros Hr He. destruct Hr as [|e2 c2 r2 e2' c2' r2' He2 _ _]; simpl; auto.
  intro H. apply (ilt_ieq _ _ H); auto.
Qed.

Theorem red_proper :
  (forall x x', red_S x x' -> BS_proper x -> BS_proper x') /\
  (forall T T', red_I T T' -> BI_proper T -> BI_proper T').
Proof.
  apply red_mut.
  - intros x x' H Hx. destruct H as [T y H | T y k Hk H]; [ apply Hx | ].
    apply (Kin_proper k T); auto. apply Hx.
  - intros T T' y H IH [HT Hy]. split; auto.
  - intros T y y' H IH [HT Hy]. split; auto.
  - intros e e' c r H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hee := proj2 red_sound e e' H He).
    split; auto. split; auto. split; auto. split; auto.
    apply (lead_below_ieq r r e e'); auto using ieq_refl.
  - intros e c c' r H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hcc := proj1 red_sound c c' H Hc).
    split; auto. split; auto. split; [ rewrite <- Hcc; auto | auto ].
  - intros e c r r' H IH [He [Hc [Hc0 [Hr Hl]]]].
    assert (Hrr := proj2 red_sound r r' H Hr).
    split; auto. split; auto. split; auto. split; auto.
    apply (lead_below_ieq r r' e e); auto using ieq_refl.
Qed.

(** ** Strong normalization *)

Theorem red_size :
  (forall x x', red_S x x' -> (BS_size x' < BS_size x)%nat) /\
  (forall T T', red_I T T' -> (BI_size T' < BI_size T)%nat).
Proof.
  apply red_mut; simpl; intros; try lia.
  destruct r as [T y H | T y k Hk H]; simpl; [ lia | ].
  pose proof (Kin_size k T Hk). lia.
Qed.

Theorem strongly_normalizing : well_founded (fun y x => red_S x y).
Proof.
  apply (Wf_nat.well_founded_lt_compat _ BS_size).
  intros y x H. apply (proj1 red_size); auto.
Qed.

(** ** Deciding the argument redex *)

Lemma Klt_mono z z' T : z ≤ z' -> Klt z T -> Klt z' T.
Proof.
  intro Hz. induction T as [|e IHe c r IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. eapply ord_lt_le_trans; eauto.
Qed.

(** Bachmann's rule, needing only the indices to be normal. *)
Lemma nest_lt_idx T a T' b :
  BI_nf T -> BI_nf T' -> ilt T T' ->
  BS_denote a < BS_denote (BN T' b) -> Klt (BS_denote (BN T' b)) T ->
  BS_denote (BN T a) < BS_denote (BN T' b).
Proof.
  intros HT HT' Hlt Ha Hc.
  set (z := BS_denote (BN T' b)) in *.
  assert (Hne : T' <> BIZ) by (intro E; subst; inversion Hlt).
  assert (Hz : zlt z (BI_denote T) (BI_denote T')).
  { apply (proj1 (nest z (BN_inf T' b HT' Hne) (S (BI_size T)) T ltac:(lia) HT Hc)); auto. }
  assert (Hi : inhabited (bsmall (BI_denote T') + bbig (BI_denote T'))).
  { destruct T' as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HT'. }
  assert (Hfix := zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b)
                    Hz (BI_good T') (BI_bfam T') Hi (BS_complete b)).
  eapply ord_lt_le_trans; [ | exact Hfix ].
  apply normal_increasing; auto using BI_normal.
  apply (BS_complete (BN T' b)).
Qed.

(** y is a fixpoint of φ_T iff y = φ_{T''}(y'') with T < T'' and every
    coefficient of T below y. *)
Definition fix_test (n:nat) (T:BIdx) (y:BSmall) : bool :=
  match y with
  | BZ => false
  | BN T'' _ => match cmpI n T T'' with LT => coefs_below n T y | _ => false end
  end.

Theorem fix_test_correct T y : BI_nf T -> BS_nf y ->
  let n := S (BI_size T + BS_size y) in
  (fix_test n T y = true -> BS_denote (BN T y) ≤ BS_denote y) /\
  (fix_test n T y = false -> BS_denote y < BS_denote (BN T y)).
Proof.
  intros HT Hy n.
  destruct y as [|T'' y'']; [ split; [ discriminate | intros _; apply (BS_pos T BZ) ] | ].
  change (fix_test n T (BN T'' y'')) with
    (match cmpI n T T'' with LT => coefs_below n T (BN T'' y'') | _ => false end).
  assert (Hy' := Hy). destruct Hy' as [HT'' [Hy'' [Hlt'' HK'']]].
  assert (HI := proj2 (cmp_correct n) T T'' ltac:(unfold n; simpl; lia) HT HT'').
  set (y := BN T'' y'') in *.
  assert (Hyinf : T'' <> BIZ -> oinf (BS_denote y)) by (intro; apply BN_inf; auto).
  destruct (cmpI n T T'') eqn:E; simpl in HI.
  - destruct (coefs_below_spec n y T (fun c Hc Hcn => proj1 (cmp_correct n) c y ltac:(unfold n; lia) Hcn Hy) HT)
      as [C1 C2].
    destruct (coefs_below n T y) eqn:E2; split; intro H; try discriminate.
    + (* a fixpoint *)
      assert (HK := C1 eq_refl).
      assert (Hne : T'' <> BIZ) by (intro Ez; subst; inversion HI).
      assert (Hz : zlt (BS_denote y) (BI_denote T) (BI_denote T'')).
      { apply (proj1 (nest _ (Hyinf Hne) (S (BI_size T)) T ltac:(lia) HT HK)); auto. }
      assert (Hi : inhabited (bsmall (BI_denote T'') + bbig (BI_denote T''))).
      { destruct T'' as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HT''. }
      exact (zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T'') (BS_denote y'')
               Hz (BI_good T'') (BI_bfam T'') Hi (BS_complete y'')).
    + (* a coefficient at least y: y ≤ φ_T(0) < φ_T(y) *)
      apply ord_le_lt_trans with (BS_denote (BN T BZ)).
      * apply dominance; [ apply BI_nf_pos; auto | apply C2; reflexivity ].
      * apply (normal_increasing _ (BI_normal T) 0 (BS_denote y) (BS_complete y) (BS_pos T'' y'')).
  - split; intro H; try discriminate.
    change (BS_denote y < bphi (addOrd 1) (BI_denote T) (BS_denote y)).
    rewrite (bphi_ieq T T'' (BS_denote y) HI).
    apply normal_increasing; auto using BI_normal, BS_complete.
  - split; intro H; try discriminate.
    apply nest_lt_idx; auto.
    + eapply ord_lt_le_trans; [ exact Hlt'' | ].
      apply normal_inflationary; auto using BI_normal, BS_complete.
    + apply Klt_mono with (BS_denote y); auto.
      apply normal_inflationary; auto using BI_normal, BS_complete.
Qed.

(** ** The coefficient redex: collapse at the end position

φ_T(0) collapses to its largest coefficient m exactly when T lies
below the index of m and m occurs only at the end of T (the coefficient
of the last summand, or, when that coefficient is 1, the end of its
exponent).  For collapse, a non-strict variant of @nest@ makes ⟦T⟧
m-reachable from the index of m; otherwise a strict context below ⟦T⟧
carries m (@Kgs_ctx@). *)

(** Every coefficient is below z, except an end occurrence, which is at most z. *)
Fixpoint Kend (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r =>
      match r with
      | BIZ => (Klt z e /\ BS_denote c ≤ z) \/ (Kend z e /\ BS_denote c ≈ 1)
      | _ => Klt z e /\ BS_denote c < z /\ Kend z r
      end
  end.

Lemma Klt_ieq z T T' : ieq T T' -> Klt z T' -> Klt z T.
Proof.
  intro H. induction H as [|e c r e' c' r' He IHe Hc Hr IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. rewrite Hc; auto.
Qed.

Lemma bleZ_bsub_l z x' x y : bsub x' x -> bleZ z x y -> bleZ z x' y.
Proof. intros H1 H2. eapply bleZ_trans; [ apply LZ_sub, H1 | exact H2 ]. Qed.

Lemma bsub_badd_zero x : bsub (badd x bzero) x.
Proof. apply bequiv_badd_zero_r. Qed.

Lemma lead_pos_bs e c r : BI_nf (BIC e c r) -> bpos (BI_denote (BIC e c r)).
Proof. intro H. apply lead_pos. apply H. Qed.

Lemma BI_denote_cons e c r :
  BI_denote (BIC e c r) = badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r).
Proof. reflexivity. Qed.

(** The target's coefficients only need to satisfy @Kend@. *)
Lemma Klt_Kend z T : Klt z T -> Kend z T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; auto.
  intros [He [Hc Hr]]. destruct r as [|e2 c2 r2].
  - left. split; auto. apply ord_lt_le; auto.
  - split; auto.
Qed.

Lemma Kend_exp z e c r : oinf z -> Kend z (BIC e c r) -> Kend z e.
Proof.
  intros Hz H. destruct r as [|e2 c2 r2]; simpl in H.
  - destruct H as [[H _]|[H _]]; auto. apply Klt_Kend; auto.
  - apply Klt_Kend, H.
Qed.

Lemma Kend_coef z e' c' r' c : Kend z (BIC e' c' r') -> BS_denote c < BS_denote c' -> 0 < BS_denote c ->
  Klt z e' /\ BS_denote c < z.
Proof.
  intros H Hcc Hc0. destruct r' as [|e2 c2 r2]; simpl in H.
  - destruct H as [[H1 H2]|[H1 H2]].
    + split; auto. eapply ord_lt_le_trans; eauto.
    + exfalso. assert (H1' : BS_denote c < 1) by (eapply ord_lt_le_trans; [ exact Hcc | apply H2 ]).
      rewrite ord_lt_unfold in H1'. destruct H1' as [u Hle].
      apply (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hc0 | exact Hle ].
  - destruct H as [H1 [H2 _]]. split; auto. eapply ord_lt_trans; eauto.
Qed.

Lemma Kend_tail z e' c' r' : r' <> BIZ -> Kend z (BIC e' c' r') -> Kend z r'.
Proof. intros Hne H. destruct r' as [|e2 c2 r2]; [ tauto | ]. apply H. Qed.

Theorem nest_le z : oinf z -> forall n T, (BI_size T < n)%nat -> BI_nf T -> Kend z T ->
  (forall T', BI_nf T' -> Kend z T' -> ilt T T' -> bleZ z (BI_denote T) (BI_denote T')) /\
  (forall a, match T with
             | BIZ => True
             | BIC e _ _ => (Klt z e -> zlt z (BI_denote e) a) /\ (Kend z e -> bleZ z (BI_denote e) a)
             end -> bleZ z (BI_denote T) (bexpΩ a)).
Proof.
  intros Hz n. induction n as [|n IH]; intros T Hsz HT HK; [ lia | ].
  (* the reduction of a tail to its exponent *)
  assert (Tail : forall e r, (BI_size r < n)%nat -> BI_nf r -> Kend z r -> lead_below r e ->
                 BI_nf e -> Klt z e -> (BI_size e < n)%nat ->
                 bleZ z (BI_denote r) (bexpΩ (BI_denote e))).
  { intros e r Hr Hrn HrK Hl He HeK Hes.
    apply (proj2 (IH r Hr Hrn HrK)).
    destruct r as [|e2 c2 r2]; auto.
    simpl in Hl. destruct Hrn as [He2 _]. simpl in Hr.
    split.
    - intro HK2. apply (proj1 (nest z Hz (S (BI_size e2)) e2 ltac:(lia) He2 HK2)); auto.
    - intro HK2. apply (proj1 (IH e2 ltac:(lia) He2 HK2)); auto. apply Klt_Kend; auto. }
  assert (B : forall a, match T with
                        | BIZ => True
                        | BIC e _ _ => (Klt z e -> zlt z (BI_denote e) a) /\ (Kend z e -> bleZ z (BI_denote e) a)
                        end -> bleZ z (BI_denote T) (bexpΩ a)).
  { intros a Ha. destruct T as [|e c r].
    - apply LZ_sub, bsub_bzero_l.
    - destruct Ha as [Ha1 Ha2]. simpl in Hsz.
      destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
      destruct r as [|e2 c2 r2].
      + simpl in HK. destruct HK as [[HKe Hcz]|[HKe Hc1]].
        * apply bleZ_bsub_l with (bmul (bexpΩ (BI_denote e)) (embed z)); [ | apply zlt_exp; auto ].
          eapply bsub_trans; [ apply bsub_badd_zero | ]. apply bsub_bmul_r, bsub_embed; auto.
        * apply bleZ_bsub_l with (bexpΩ (BI_denote e)); [ | apply bleZ_exp; auto ].
          eapply bsub_trans; [ apply bsub_badd_zero | ].
          eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, (proj1 Hc1) | apply bsub_bmul_one ].
      + simpl in HK. destruct HK as [HKe [Hcz HKr]].
        assert (Hrb := Tail e (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr Hl He HKe ltac:(lia)).
        apply bleZ_trans with (bmul (bexpΩ (BI_denote e)) (embed z)); [ | apply zlt_exp; auto ].
        rewrite BI_denote_cons. eapply bleZ_mono_r; [ apply bleZ_shift, Hrb | ].
        eapply bsub_trans; [ apply bsub_mul_succ | apply bsub_bmul_r, bsub_embed, succ_least; auto ]. }
  split; auto.
  intros T' HT' HKT' Hlt.
  destruct Hlt as [e' c' r' | e c r e' c' r' Hee | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr].
  - apply LZ_sub, bsub_bzero_l.
  - simpl in Hsz. assert (HKe' := Kend_exp _ _ _ _ Hz HKT'). destruct HT' as [He' [_ [Hc0' _]]].
    assert (HTe := proj1 HT).
    eapply bleZ_mono_r; [ apply (B (BI_denote e')) | ].
    + split.
      * intro HKe. apply (proj1 (nest z Hz (S (BI_size e)) e ltac:(lia) HTe HKe)); auto.
      * intro HKe. apply (proj1 (IH e ltac:(lia) HTe HKe)); auto.
    + rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_P_Pz, Hc0' | apply bsub_le_badd ].
  - simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
    destruct (Kend_coef _ _ _ _ _ HKT' Hcc Hc0) as [HKe' Hcz].
    assert (HKe := Klt_ieq z e e' Hee HKe').
    assert (Hsub : bsub (bmul (bexpΩ (BI_denote e)) (embed (succOrd (BS_denote c))))
                        (BI_denote (BIC e' c' r'))).
    { rewrite BI_denote_cons. eapply bsub_trans; [ | apply bsub_le_badd ].
      eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, succ_least, Hcc | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee). }
    destruct r as [|e2 c2 r2].
    + apply LZ_sub. eapply bsub_trans; [ | exact Hsub ].
      rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_badd_zero | ].
      apply bsub_bmul_r, bsub_embed, ord_lt_le, succ_lt.
    + simpl in HK. destruct HK as [_ [_ HKr]].
      assert (Hrb := Tail e (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr Hl He HKe ltac:(lia)).
      rewrite BI_denote_cons. eapply bleZ_mono_r; [ apply bleZ_shift, Hrb | ].
      eapply bsub_trans; [ apply bsub_mul_succ | exact Hsub ].
  - simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]]. destruct HT' as [_ [_ [_ [Hr' _]]]].
    assert (Hne' : r' <> BIZ) by (intro E; subst r'; inversion Hrr).
    assert (HKr' := Kend_tail _ _ _ _ Hne' HKT').
    assert (Hterm : bsub (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                         (bmul (bexpΩ (BI_denote e')) (embed (BS_denote c')))).
    { eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed, (proj1 Hcc) | ].
      apply bsub_bmul_l, bsub_bexpΩ, (ieq_bequiv _ _ Hee). }
    destruct r as [|e2 c2 r2].
    + apply LZ_sub. rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_badd_zero | ].
      eapply bsub_trans; [ exact Hterm | apply bsub_le_badd ].
    + simpl in HK. destruct HK as [_ [_ HKr]].
      rewrite BI_denote_cons.
      apply (bleZ_mono_r z _ (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r'))).
      * apply bleZ_shift. apply (proj1 (IH (BIC e2 c2 r2) ltac:(simpl in *; lia) Hr HKr)); auto.
      * exact (bsub_badd_l _ _ Hterm (BI_denote r')).
Qed.

(** A coefficient at least z at a position that is not the end. *)
Fixpoint Kgs (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC e c r =>
      match r with
      | BIZ => (Kge z e /\ 1 < BS_denote c) \/ (BS_denote c ≈ 1 /\ Kgs z e)
      | _ => Kge z e \/ z ≤ BS_denote c \/ Kgs z r
      end
  end.

Lemma bslt_P_Pc P c : bpos P -> 1 < c -> bslt P (bmul P (embed c)).
Proof.
  intros HP Hc. destruct c as [C k].
  rewrite ord_lt_unfold in Hc. destruct Hc as [j Hj].
  assert (Hj0 : 0 < k j) by (apply ord_lt_le_trans with 1; [ apply succ_lt | exact Hj ]).
  apply bslt_bsub_l with (bmul P (embed (k j))); [ apply bsub_P_Pz; auto | ].
  apply bslt_bsub_r with (badd (bmul P (embed (k j))) P); [ | apply (bsub_bmul_step P (embed (ord C k)) j) ].
  apply (bslt_badd_pos _ bzero); auto.
Qed.

Lemma Kgs_ctx : forall T, BI_pos T -> forall z, Kgs z T ->
  exists C ζ, bctx C /\ complete ζ /\ z ≤ ζ /\ bslt (C ζ) (BI_denote T).
Proof.
  induction T as [|e IHe c r IHr]; [ simpl; tauto | ].
  intros [He [Hc0 Hr]] z HK.
  assert (Hterm : bcd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))) by apply idx_term_bcd.
  destruct r as [|e2 c2 r2].
  - destruct HK as [[HKe Hc1]|[Hc1 HKe]].
    + destruct (Kge_ctx e He z HKe) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply bslt_bsub_l with (bexpΩ (BI_denote e)); [ apply bsub_bexpΩ; auto | ].
      rewrite BI_denote_cons. apply bslt_bsub_r with (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))).
      * apply bslt_P_Pc; auto. apply bpos_bexpΩ.
      * apply bsub_le_badd.
    + destruct (IHe He z HKe) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply bslt_bsub_r with (bexpΩ (BI_denote e)); [ apply bslt_bexpΩ; auto | ].
      rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_P_Pz, Hc0 | apply bsub_le_badd ].
  - assert (Hrpos : bpos (BI_denote (BIC e2 c2 r2))) by (apply lead_pos; apply Hr).
    assert (Htail : forall X, bsub X (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) ->
                              bslt X (BI_denote (BIC e c (BIC e2 c2 r2)))).
    { intros X HX. rewrite BI_denote_cons.
      apply bslt_bsub_l with (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))); auto.
      apply (bslt_badd_pos _ bzero); auto. }
    destruct HK as [HKe|[Hzc|HKr]].
    + destruct (Kge_ctx e He z HKe) as [C [ζ [HC [Hζ [Hzζ Hsub]]]]].
      exists (fun ξ => bexpΩ (C ξ)), ζ. split; [ apply bctx_exp; auto | split; [ auto | split; [ auto | ] ] ].
      apply Htail. eapply bsub_trans; [ apply bsub_bexpΩ, Hsub | apply bsub_P_Pz, Hc0 ].
    + exists (fun ξ => bmul (bexpΩ (BI_denote e)) (embed ξ)), (BS_denote c).
      split; [ apply bctx_mul; [ apply bcd_bexpΩ, BI_ok | apply bpos_bexpΩ | apply bctx_embed ] | ].
      split; [ apply BS_complete | split; [ auto | apply Htail, bsub_refl ] ].
    + destruct (IHr Hr z HKr) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
      exists (fun ξ => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (C ξ)), ζ.
      split; [ apply bctx_add; auto | split; [ auto | split; [ auto | ] ] ].
      rewrite BI_denote_cons. apply bslt_badd_r; auto.
Qed.

(** All coefficients, at any depth, are at most z. *)
Fixpoint Kle (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => Kle z e /\ BS_denote c ≤ z /\ Kle z r
  end.

Lemma Kle_lt z w T : Kle z T -> z < w -> Klt w T.
Proof.
  intros H Hz. induction T as [|e IHe c r IHr]; simpl in *; auto.
  destruct H as [H1 [H2 H3]]. split; auto. split; auto. eapply ord_le_lt_trans; eauto.
Qed.

Lemma Kge_ieq z T T' : ieq T T' -> Kge z T -> Kge z T'.
Proof.
  intro H. induction H as [|e c r e' c' r' He IHe Hc Hr IHr]; simpl; auto.
  intros [H1|[H1|H1]]; auto. right; left. rewrite <- Hc; auto.
Qed.

Lemma Kin_nf k T : Kin k T -> BI_nf T -> BS_nf k.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [He [Hc [_ [Hr _]]]]; [ auto | subst; auto | auto ].
Qed.

Lemma Kin_size' k T : Kin k T -> (BS_size k <= BI_size T)%nat.
Proof. intro H. pose proof (Kin_size k T H). lia. Qed.

(** *** The largest coefficient *)

Definition omax (n:nat) (a b:option BSmall) : option BSmall :=
  match a, b with
  | None, x => x
  | x, None => x
  | Some u, Some v => if isLT (cmpS n u v) then Some v else Some u
  end.

Fixpoint kmax (n:nat) (T:BIdx) : option BSmall :=
  match T with
  | BIZ => None
  | BIC e c r => omax n (omax n (kmax n e) (Some c)) (kmax n r)
  end.

Definition kmax_ok (T:BIdx) (o:option BSmall) : Prop :=
  match o with
  | None => T = BIZ
  | Some m => Kin m T /\ Kle (BS_denote m) T
  end.

Lemma Kle_mono z z' T : z ≤ z' -> Kle z T -> Kle z' T.
Proof.
  intro Hz. induction T as [|e IHe c r IHr]; simpl; auto.
  intros [H1 [H2 H3]]. split; auto. split; auto. transitivity z; auto.
Qed.

(** The max of two coefficient candidates. *)
Lemma omax_spec n a b (P:BSmall -> Prop) :
  (forall u v, P u -> P v -> ordering_correct (cmpS n u v) (BS_denote u) (BS_denote v)) ->
  match a with None => True | Some u => P u end -> match b with None => True | Some v => P v end ->
  match omax n a b with
  | None => a = None /\ b = None
  | Some w => P w /\ (w = match a with Some u => u | None => w end \/ w = match b with Some v => v | None => w end) /\
              match a with None => True | Some u => BS_denote u ≤ BS_denote w end /\
              match b with None => True | Some v => BS_denote v ≤ BS_denote w end
  end.
Proof.
  intros Hc Ha Hb.
  destruct a as [u|]; destruct b as [v|]; simpl; auto.
  - destruct (isLT_spec _ _ _ (Hc u v Ha Hb)) as [S1 S2].
    destruct (isLT (cmpS n u v)) eqn:E.
    + split; auto. split; [ right; auto | split; [ apply ord_lt_le; auto | reflexivity ] ].
    + split; auto. split; [ left; auto | split; [ reflexivity | auto ] ].
  - split; auto. split; [ left; auto | split; reflexivity ].
  - split; auto. split; [ right; auto | split; reflexivity ].
Qed.

Lemma kmax_spec n : forall T, BI_nf T -> (BI_size T + BI_size T < n)%nat -> kmax_ok T (kmax n T).
Proof.
  induction T as [|e IHe c r IHr]; intros HT Hsz; simpl; auto.
  simpl in Hsz. destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
  set (P := fun u => BS_nf u /\ (BS_size u <= BI_size (BIC e c r))%nat /\ Kin u (BIC e c r)).
  assert (HP : forall u v, P u -> P v -> ordering_correct (cmpS n u v) (BS_denote u) (BS_denote v)).
  { intros u v [Hu [Hsu _]] [Hv [Hsv _]]. apply (proj1 (cmp_correct n)); auto. simpl in Hsu, Hsv. lia. }
  assert (He' := IHe He ltac:(lia)). assert (Hr' := IHr Hr ltac:(lia)).
  assert (Pe : match kmax n e with None => True | Some u => P u end).
  { destruct (kmax n e) as [u|]; auto. destruct He' as [Hin Hle].
    split; [ apply (Kin_nf u e); auto | split; [ pose proof (Kin_size' u e Hin); simpl; lia | simpl; auto ] ]. }
  assert (Pc : P c).
  { split; auto. split; [ simpl; lia | simpl; auto ]. }
  assert (Pr : match kmax n r with None => True | Some u => P u end).
  { destruct (kmax n r) as [u|]; auto. destruct Hr' as [Hin Hle].
    split; [ apply (Kin_nf u r); auto | split; [ pose proof (Kin_size' u r Hin); simpl; lia | simpl; auto ] ]. }
  assert (S1 := omax_spec n (kmax n e) (Some c) P HP Pe Pc).
  destruct (omax n (kmax n e) (Some c)) as [w1|] eqn:E1; [ | destruct S1 as [_ D]; discriminate ].
  destruct S1 as [Pw1 [_ [Lw1e Lw1c]]].
  assert (S2 := omax_spec n (Some w1) (kmax n r) P HP Pw1 Pr).
  destruct (omax n (Some w1) (kmax n r)) as [w|] eqn:E2; [ | destruct S2 as [D _]; discriminate ].
  destruct S2 as [Pw [_ [Lw1 Lwr]]].
  split; [ apply Pw | ].
  simpl. split; [ | split ].
  - destruct (kmax n e) as [u|]; [ | simpl in He'; rewrite He'; exact I ].
    destruct He' as [_ Hle]. apply Kle_mono with (BS_denote u); auto. transitivity (BS_denote w1); auto.
  - transitivity (BS_denote w1); auto.
  - destruct (kmax n r) as [u|]; [ | rewrite Hr'; exact I ].
    destruct Hr' as [_ Hle]. apply Kle_mono with (BS_denote u); auto.
Qed.

(** *** The end test *)

(** c ≤ 1, for a positive normal coefficient: c = 1. *)
Definition le_one (n:nat) (c:BSmall) : bool :=
  match cmpS n c BS_one with GT => false | _ => true end.

Fixpoint end_test (n:nat) (m:BSmall) (T:BIdx) : bool :=
  match T with
  | BIZ => true
  | BIC e c r =>
      match r with
      | BIZ => coefs_below n e m || (le_one n c && end_test n m e)
      | _ => coefs_below n e m && isLT (cmpS n c m) && end_test n m r
      end
  end.

Lemma BS_one_nf : BS_nf BS_one.
Proof.
  split; [ exact I | split; [ exact I | split; [ apply BS_pos | exact I ] ] ].
Qed.

Lemma BS_one_denote : BS_denote BS_one ≈ 1.
Proof.
  unfold BS_one. rewrite BS_denote_onePlus. rewrite addOrd_zero_r. reflexivity.
Qed.

Lemma le_one_spec n c : BS_nf c -> 0 < BS_denote c -> (BS_size c + 3 < n)%nat ->
  (le_one n c = true -> BS_denote c ≈ 1) /\ (le_one n c = false -> 1 < BS_denote c).
Proof.
  intros Hc Hc0 Hsz.
  assert (H := proj1 (cmp_correct n) c BS_one ltac:(simpl; lia) Hc BS_one_nf).
  unfold le_one. destruct (cmpS n c BS_one); simpl in H; split; intro E; try discriminate.
  - split; [ rewrite <- BS_one_denote; apply ord_lt_le; auto | ].
    apply succ_least; auto.
  - rewrite H. apply BS_one_denote.
  - rewrite <- BS_one_denote. auto.
Qed.

Lemma end_test_spec n m : BS_nf m -> forall T, BI_nf T -> Kle (BS_denote m) T ->
  (BI_size T + BS_size m + 3 < n)%nat ->
  (end_test n m T = true -> Kend (BS_denote m) T) /\ (end_test n m T = false -> Kgs (BS_denote m) T).
Proof.
  intros Hm. induction T as [|e IHe c r IHr]; intros HT HK Hsz; [ simpl; split; auto; discriminate | ].
  simpl in Hsz. assert (HT' := HT). destruct HT' as [He [Hc [Hc0 [Hr Hl]]]].
  destruct HK as [HKe [HKc HKr]].
  destruct (IHe He HKe ltac:(lia)) as [E1 E2].
  destruct (coefs_below_spec n m e
              (fun c0 H0 Hc0' => proj1 (cmp_correct n) c0 m ltac:(lia) Hc0' Hm) He) as [C1 C2].
  destruct (isLT_spec _ _ _ (proj1 (cmp_correct n) c m ltac:(lia) Hc Hm)) as [L1 L2].
  destruct (le_one_spec n c Hc Hc0 ltac:(lia)) as [O1 O2].
  destruct r as [|e2 c2 r2].
  - change ((coefs_below n e m || (le_one n c && end_test n m e) = true ->
             (Klt (BS_denote m) e /\ BS_denote c ≤ BS_denote m) \/
             (Kend (BS_denote m) e /\ BS_denote c ≈ 1)) /\
            (coefs_below n e m || (le_one n c && end_test n m e) = false ->
             (Kge (BS_denote m) e /\ 1 < BS_denote c) \/ (BS_denote c ≈ 1 /\ Kgs (BS_denote m) e))).
    destruct (coefs_below n e m); destruct (le_one n c); destruct (end_test n m e); simpl;
      split; intro H; try discriminate; intuition.
  - destruct (IHr Hr HKr ltac:(simpl in *; lia)) as [R1 R2].
    change ((coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2) = true ->
             Klt (BS_denote m) e /\ BS_denote c < BS_denote m /\ Kend (BS_denote m) (BIC e2 c2 r2)) /\
            (coefs_below n e m && isLT (cmpS n c m) && end_test n m (BIC e2 c2 r2) = false ->
             Kge (BS_denote m) e \/ BS_denote m ≤ BS_denote c \/ Kgs (BS_denote m) (BIC e2 c2 r2))).
    destruct (coefs_below n e m); destruct (isLT (cmpS n c m)); destruct (end_test n m (BIC e2 c2 r2)); simpl;
      split; intro H; try discriminate; intuition.
Qed.

(** *** Deciding the coefficient redex *)

Definition coll_test (n:nat) (T:BIdx) : option BSmall :=
  match kmax n T with
  | None => None
  | Some m =>
      match m with
      | BZ => None
      | BN Tm _ =>
          match cmpI n T Tm with
          | LT => if end_test n m T then Some m else None
          | _ => None
          end
      end
  end.

Theorem coll_test_correct T : BI_nf T ->
  let n := S (4 * BI_size T + 4) in
  (forall m, coll_test n T = Some m -> Kin m T /\ BS_denote (BN T BZ) ≤ BS_denote m) /\
  (coll_test n T = None -> Klt (BS_denote (BN T BZ)) T).
Proof.
  intros HT n.
  assert (HK := kmax_spec n T HT ltac:(unfold n; lia)).
  unfold coll_test.
  destruct (kmax n T) as [m|] eqn:Ek; [ | simpl in HK; subst; split; [ discriminate | intros _; exact I ] ].
  destruct HK as [Hin Hle].
  assert (Hm : BS_nf m) by (apply (Kin_nf m T); auto).
  assert (Hms := Kin_size m T Hin).
  assert (Hdom : BS_denote m ≤ BS_denote (BN T BZ)) by (apply dominance; auto using BI_nf_pos, Kin_Kge).
  destruct m as [|Tm ym].
  - split; [ discriminate | intros _ ].
    apply Kle_lt with (BS_denote BZ); auto. apply BS_pos.
  - assert (Hm' := Hm). destruct Hm' as [HTm [Hym [Hymlt HKm]]].
    simpl in Hms.
    assert (HI := proj2 (cmp_correct n) T Tm ltac:(unfold n; lia) HT HTm).
    (* m below the value suffices for the coefficient condition *)
    assert (Hlt_ok : BS_denote (BN Tm ym) < BS_denote (BN T BZ) -> Klt (BS_denote (BN T BZ)) T).
    { intro H. apply Kle_lt with (BS_denote (BN Tm ym)); auto. }
    destruct (cmpI n T Tm) eqn:EI; simpl in HI.
    + destruct (end_test_spec n (BN Tm ym) Hm T HT Hle ltac:(unfold n; simpl; lia)) as [N1 N2].
      destruct (end_test n (BN Tm ym) T) eqn:Ee.
      * split; [ | discriminate ].
        intros m' Em'. injection Em' as <-. split; auto.
        assert (Hne : Tm <> BIZ) by (intro E; subst; inversion HI).
        assert (Hz := BN_inf Tm ym HTm Hne).
        assert (HB := proj1 (nest_le _ Hz (S (BI_size T)) T ltac:(lia) HT (N1 eq_refl)) Tm HTm (Klt_Kend _ _ HKm) HI).
        assert (Hi : inhabited (bsmall (BI_denote Tm) + bbig (BI_denote Tm))).
        { destruct Tm as [|e' c' r']; [ tauto | ]. apply BI_inh. apply HTm. }
        exact (bleZ_sound (addOrd 1) onePlus_normal _ _ _ HB (BI_denote Tm) (bsub_refl _) (BI_good Tm)
                 (BI_bfam Tm) (BS_complete (BN Tm ym))
                 (bfix_value_full (addOrd 1) onePlus_normal _ _ (BI_good Tm) Hi (BS_complete ym))).
      * split; [ discriminate | intros _ ].
        apply Hlt_ok.
        destruct (Kgs_ctx T (BI_nf_pos T HT) _ (N2 eq_refl)) as [C [ζ [HC [Hζ [Hmζ Hlt]]]]].
        apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
        -- transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
        -- apply (bphi_strict (addOrd 1) onePlus_normal); auto using BI_good, BI_bfam.
    + split; [ discriminate | intros _ ].
      exfalso. apply (ord_lt_irreflexive (BS_denote (BN Tm ym))).
      apply (Kge_lt _ _ Tm); auto.
      apply (Kge_ieq _ T); auto. apply Kin_Kge; auto.
    + split; [ discriminate | intros _ ].
      apply Hlt_ok. apply nest_lt_idx; auto.
      * eapply ord_lt_le_trans; [ exact Hymlt | exact Hdom ].
      * apply Klt_mono with (BS_denote (BN Tm ym)); auto.
Qed.

(** ** The normalizer *)

Definition smartN (T:BIdx) (y:BSmall) : BSmall :=
  if fix_test (S (BI_size T + BS_size y)) T y then y
  else match y with
       | BZ => match coll_test (S (4 * BI_size T + 4)) T with
               | Some m => m
               | None => BN T BZ
               end
       | _ => BN T y
       end.

Fixpoint normS (x:BSmall) : BSmall :=
  match x with
  | BZ => BZ
  | BN T y => smartN (normI T) (normS y)
  end
with normI (T:BIdx) : BIdx :=
  match T with
  | BIZ => BIZ
  | BIC e c r => BIC (normI e) (normS c) (normI r)
  end.

(** Coefficients of T lie below φ_T(y) once y is positive. *)
Lemma Klt_of_Kge w T : (forall z, Kge z T -> z < w) -> Klt w T.
Proof.
  induction T as [|e IHe c r IHr]; simpl; intro H; auto.
  split; [ apply IHe; auto | split; [ apply H; right; left; reflexivity | apply IHr; auto ] ].
Qed.

Lemma Klt_pos_arg T y : BI_nf T -> 0 < BS_denote y -> Klt (BS_denote (BN T y)) T.
Proof.
  intros HT Hy. apply Klt_of_Kge. intros z Hz.
  apply ord_le_lt_trans with (BS_denote (BN T BZ)).
  - apply dominance; auto using BI_nf_pos.
  - apply (normal_increasing _ (BI_normal T) 0 (BS_denote y) (BS_complete y) Hy).
Qed.

Lemma smartN_correct T y : BI_nf T -> BS_nf y ->
  BS_nf (smartN T y) /\ BS_denote (smartN T y) ≈ BS_denote (BN T y).
Proof.
  intros HT Hy. unfold smartN.
  destruct (fix_test_correct T y HT Hy) as [F1 F2].
  destruct (fix_test (S (BI_size T + BS_size y)) T y) eqn:Ef.
  - split; auto. split; [ apply normal_inflationary; auto using BI_normal, BS_complete | apply F1; auto ].
  - assert (Hlt := F2 eq_refl).
    destruct y as [|Ty yy].
    + destruct (coll_test_correct T HT) as [C1 C2].
      destruct (coll_test (S (4 * BI_size T + 4)) T) as [m|] eqn:Ec.
      * destruct (C1 m eq_refl) as [Hin Hle].
        split; [ apply (Kin_nf m T); auto | ].
        split; [ apply dominance; auto using BI_nf_pos, Kin_Kge | auto ].
      * split; [ | reflexivity ].
        exact (conj HT (conj I (conj (BS_pos T BZ) (C2 eq_refl)))).
    + split; [ | reflexivity ].
      exact (conj HT (conj Hy (conj Hlt (Klt_pos_arg T (BN Ty yy) HT (BS_pos Ty yy))))).

Qed.

Theorem normalize_correct :
  (forall x, BS_proper x -> BS_nf (normS x) /\ BS_denote (normS x) ≈ BS_denote x) /\
  (forall T, BI_proper T -> BI_nf (normI T) /\ ieq (normI T) T).
Proof.
  apply BNotation_mut.
  - intros _. split; [ exact I | reflexivity ].
  - intros T IHT y IHy [HT Hy].
    destruct (IHT HT) as [HT' HTe]. destruct (IHy Hy) as [Hy' Hye].
    destruct (smartN_correct _ _ HT' Hy') as [N1 N2].
    split; auto. simpl. rewrite N2. simpl.
    rewrite (bphi_ieq _ _ _ HTe). apply ord_eq_normal; auto using BI_normal.
  - intros _. split; [ exact I | constructor ].
  - intros e IHe c IHc r IHr [He [Hc [Hc0 [Hr Hl]]]].
    destruct (IHe He) as [He' Hee]. destruct (IHc Hc) as [Hc' Hce]. destruct (IHr Hr) as [Hr' Hre].
    split; [ | constructor; auto ].
    simpl. split; auto. split; auto. split; [ rewrite Hce; auto | split; auto ].
    apply (lead_below_ieq r (normI r) e (normI e)); auto using ieq_sym.
Qed.

Corollary normS_nf x : BS_proper x -> BS_nf (normS x).
Proof. apply normalize_correct. Qed.

Corollary normS_equal x : BS_proper x -> BS_denote (normS x) ≈ BS_denote x.
Proof. apply normalize_correct. Qed.

(** ** Reduction to the normal form *)

From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.

Definition reds := clos_refl_trans BSmall red_S.
Definition redsI := clos_refl_trans BIdx red_I.

Lemma reds_trans x y z : reds x y -> reds y z -> reds x z.
Proof. intros; eapply rt_trans; eauto. Qed.

Lemma reds_BN_idx T T' y : redsI T T' -> reds (BN T y) (BN T' y).
Proof.
  intro H. induction H; [ apply rt_step, red_idx; auto | apply rt_refl | eapply rt_trans; eauto ].
Qed.

Lemma reds_BN_arg T y y' : reds y y' -> reds (BN T y) (BN T y').
Proof.
  intro H. induction H; [ apply rt_step, red_arg; auto | apply rt_refl | eapply rt_trans; eauto ].
Qed.

Lemma redsI_exp e e' c r : redsI e e' -> redsI (BIC e c r) (BIC e' c r).
Proof. intro H. induction H; [ apply rt_step, red_exp; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma redsI_coef e c c' r : reds c c' -> redsI (BIC e c r) (BIC e c' r).
Proof. intro H. induction H; [ apply rt_step, red_coef; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma redsI_rest e c r r' : redsI r r' -> redsI (BIC e c r) (BIC e c r').
Proof. intro H. induction H; [ apply rt_step, red_rest; auto | apply rt_refl | eapply rt_trans; eauto ]. Qed.

Lemma smartN_reds T y : BI_nf T -> BS_nf y -> reds (BN T y) (smartN T y).
Proof.
  intros HT Hy. unfold smartN.
  destruct (fix_test_correct T y HT Hy) as [F1 _].
  destruct (fix_test (S (BI_size T + BS_size y)) T y) eqn:Ef.
  - apply rt_step, red_top, redex_arg, F1; auto.
  - destruct y as [|Ty yy]; [ | apply rt_refl ].
    destruct (coll_test_correct T HT) as [C1 _].
    destruct (coll_test (S (4 * BI_size T + 4)) T) as [m|] eqn:Ec; [ | apply rt_refl ].
    destruct (C1 m eq_refl) as [Hin Hle].
    apply rt_step, red_top, redex_coef; auto.
Qed.

Theorem normalize_reds :
  (forall x, BS_proper x -> reds x (normS x)) /\ (forall T, BI_proper T -> redsI T (normI T)).
Proof.
  apply BNotation_mut.
  - intros _. apply rt_refl.
  - intros T IHT y IHy [HT Hy]. simpl.
    apply reds_trans with (BN (normI T) y); [ apply reds_BN_idx; auto | ].
    apply reds_trans with (BN (normI T) (normS y)); [ apply reds_BN_arg; auto | ].
    apply smartN_reds; [ apply (proj2 normalize_correct); auto | apply (proj1 normalize_correct); auto ].
  - intros _. apply rt_refl.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]]. simpl.
    eapply rt_trans; [ apply redsI_exp; auto | ].
    eapply rt_trans; [ apply redsI_coef; auto | ].
    apply redsI_rest; auto.
Qed.

(** ** Normal forms are exactly the irreducible terms *)

Lemma Kin_Klt k z T : Kin k T -> Klt z T -> BS_denote k < z.
Proof.
  induction T as [|e IHe c r IHr]; simpl; [ tauto | ].
  intros [H|[H|H]] [H1 [H2 H3]]; [ auto | subst; auto | auto ].
Qed.

Theorem nf_irreducible :
  (forall x x', red_S x x' -> ~ BS_nf x) /\ (forall T T', red_I T T' -> ~ BI_nf T).
Proof.
  apply red_mut.
  - intros x x' H Hx. destruct H as [T y H | T y k Hk H].
    + destruct Hx as [_ [_ [Hlt _]]]. apply (ord_lt_irreflexive (BS_denote y)).
      eapply ord_lt_le_trans; eauto.
    + destruct Hx as [_ [_ [_ HK]]]. apply (ord_lt_irreflexive (BS_denote k)).
      eapply ord_lt_le_trans; [ apply (Kin_Klt k _ T Hk HK) | exact H ].
  - intros T T' y H IH [HT _]. auto.
  - intros T y y' H IH [_ [Hy _]]. auto.
  - intros e e' c r H IH [He _]. auto.
  - intros e c c' r H IH [_ [Hc _]]. auto.
  - intros e c r r' H IH [_ [_ [_ [Hr _]]]]. auto.
Qed.

Theorem nf_iff_irreducible x : BS_proper x -> BS_nf x <-> ~ exists x', red_S x x'.
Proof.
  intro Hx. split.
  - intros Hn [x' H]. apply ((proj1 nf_irreducible) x x' H Hn).
  - intro Hirr.
    assert (Hr := proj1 normalize_reds x Hx).
    apply clos_rt_rt1n in Hr.
    assert (Hn := normS_nf x Hx).
    remember (normS x) as w eqn:Ew.
    destruct Hr as [|x1 Hstep]; auto.
    elim Hirr. eexists; eauto.
Qed.

(** ** Unique normal forms and confluence *)

Theorem reds_sound x y : BS_proper x -> reds x y -> BS_proper y /\ BS_denote x ≈ BS_denote y.
Proof.
  intros Hx H. induction H as [x y H | x | x y z H1 IH1 H2 IH2].
  - split; [ apply (proj1 red_proper) with x | apply (proj1 red_sound) ]; auto.
  - split; [ auto | reflexivity ].
  - destruct (IH1 Hx) as [Hy Hxy]. destruct (IH2 Hy) as [Hz Hyz]. split; auto. rewrite Hxy; auto.
Qed.

Definition normalizes (x y:BSmall) : Prop := reds x y /\ BS_nf y.

Theorem normalizes_iff x y : BS_proper x -> normalizes x y <-> BS_nf y /\ BS_denote x ≈ BS_denote y.
Proof.
  intro Hx. split.
  - intros [H Hy]. split; auto. apply (reds_sound x y Hx H).
  - intros [Hy Heq]. split; auto.
    replace y with (normS x); [ apply normalize_reds; auto | ].
    apply BS_nf_unique; auto using normS_nf. rewrite normS_equal; auto.
Qed.

Theorem normalizes_unique x : BS_proper x -> exists! y, normalizes x y.
Proof.
  intro Hx. exists (normS x). split.
  - split; [ apply normalize_reds; auto | apply normS_nf; auto ].
  - intros y Hy. apply (normalizes_iff x y Hx) in Hy. destruct Hy as [Hy Heq].
    apply BS_nf_unique; auto using normS_nf. rewrite normS_equal; auto.
Qed.

Theorem reduce_confluent x y1 y2 : BS_proper x -> reds x y1 -> reds x y2 ->
  exists w, reds y1 w /\ reds y2 w.
Proof.
  intros Hx H1 H2.
  destruct (reds_sound x y1 Hx H1) as [Hy1 E1]. destruct (reds_sound x y2 Hx H2) as [Hy2 E2].
  exists (normS y1). split; [ apply normalize_reds; auto | ].
  replace (normS y1) with (normS y2); [ apply normalize_reds; auto | ].
  apply BS_nf_unique; auto using normS_nf.
  rewrite !normS_equal; auto. rewrite <- E1, <- E2. reflexivity.
Qed.

(** ** Examples, by computation *)

(** φ_1(ε₀) = ω + ε₀ = ε₀: the argument is a fixpoint. *)
Example normalize_arg : normS (BN BI_one (BN BI_Ω BZ)) = BN BI_Ω BZ.
Proof. reflexivity. Qed.

(** φ_{Ω^0·ε₀}(0) = ω^{ε₀} = ε₀: collapse to the coefficient. *)
Example normalize_coef : normS (BN (BIC BIZ (BN BI_Ω BZ) BIZ) BZ) = BN BI_Ω BZ.
Proof. reflexivity. Qed.

(** ε₀ + 1 = ω^{ε₀} + 1 is normal, and φ_{Ω^0·(ε₀+1)}(0) = ω^{ε₀+1}
    does not collapse. *)
Definition BS_ε0_plus1 : BSmall := BN (BIC BIZ (BN BI_Ω BZ) BIZ) BS_one.

Example normalize_ε0_plus1 : normS BS_ε0_plus1 = BS_ε0_plus1.
Proof. reflexivity. Qed.

Example normalize_nocollapse :
  normS (BN (BIC BIZ BS_ε0_plus1 BIZ) BZ) = BN (BIC BIZ BS_ε0_plus1 BIZ) BZ.
Proof. reflexivity. Qed.

(** * Interpolants

Every normal notation has interpolants: each ordinal below it is
bounded by a smaller normal notation which has interpolants in turn.
Under excluded middle this means that every ordinal below a notation
is denoted by a normal notation.  The proof has a semantic half
(@cfe_interp@/@bphi_interp@: everything below φ_T(u) lies below 1+u or
below a finite composition of the components of ⟦T⟧) and a syntactic
half (@cover@: each component is sandwiched, up to @bsub@, between
components given by normal notations, i.e. syntactic fundamental
sequences). *)

Abbreviation HI := (has_interpolants BS_denote BS_nf).

Lemma HI_zero : HI 0.
Proof.
  rewrite has_interpolants_unfold. intros i Hi.
  rewrite ord_lt_unfold in Hi. destruct Hi as [[] _].
Qed.

Lemma HI_below z γ : HI z -> γ < z ->
  exists n, BS_nf n /\ HI (BS_denote n) /\ γ ≤ BS_denote n /\ BS_denote n < z.
Proof.
  intros H Hγ. rewrite has_interpolants_unfold in H.
  destruct (H γ Hγ) as [n [H1 [H2 [H3 H4]]]]. exists n; auto.
Qed.

Lemma HI_succ m : BS_nf m -> HI (BS_denote m) -> HI (succOrd (BS_denote m)).
Proof.
  intros Hm H. rewrite has_interpolants_unfold. intros i Hi.
  rewrite ord_lt_unfold in Hi. destruct Hi as [[] Hi]. simpl in Hi.
  exists m. split; auto. split; auto. split; auto. apply succ_lt.
Qed.

Definition BS_onePlus (a:BSmall) : BSmall := normS (BN BIZ a).

Lemma BS_onePlus_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD) (addOrd 1) BS_onePlus.
Proof.
  intros x a [Hx Ha].
  assert (Hp : BS_proper (BN BIZ a)) by (split; [ exact I | apply (proj1 nf_proper); auto ]).
  split; [ | apply normS_nf; auto ].
  unfold BS_onePlus. rewrite normS_equal; auto. rewrite BS_denote_onePlus. rewrite Hx. reflexivity.
Qed.

Lemma HI_onePlus x : HI x -> HI (1 + x).
Proof.
  assert (Hz : reflects BSmall BS_denote BS_nf ORD 0 BZ) by (split; [ reflexivity | exact I ]).
  exact (onePlus_interpolants Hz BS_onePlus_reflects x).
Qed.

Lemma HI_eq x y : x ≈ y -> HI x -> HI y.
Proof. intro H. apply (proj1 (has_interpolants_eq_mor BS_denote BS_nf H)). Qed.

Lemma HI_one : HI (BS_denote BS_one).
Proof.
  apply HI_eq with (1 + 0).
  - rewrite BS_one_denote. apply addOrd_zero_r.
  - apply HI_onePlus, HI_zero.
Qed.

(** ** Syntactic covers of the children

Ω^e·0 is not a proper index term; @smartC@ drops a zero coefficient. *)

Definition smartC (e:BIdx) (c:BSmall) (r:BIdx) : BIdx :=
  match c with BZ => r | _ => BIC e c r end.

Lemma smartC_bequiv e c r : bequiv (BI_denote (smartC e c r)) (BI_denote (BIC e c r)).
Proof.
  destruct c as [|T y]; [ | apply bequiv_refl ].
  eapply bequiv_trans; [ apply bequiv_sym, bequiv_badd_zero_l | ].
  apply bequiv_badd; [ | apply bequiv_refl ].
  split; [ apply bsub_bzero_l | apply bsub_mul_zero ].
Qed.

Lemma smartC_nf e c r : BI_nf e -> BS_nf c -> BI_nf r -> lead_below r e -> BI_nf (smartC e c r).
Proof.
  destruct c as [|T y]; [ simpl; auto | ].
  intros He Hc Hr Hl. change (BI_nf e /\ BS_nf (BN T y) /\ 0 < BS_denote (BN T y) /\ BI_nf r /\ lead_below r e).
  split; [ | split; [ | split; [ apply BS_pos | ] ] ]; auto.
Qed.

Lemma Kin_smartC k e c r : Kin k (smartC e c r) -> Kin k (BIC e c r).
Proof. destruct c; simpl; tauto. Qed.

Lemma ilt_smartC e c r T0 : ilt (BIC e c r) T0 -> ilt r T0 -> ilt (smartC e c r) T0.
Proof. destruct c; auto. Qed.

Lemma ilt_trans a b c : ilt a b -> ilt b c -> ilt a c.
Proof.
  intro H. revert c.
  induction H as [e c r | e c r e' c' r' Hee IH | e c r e' c' r' Hee Hcc | e c r e' c' r' Hee Hcc Hrr IH];
    intros t Ht; inversion Ht as [| ? ? ? e2 c2 r2 H1 | ? ? ? e2 c2 r2 H1 H2 | ? ? ? e2 c2 r2 H1 H2 H3]; subst.
  - constructor.
  - constructor.
  - constructor.
  - apply ilt_exp. auto.
  - apply ilt_exp. apply (ilt_ieq e e' Hee e e2); auto using ieq_refl.
  - apply ilt_exp. apply (ilt_ieq e e' Hee e e2); auto using ieq_refl.
  - apply ilt_exp. apply (ilt_ieq e' e2 H1 e e2); auto using ieq_refl, ieq_sym.
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_lt_trans; eauto ].
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_lt_le_trans; eauto; apply H2 ].
  - apply ilt_exp. apply (ilt_ieq e' e2 H1 e e2); auto using ieq_refl, ieq_sym.
  - apply ilt_coef; [ eapply ieq_trans; eauto | eapply ord_le_lt_trans; eauto; apply Hcc ].
  - apply ilt_tail; [ eapply ieq_trans; eauto | transitivity (BS_denote c'); auto | auto ].
Qed.

Lemma lead_below_ilt r' r e : ilt r' r -> lead_below r e -> lead_below r' e.
Proof.
  intros H Hl. destruct H as [e2 c2 r2 | e1 c1 r1 e2 c2 r2 H | e1 c1 r1 e2 c2 r2 H _ | e1 c1 r1 e2 c2 r2 H _ _];
    simpl in *; auto.
  - eapply ilt_trans; eauto.
  - apply (ilt_ieq e2 e Hl e1 e); auto using ieq_refl, ieq_sym.
  - apply (ilt_ieq e2 e Hl e1 e); auto using ieq_refl, ieq_sym.
Qed.

Definition KHI (T:BIdx) : Prop := forall k, Kin k T -> HI (BS_denote k).

(** Every small child of ⟦T₀⟧ lies, up to @bsub@, below a normal index T
    which lies below another small child; every Ω-family member at a
    notation lies below a normal index which lies below another family's
    member at the same argument.  These are Bachmann's fundamental
    sequences up to @bsub@ in both directions. *)
Definition icov (T0:BIdx) : Prop :=
  (forall a, exists T, BI_nf T /\ KHI T /\ ilt T T0 /\
     bsub (bsmallSz (BI_denote T0) a) (BI_denote T) /\
     exists a', bsub (BI_denote T) (bsmallSz (BI_denote T0) a')) /\
  (forall d x, BS_nf x -> HI (BS_denote x) -> exists T, BI_nf T /\ KHI T /\ ilt T T0 /\
     bsub (bbigSz (BI_denote T0) d (BS_denote x)) (BI_denote T) /\
     exists d', bsub (BI_denote T) (bbigSz (BI_denote T0) d' (BS_denote x))).

Lemma KHI_cons e c r : KHI (BIC e c r) -> KHI e /\ HI (BS_denote c) /\ KHI r.
Proof. intro H. split; [ | split ]; [ intros k Hk | | intros k Hk ]; apply H; simpl; auto. Qed.

Lemma KHI_intro e c r : KHI e -> HI (BS_denote c) -> KHI r -> KHI (BIC e c r).
Proof. intros H1 H2 H3 k [Hk|[Hk|Hk]]; [ auto | subst; auto | auto ]. Qed.

Lemma KHI_smartC e c r : KHI e -> HI (BS_denote c) -> KHI r -> KHI (smartC e c r).
Proof. intros H1 H2 H3 k Hk. apply (KHI_intro e c r); auto. apply Kin_smartC; auto. Qed.

Lemma KHI_nil : KHI BIZ.
Proof. intros k []. Qed.

(** A coefficient approximated from below by a notation n, itself
    below an immediate predecessor of the coefficient. *)
Lemma coef_approx c γ : HI (BS_denote c) -> γ < BS_denote c ->
  exists n, BS_nf n /\ HI (BS_denote n) /\ γ ≤ BS_denote n /\ BS_denote n < BS_denote c /\
    exists j, BS_denote n ≤ BS_denote c j.
Proof.
  intros H Hγ. destruct (HI_below _ _ H Hγ) as [n [Hn [HIn [H1 H2]]]].
  exists n. repeat split; auto.
  rewrite ord_lt_unfold in H2. exact H2.
Qed.

Lemma bsub_term_mono e e' γ n : bsub e e' -> γ ≤ n ->
  bsub (bmul (bexpΩ e) (embed γ)) (bmul (bexpΩ e') (embed n)).
Proof.
  intros He Hγ. eapply bsub_trans; [ apply bsub_bmul_r, bsub_embed; exact Hγ | ].
  apply bsub_bmul_l, bsub_bexpΩ; auto.
Qed.

Theorem cover : forall T0, BI_nf T0 -> KHI T0 -> icov T0.
Proof.
  induction T0 as [|e IHe c r IHr]; intros HT HK.
  - split; [ intros [] | intros [] ].
  - destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
    destruct (KHI_cons _ _ _ HK) as [HKe [HKc HKr]].
    destruct (IHe He HKe) as [Se Fe]. destruct (IHr Hr HKr) as [Sr Fr].
    assert (Hnf : forall n x, BS_nf n -> BI_nf x -> lead_below x e -> BI_nf (smartC e n x)).
    { intros. apply smartC_nf; auto. }
    assert (Hilt : forall n x, BS_denote n < BS_denote c -> ilt x (BIC e c r) ->
                      ilt (smartC e n x) (BIC e c r)).
    { intros n x Hn Hx. apply ilt_smartC; auto. apply ilt_coef; auto using ieq_refl. }
    unfold icov.
    change (BI_denote (BIC e c r)) with
      (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)).
    split.
    + intro a.
      destruct (badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a)
        as [[a' Ea]|[b Eb]]; rewrite ?Ea, ?Eb.
      * destruct (mul_small_form (bexpΩ (BI_denote e)) (BS_denote c) a') as [γ [Hγ [k Hk]]].
        rewrite Hk, bexpΩ_small_all.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        exists (smartC e n BIZ). split; [ apply Hnf; simpl; auto | split; [ apply KHI_smartC; auto using KHI_nil | ] ].
        split; [ apply Hilt; auto; constructor | ].
        split.
        { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
          apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl. }
        destruct (bexpΩ_small_zero (BI_denote e)) as [t0 Ht0].
        destruct (mul_small_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [a0 Ha0].
        destruct (badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) a0) as [a'' Ha''].
        exists a''. rewrite Ha'', Ha0, Ht0.
        eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
        apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
      * destruct (Sr b) as [r' [Hr' [HKr' [Hlt [Hlo [b' Hup]]]]]].
        exists (BIC e c r'). split; [ simpl; repeat split; auto; eapply lead_below_ilt; eauto | ].
        split; [ apply KHI_intro; auto | ].
        split; [ apply ilt_tail; auto using ieq_refl; reflexivity | ].
        split; [ simpl; apply bsub_badd_r; auto | ].
        destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) b') as [a'' Ha''].
        exists a''. rewrite Ha''. simpl. apply bsub_badd_r; auto.
    + intros d x Hx HIx.
      destruct (badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d)
        as [[d' Ed]|[d' Ed]]; rewrite Ed.
      * destruct (mul_big_form (bexpΩ (BI_denote e)) (BS_denote c) d') as [γ [Hγ [k Hk]]].
        rewrite Hk.
        destruct (coef_approx c γ HKc Hγ) as [n [Hn [HIn [Hγn [Hnc [j Hj]]]]]].
        destruct (bexpΩ_big_cases (BI_denote e) k) as [[q Hq]|[de Hde]].
        -- rewrite Hq. destruct (Se q) as [e' [He' [HKe' [Hlte [Hloe [q' Hupe]]]]]].
           exists (smartC e n (smartC e' x BIZ)).
           split.
           { apply Hnf; auto. apply smartC_nf; simpl; auto. destruct x; simpl; auto. }
           split; [ apply KHI_smartC; auto; apply KHI_smartC; auto using KHI_nil | ].
           split; [ apply Hilt; auto; apply ilt_smartC; [ apply ilt_exp; auto | constructor ] | ].
           split.
           { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
             simpl. apply bsub_trans with
               (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n))) (BI_denote (BIC e' x BIZ))).
             - apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                           (bmul (bexpΩ (bsmallSz (BI_denote e) q)) (embed (BS_denote x)))).
               + apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
               + apply bsub_badd_r. simpl. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
                 apply bsub_term_mono; auto. reflexivity.
             - apply bsub_badd_r. apply (proj2 (smartC_bequiv _ _ _)). }
           destruct (bexpΩ_fam_s (BI_denote e) q') as [t0 Ht0].
           destruct (mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [d0 Hd0].
           destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0) as [d'' Hd''].
           exists d''. rewrite Hd'', Hd0, Ht0.
           eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
           simpl. apply bsub_trans with
             (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n))) (BI_denote (BIC e' x BIZ))).
           ++ apply bsub_badd_r. apply (proj1 (smartC_bequiv _ _ _)).
           ++ eapply bsub_trans; [ apply bsub_badd_l, bsub_term_mono; [ apply bsub_refl | exact Hj ] | ].
              apply bsub_badd_r. simpl. eapply bsub_trans; [ apply (proj1 (bequiv_badd_zero_r _)) | ].
              apply bsub_term_mono; auto. reflexivity.
        -- rewrite Hde. destruct (Fe de x Hx HIx) as [e' [He' [HKe' [Hlte [Hloe [de' Hupe]]]]]].
           exists (smartC e n (BIC e' BS_one BIZ)).
           assert (H1 : bequiv (bmul (bexpΩ (BI_denote e')) (embed (BS_denote BS_one))) (bexpΩ (BI_denote e'))).
           { eapply bequiv_trans; [ apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed, BS_one_denote ] | ].
             split; apply bsub_bmul_one. }
           split.
           { apply Hnf; [ exact Hn | | exact Hlte ].
             change (BI_nf e' /\ BS_nf BS_one /\ 0 < BS_denote BS_one /\ BI_nf BIZ /\ lead_below BIZ e').
             split; [ exact He' | split; [ apply BS_one_nf | split; [ | split; exact I ] ] ].
             rewrite BS_one_denote. apply succ_lt. }
           split; [ apply KHI_smartC; auto; apply KHI_intro; auto using KHI_nil, HI_one | ].
           split; [ apply Hilt; auto; apply ilt_exp; auto | ].
           split.
           { eapply bsub_trans; [ | apply (proj2 (smartC_bequiv _ _ _)) ].
             simpl. apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                                (bexpΩ (bbigSz (BI_denote e) de (BS_denote x)))).
             - apply bsub_badd_l. apply bsub_term_mono; auto using bsub_refl.
             - apply bsub_badd_r. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
               eapply bsub_trans; [ | apply (proj2 H1) ]. apply bsub_bexpΩ; auto. }
           destruct (bexpΩ_big_b (BI_denote e) de') as [t0 Ht0].
           destruct (mul_big_back (bexpΩ (BI_denote e)) (BS_denote c) j t0) as [d0 Hd0].
           destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d0) as [d'' Hd''].
           exists d''. rewrite Hd'', Hd0, Ht0.
           eapply bsub_trans; [ apply (proj1 (smartC_bequiv _ _ _)) | ].
           simpl. apply bsub_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote n)))
                                              (bexpΩ (BI_denote e'))).
           ++ apply bsub_badd_r. eapply bsub_trans; [ apply (proj1 (bequiv_badd_zero_r _)) | apply (proj1 H1) ].
           ++ eapply bsub_trans; [ apply bsub_badd_l, bsub_term_mono; [ apply bsub_refl | exact Hj ] | ].
              apply bsub_badd_r. apply bsub_bexpΩ; auto.
      * destruct (Fr d' x Hx HIx) as [r' [Hr' [HKr' [Hlt [Hlo [d'' Hup]]]]]].
        exists (BIC e c r'). split; [ simpl; repeat split; auto; eapply lead_below_ilt; eauto | ].
        split; [ apply KHI_intro; auto | ].
        split; [ apply ilt_tail; auto using ieq_refl; reflexivity | ].
        split; [ simpl; apply bsub_badd_r; auto | ].
        destruct (badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r) d'') as [d0 Hd0].
        exists d0. rewrite Hd0. simpl. apply bsub_badd_r; auto.
Qed.

(** ** Interpolation

By induction on the index tree (in the well-founded order @blt@) and
then on the argument: below φ_T(u), everything lies below 1+u (handled
by the interpolants of 1+x), or below a word in f and the components
applied to 0 or to the successor of an earlier value.  Each component
is replaced by the φ of a covering normal index, which takes notations
to notations, has interpolants by induction (its tree lies below a
child of ⟦T⟧), and stays below φ_T(u) because it lies below another
component. *)

Lemma onePlus_mono : forall x y, x ≤ y -> 1 + x ≤ 1 + y.
Proof. apply normal_monotone, onePlus_normal. Qed.

Lemma nf_BN_proper T y : BI_nf T -> BS_nf y -> BS_proper (BN T y).
Proof. intros. split; [ apply (proj2 nf_proper) | apply (proj1 nf_proper) ]; auto. Qed.

Theorem interp_aux : forall U T, BI_nf T -> KHI T -> ble (BI_denote T) U ->
  forall u, complete u -> HI u -> HI (bphi (addOrd 1) (BI_denote T) u).
Proof.
  intro U. induction U as [U IHU] using (well_founded_induction blt_wf).
  intros T HT HK HU u. induction u as [u IHu] using ordinal_induction. intros Hu HIu.
  destruct (cover T HT HK) as [CS CF].
  assert (Hg := BI_good T). assert (Hfam := BI_bfam T).
  set (X := BI_denote T) in *.
  set (V := bphi (addOrd 1) X u).
  assert (Hcomp : forall T', BI_nf T' -> KHI T' -> blt (BI_denote T') X ->
             forall m, BS_nf m -> HI (BS_denote m) -> HI (bphi (addOrd 1) (BI_denote T') (BS_denote m))).
  { intros T' HT' HK' Hlt m Hm HIm.
    apply (IHU (BI_denote T')); auto using ble_refl, BS_complete.
    apply blt_le_trans with X; auto. }
  rewrite has_interpolants_unfold. intros i Hi.
  destruct (bphi_interp _ onePlus_normal X u i Hg Hu Hi) as [Hi1 | [Hinh [o [w [Hiw Hst]]]]].
  - destruct (HI_below _ _ (HI_onePlus u HIu) Hi1) as [n [Hn [HIn [H1 H2]]]].
    exists n. repeat split; auto.
    eapply ord_lt_le_trans; [ exact H2 | apply bphi_ge_f ].
  - destruct (bfix_value_full _ onePlus_normal X u Hg Hinh Hu) as [Hf1 [Hf2 Hf3]].
    fold V in Hf1, Hf2, Hf3.
    assert (Hchain : forall w x0 m, BS_nf m -> x0 ≤ BS_denote m -> BS_denote m ≤ V -> HI (BS_denote m) ->
      exists m', BS_nf m' /\ wev (addOrd 1) _ (bphi_fam (addOrd 1) (bsmallSz X) (bbigSz X)) w x0 ≤ BS_denote m' /\
                 BS_denote m' ≤ V /\ HI (BS_denote m')).
    { clear Hiw Hst. intro w0.
      induction w0 as [|[[a|c]|] w0 IHw]; intros x0 m Hm L0 U0 HI0; simpl.
      - exists m; auto.
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (CS a) as [T' [HT' [HK' [_ [Hlo [a' Hup]]]]]].
        assert (Hp := nf_BN_proper T' m1 HT' Hm1).
        exists (normS (BN T' m1)). split; [ apply normS_nf; auto | ].
        rewrite (normS_equal _ Hp). simpl.
        split; [ | split ].
        + transitivity (bphi (addOrd 1) (bsmallSz X a) (BS_denote m1)).
          * apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a))); auto.
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam T'))); auto.
        + transitivity (bphi (addOrd 1) (bsmallSz X a') (BS_denote m1)).
          { apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a'))); auto. }
          transitivity (bphi (addOrd 1) (bsmallSz X a') V); auto.
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hfam a'))); auto.
        + apply Hcomp; auto. apply (bsub_child_blt _ X (inl a')). auto.
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (CF c m1 Hm1 HI1) as [T' [HT' [HK' [_ [Hlo [c' Hup]]]]]].
        assert (Hp := nf_BN_proper T' BZ HT' I).
        exists (normS (BN T' BZ)). split; [ apply normS_nf; auto | ].
        rewrite (normS_equal _ Hp). simpl.
        split; [ | split ].
        + transitivity (bphi (addOrd 1) (bbigSz X c (BS_denote m1)) 0).
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c _))).
            apply bfam_fam; auto.
          * apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam T'))); auto.
        + transitivity (bphi (addOrd 1) (bbigSz X c' (BS_denote m1)) 0).
          { apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _))); auto. }
          transitivity (bphi (addOrd 1) (bbigSz X c' V) 0); auto.
          apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hfam c' _))).
          apply bfam_fam; auto.
        + apply (Hcomp T' HT' HK' (bsub_child_blt _ X (inr (c', BS_denote m1)) Hup) BZ I HI_zero).
      - destruct (IHw x0 m Hm L0 U0 HI0) as [m1 [Hm1 [L1 [U1 HI1]]]].
        destruct (BS_onePlus_reflects (BS_denote m1) m1 (conj (ord_eq_refl _) Hm1)) as [E1 N1].
        exists (BS_onePlus m1). split; auto.
        rewrite <- E1. split; [ | split ].
        + apply onePlus_mono; auto.
        + transitivity (1 + V); auto. apply onePlus_mono; auto.
        + apply HI_onePlus; auto. }
    assert (Hstart : exists m, BS_nf m /\
      match o with None => 0 | Some j => succOrd (bphi (addOrd 1) X (u j)) end ≤ BS_denote m /\
      BS_denote m ≤ V /\ HI (BS_denote m)).
    { destruct o as [j|].
      - assert (Hj : u j < u) by apply index_lt.
        destruct (HI_below _ _ HIu Hj) as [n [Hn [HIn [H1 H2]]]].
        assert (Hp := nf_BN_proper T n HT Hn).
        set (m0 := normS (BN T n)).
        assert (Hm0 : BS_nf m0) by (apply normS_nf; auto).
        assert (E0 : BS_denote m0 ≈ bphi (addOrd 1) X (BS_denote n)) by (apply normS_equal; auto).
        destruct (BS_succ_reflects (BS_denote m0) m0 (conj (ord_eq_refl _) Hm0)) as [E1 N1].
        exists (BS_succ m0). split; auto.
        rewrite <- E1. split; [ | split ].
        + apply succ_monotone. rewrite E0.
          apply (proj1 (bphi_mono_index _ onePlus_mono _ Hfam)); auto.
        + apply succ_least. rewrite E0.
          apply (normal_increasing _ (BI_normal T)); auto.
        + apply HI_succ; auto. apply HI_eq with (bphi (addOrd 1) X (BS_denote n)); [ symmetry; auto | ].
          apply IHu; auto using BS_complete.
      - exists BZ. split; [ exact I | ]. split; [ reflexivity | ]. split; [ apply zero_least | exact HI_zero ]. }
    destruct Hstart as [m [Hm [L0 [U0 HI0]]]].
    destruct (Hchain w _ m Hm L0 U0 HI0) as [m' [Hm' [L [U' HI']]]].
    destruct (HI_below _ i HI' (ord_lt_le_trans _ _ _ Hiw L)) as [n [Hn [HIn [H1 H2]]]].
    exists n. repeat split; auto. eapply ord_lt_le_trans; eauto.
Qed.

Lemma notation_KHI : (forall x, BS_nf x -> HI (BS_denote x)) /\ (forall T, BI_nf T -> KHI T).
Proof.
  apply BNotation_mut.
  - intros _. exact HI_zero.
  - intros T IHT y IHy [HT [Hy _]].
    apply (interp_aux (BI_denote T) T HT (IHT HT) (ble_refl _) _ (BS_complete y) (IHy Hy)).
  - intros _. exact KHI_nil.
  - intros e IHe c IHc r IHr [He [Hc [_ [Hr _]]]].
    apply KHI_intro; auto.
Qed.

Theorem BS_has_all_interpolants : has_all_interpolants BS_denote BS_nf.
Proof. intros x Hx. apply notation_KHI; auto. Qed.

Theorem BS_has_enough_notations : ClassicalFacts.excluded_middle -> has_enough_notations BS_denote BS_nf.
Proof.
  intro EM. apply has_interpolants_has_enough_notations; auto using BS_complete.
  apply BS_has_all_interpolants.
Qed.

(** * The natural product *)

Definition BS_nmul := cantor_nmul _ _ _ BS_has_cantor_decomposition.

Theorem BS_nmul_reflects : reflects BSmall BS_denote BS_nf (ORD ==> ORD ==> ORD) nmulOrd BS_nmul.
Proof. apply cantor_nmul_reflects. apply BS_has_all_interpolants. Qed.

(** * The order type of the normal forms

The normal forms are cofinal in BHO₁: their limit is a fixpoint of 1+x
and of the components φ_{tower n} of ε_{Ω+1}, since each component is
bounded by φ of a notation index tₙ (Ω+1, Ω^(Ω+1), …) and so takes
notations to notations. *)

Fixpoint BI_tower (n:nat) : BIdx :=
  match n with
  | O => BIC BI_one BS_one (BIC BIZ BS_one BIZ)
  | S n' => BIC (BI_tower n') BS_one BIZ
  end.

Lemma BS_one_proper : BS_proper BS_one.
Proof. apply (proj1 nf_proper), BS_one_nf. Qed.

Lemma BS_one_pos : 0 < BS_denote BS_one.
Proof. rewrite BS_one_denote. apply succ_lt. Qed.

Lemma BI_tower_proper n : BI_proper (BI_tower n).
Proof.
  induction n as [|n IH]; simpl.
  - repeat split; auto using BS_one_proper, BS_one_pos; constructor.
  - repeat split; auto using BS_one_proper, BS_one_pos.
Qed.

Lemma bequiv_mul_one P : bequiv (bmul P (embed (BS_denote BS_one))) P.
Proof.
  eapply bequiv_trans; [ apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed, BS_one_denote ] | ].
  split; apply bsub_bmul_one.
Qed.

Lemma bsub_succ_add x : bsub (bsucc x) (badd x (embed 1)).
Proof.
  apply bsub_intro; [ | intros [] ].
  intros [].
  destruct (badd_small_r x (embed 1) tt) as [t Ht].
  exists t. rewrite Ht. apply bsub_le_badd.
Qed.

Lemma bsub_tower n : bsub (btower n) (BI_denote (BI_tower n)).
Proof.
  induction n as [|n IH].
  - change (bsub (bsucc bOmega)
      (badd (bmul (bexpΩ (BI_denote BI_one)) (embed (BS_denote BS_one)))
            (badd (bmul (bexpΩ bzero) (embed (BS_denote BS_one))) bzero))).
    assert (H1 : bequiv (BI_denote BI_one) (embed 1)).
    { eapply bequiv_trans; [ apply (exp_equiv BI_one BS_one eq_refl) | apply bequiv_embed, BS_one_denote ]. }
    apply bsub_trans with (badd (bexpΩ (embed 1)) (embed 1)).
    + eapply bsub_trans; [ apply bsub_succ_add | ].
      apply bsub_badd_l. apply Ω_le_exp. apply succ_lt.
    + apply bsub_trans with (badd (bexpΩ (embed 1)) (badd (bmul (bexpΩ bzero) (embed (BS_denote BS_one))) bzero)).
      * apply bsub_badd_r.
        eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
        eapply bsub_trans; [ apply (proj2 (bequiv_embed _ _ BS_one_denote)) | ].
        apply (proj2 (bequiv_one_mul _)).
      * apply bsub_badd_l. eapply bsub_trans; [ | apply (proj2 (bequiv_mul_one _)) ].
        apply bsub_bexpΩ. apply (proj2 H1).
  - simpl. eapply bsub_trans; [ | apply (proj2 (bequiv_badd_zero_r _)) ].
    eapply bsub_trans; [ | apply (proj2 (bequiv_mul_one _)) ].
    apply bsub_bexpΩ; auto.
Qed.

Definition NFOrd : Ord := ord {x:BSmall | BS_nf x} (fun x => BS_denote (proj1_sig x)).

Lemma NF_below x : BS_nf x -> BS_denote x < NFOrd.
Proof. intro Hx. apply (index_lt NFOrd (exist _ x Hx)). Qed.

(** A normal function taking notations below notations fixes the limit
    of the normal forms. *)
Lemma NF_closed G : normal_function G ->
  (forall x, BS_nf x -> exists y, BS_nf y /\ G (BS_denote x) ≤ BS_denote y) ->
  G NFOrd ≤ NFOrd.
Proof.
  intros HG HGn.
  set (s := fun x:{x:BSmall | BS_nf x} => succOrd (BS_denote (proj1_sig x))).
  assert (Hdir : directed _ s).
  { intros [x1 H1] [x2 H2].
    destruct (BS_add_reflects (BS_denote x1) x1 (conj (ord_eq_refl _) H1)
                              (BS_denote x2) x2 (conj (ord_eq_refl _) H2)) as [E N].
    exists (exist _ (BS_add x1 x2) N). unfold s; simpl. rewrite <- E.
    split; apply succ_monotone; [ apply addOrd_le1 | apply addOrd_le2 ]. }
  assert (Hc : forall a, complete (s a)) by (intro; apply succ_complete, BS_complete).
  assert (Hle : NFOrd ≤ supOrd s).
  { rewrite ord_le_unfold. intro a. eapply ord_lt_le_trans; [ apply succ_lt | apply (sup_le _ s a) ]. }
  transitivity (G (supOrd s)); [ apply normal_monotone; auto | ].
  eapply ord_le_trans; [ apply (normal_continuous G HG _ s (exist _ BZ I) Hdir Hc) | ].
  apply sup_least. intros [x Hx]. unfold s; simpl.
  destruct (BS_succ_reflects (BS_denote x) x (conj (ord_eq_refl _) Hx)) as [E N].
  destruct (HGn _ N) as [y [Hy Hyl]].
  transitivity (BS_denote y); [ | apply ord_lt_le, NF_below; auto ].
  rewrite <- Hyl. apply normal_monotone; auto. apply E.
Qed.

(** The normal forms have order type BHO₁. *)
Theorem BS_order_type : NFOrd ≈ BHO1.
Proof.
  split.
  - rewrite ord_le_unfold. intros [x Hx]. apply BS_bounded; auto.
  - unfold BHO1.
    change (cfe (addOrd 1) (nat + False) (bphi_fam (addOrd 1) btower (False_rect (Ord -> BOrd))) 0 ≤ NFOrd).
    destruct bεΩ1_good as [Hfam Hg].
    assert (HF := bphi_fam_normal' _ onePlus_normal _ _ _ _ Hg).
    apply (cfe_least (addOrd 1) onePlus_normal _ _ HF).
    + transitivity (BS_denote BS_one); [ apply (BS_denote_onePlus BZ) | ].
      apply ord_lt_le, NF_below, BS_one_nf.
    + apply limit_least. intros [].
    + assert (H1 : 1 + NFOrd ≤ NFOrd).
      { apply NF_closed; [ apply onePlus_normal | ].
        intros x Hx. destruct (BS_onePlus_reflects (BS_denote x) x (conj (ord_eq_refl _) Hx)) as [E N].
        exists (BS_onePlus x). split; auto. apply E. }
      intros [n|[]]. split; auto.
      apply NF_closed; [ apply (HF (inl n)) | ].
      intros x Hx.
      assert (Hp : BS_proper (BN (BI_tower n) x)) by (split; [ apply BI_tower_proper | apply (proj1 nf_proper); auto ]).
      exists (normS (BN (BI_tower n) x)). split; [ apply normS_nf; auto | ].
      rewrite (normS_equal _ Hp). simpl.
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (BI_bfam _))).
      apply bsub_tower.
Qed.

(** * Base change: BHO₁ is the Bachmann–Howard ordinal

φ^{1+x}_T ≤ φ^{ω^x}_T gives one direction.  For the other, φ^{ω^x}_T ≤
φ^{1+x}_{Ω+T}, and Ω + tower n lies z-reachably below tower (n+2),
so BHO₁ is closed under ω^x and every φ^{ω^x}_{tower n}. *)

Theorem BHO1_BachmannHoward : BHO1 ≈ BachmannHoward.
Proof.
  split.
  - apply bphi_base_mono; auto using bcd_bεΩ1, zero_complete.
  - unfold BachmannHoward.
    assert (Hg := bcd_good _ powOmega_normal _ bcd_bεΩ1).
    change (cfe powOmega (nat + False) (bphi_fam powOmega btower (False_rect (Ord -> BOrd))) 0 ≤ BHO1).
    assert (Hcomp : forall n, bphi powOmega (btower n) BHO1 ≤ BHO1).
    { intro n. rewrite (bphi_powOmega_shift _ (bcd_btower n) _ BHO1_complete).
      destruct bεΩ1_good as [Hfam1 Hg1].
      assert (Hgt : bgood (addOrd 1) (btower (S (S n)))) by (apply (bgood_small _ bεΩ1 (S (S n))); auto).
      assert (Hft : bfam (btower (S (S n)))) by (apply (bfam_small bεΩ1 Hfam1 (S (S n)))).
      apply (zlt_nest _ onePlus_normal _ _ (btower (S (S n))) (zlt_Ω_tower n _ BHO1_inf) Hgt Hft BHO1_complete).
      apply bfix_of_fix; auto using onePlus_normal, BHO1_complete.
      apply (bphi_fix_small' _ onePlus_normal bεΩ1 (S (S n)) 0 Hg1 zero_complete). }
    assert (Hpow : powOmega BHO1 ≤ BHO1).
    { transitivity (bphi powOmega (btower 0) BHO1); [ | apply Hcomp ].
      transitivity (bphi powOmega bzero BHO1); [ apply (bphi_bzero _ powOmega_normal) | ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ powOmega_normal) _ (bfam_btower 0))).
      apply bsub_bzero_l. }
    apply (cfe_least powOmega powOmega_normal _ _ (bphi_fam_normal' _ powOmega_normal _ _ _ _ Hg)).
    + transitivity (powOmega BHO1); auto. apply normal_monotone; [ apply powOmega_normal | apply zero_least ].
    + apply limit_least. intros [].
    + intros [n|[]]. split; [ apply Hcomp | exact Hpow ].
Qed.

Corollary BS_order_type_BH : NFOrd ≈ BachmannHoward.
Proof. rewrite BS_order_type. apply BHO1_BachmannHoward. Qed.

(** * The offset of a threshold

For a normal index R with a nonzero leading exponent and a normal
notation m, @BS_offset R m@ is the least t with m < φ_R(t): the least
value of φ_R above m is φ_R(t).  It is computed by recursion on m:
if m < φ_R(0) then t = 0; otherwise m = φ_{T'}(y') with
 - T' = R: t = y' + 1;
 - T' > R: if R's coefficients lie below m, m is a fixpoint of φ_R and
   t = m + 1; otherwise m = φ_R(0) and t = 1;
 - T' < R: the values of φ_R above max(y', coefficients of T') are the
   values above m, so recurse on that maximum. *)

Abbreviation PHI R := (bphi (addOrd 1) (BI_denote R)).

Definition lead_big (R:BIdx) : Prop :=
  match R with BIC e _ _ => e <> BIZ | BIZ => False end.

Lemma Ω_le_R R : BI_nf R -> lead_big R -> bsub bOmega (BI_denote R).
Proof.
  destruct R as [|e c r]; [ contradiction | ]. destruct e as [|e1 c1 r1]; [ contradiction | ].
  intros [He [_ [Hc0 _]]] _. destruct He as [_ [_ [Hc10 _]]].
  change (bsub bOmega (badd (bmul (bexpΩ (BI_denote (BIC e1 c1 r1))) (embed (BS_denote c))) (BI_denote r))).
  eapply bsub_trans; [ | apply bsub_le_badd ].
  eapply bsub_trans; [ | apply bsub_P_Pz; auto ].
  destruct (bsmall_mul_embed_inh (BI_denote e1) (BS_denote c1) Hc10) as [t].
  destruct (badd_small_l (bmul (bexpΩ (BI_denote e1)) (embed (BS_denote c1))) (BI_denote r1) t) as [a _].
  apply (Ω_le_bexp _ a).
Qed.

(** Common fixpoints of the components of such an R are additively principal. *)
Lemma fix_principal R z a : BI_nf R -> lead_big R -> complete z -> bfix (addOrd 1) (BI_denote R) z ->
  a < z -> a + z ≤ z.
Proof.
  intros HR Hl Hz Hfix Ha.
  assert (Ha' := Ha). rewrite ord_lt_unfold in Ha'. destruct Ha' as [j Hj].
  assert (Hc : complete (z j)) by (apply complete_subord; auto).
  transitivity (z j + z); [ apply addOrd_monotone; [ exact Hj | reflexivity ] | ].
  transitivity (expOrd ω (z j) + z); [ apply addOrd_monotone; [ apply le_expOmega | reflexivity ] | ].
  transitivity (bphi (addOrd 1) (embed (z j)) z); [ apply (proj2 (bphi_onePlus_embed _ _ Hc Hz)) | ].
  apply (zlt_nest _ onePlus_normal z (embed (z j)) (BI_denote R)); auto using BI_good, BI_bfam.
  apply zlt_mono_r with bOmega; [ apply zlt_embed_Ω, index_lt | apply Ω_le_R; auto ].
Qed.

Lemma fix_succ_lt R z a : BI_nf R -> lead_big R -> complete z -> bfix (addOrd 1) (BI_denote R) z ->
  a < z -> succOrd a < z.
Proof.
  intros HR Hl Hz Hfix Ha.
  assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hz (proj1 Hfix)).
  apply ord_le_lt_trans with (a + 1).
  { rewrite addOrd_succ. apply succ_monotone, addOrd_le1. }
  eapply ord_lt_le_trans; [ apply addOrd_increasing | apply (fix_principal R z a); auto ].
  apply ord_lt_le_trans with (natOrdSize 2); [ apply succ_lt | apply Hinf ].
Qed.

Definition off_max (y':BSmall) (T':BIdx) : BSmall :=
  match kmax (S (BI_size T' + BI_size T')) T' with
  | None => y'
  | Some k => match BS_compare k y' with LT => y' | _ => k end
  end.

Lemma off_max_spec T' y' : BS_nf (BN T' y') ->
  BS_nf (off_max y' T') /\ (BS_size (off_max y' T') < BS_size (BN T' y'))%nat /\
  BS_denote (off_max y' T') < BS_denote (BN T' y') /\
  (forall z, BS_denote (off_max y' T') < z -> BS_denote y' < z /\ Klt z T').
Proof.
  intro Hm. assert (Hm' := Hm). destruct Hm' as [HT' [Hy' [Hylt HK]]].
  assert (Hk := kmax_spec (S (BI_size T' + BI_size T')) T' HT' ltac:(lia)).
  unfold off_max. destruct (kmax (S (BI_size T' + BI_size T')) T') as [k|]; simpl in Hk.
  - destruct Hk as [Hkin HKle].
    assert (Hkn := Kin_nf k T' Hkin HT').
    assert (Hkm : BS_denote k < BS_denote (BN T' y')) by (apply (Kge_lt _ _ T' (Kin_Kge k T' Hkin) HK)).
    assert (Hks := Kin_size' k T' Hkin).
    assert (Hc := BS_compare_correct k y' Hkn Hy').
    destruct (BS_compare k y'); simpl in Hc.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; auto. apply Kle_lt with (BS_denote k); auto. eapply ord_lt_trans; eauto.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; [ rewrite <- Hc; auto | ]. apply Kle_lt with (BS_denote k); auto.
    + split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
      intros w Hw. split; [ eapply ord_lt_trans; eauto | ]. apply Kle_lt with (BS_denote k); auto.
  - subst T'. split; [ auto | split; [ simpl; lia | split; [ auto | ] ] ].
    intros w Hw. split; [ auto | exact I ].
Qed.

Definition offStep (rec:BSmall -> BSmall) (R:BIdx) (m:BSmall) : BSmall :=
  match m with
  | BZ => BZ
  | BN T' y' =>
    match cmpI (S (BI_size T' + BI_size R)) T' R with
    | EQ => BS_succ y'
    | LT => rec (off_max y' T')
    | GT => if coefs_below (S (BI_size R + BS_size m)) R m then BS_succ m else BS_one
    end
  end.

Fixpoint offN (fuel:nat) (R:BIdx) (m:BSmall) : BSmall :=
  match fuel with
  | O => BZ
  | S fuel' =>
    match BS_compare m (normS (BN R BZ)) with
    | LT => BZ
    | _ => offStep (offN fuel' R) R m
    end
  end.

Definition BS_offset (R:BIdx) (m:BSmall) : BSmall := offN (S (BS_size m)) R m.

Definition OffSpec (R:BIdx) (m t:BSmall) : Prop :=
  BS_nf t /\ BS_denote m < PHI R (BS_denote t) /\ BS_denote t < PHI R (BS_denote t) /\
  (forall z, complete z -> bfix (addOrd 1) (BI_denote R) z -> BS_denote m < z -> PHI R (BS_denote t) ≤ z).

Lemma Hinh_of T : BI_nf T -> T <> BIZ -> inhabited (bsmall (BI_denote T) + bbig (BI_denote T)).
Proof. destruct T as [|e c r]; [ tauto | ]. intros HT _. apply BI_inh, HT. Qed.

Section offset.
  Variable R : BIdx.
  Hypothesis HR : BI_nf R.
  Hypothesis HRl : lead_big R.

  Let HRpos : BI_pos R := BI_nf_pos R HR.
  Let Hinh : inhabited (bsmall (BI_denote R) + bbig (BI_denote R)).
  Proof. destruct R as [|e c r]; [ contradiction | ]. apply BI_inh, HR. Qed.

  Let Hvfix x : complete x -> bfix (addOrd 1) (BI_denote R) (PHI R x).
  Proof. intro Hx. apply bfix_value_full; auto using onePlus_normal, BI_good. Qed.

  Let Hvc x : complete x -> complete (PHI R x).
  Proof. intro Hx. apply normal_complete; auto using BI_normal. Qed.

  Let Hinc x y : complete y -> x < y -> PHI R x < PHI R y.
  Proof. intros. apply (normal_increasing _ (BI_normal R)); auto. Qed.

  (** If φ_R(a) lies below m, then φ_R(a+1) is the least common fixpoint above m. *)
  Let succ_case m a t : BS_nf t -> BS_denote t ≈ succOrd a -> complete a ->
    PHI R a ≤ BS_denote m -> BS_denote m < PHI R (succOrd a) -> OffSpec R m t.
  Proof.
    intros Ht Et Ha Hle Hlt.
    assert (E : PHI R (BS_denote t) ≈ PHI R (succOrd a)) by (apply ord_eq_normal; auto using BI_normal).
    split; [ exact Ht | split; [ rewrite E; exact Hlt | split ] ].
    - rewrite E, Et. apply (fix_succ_lt R); auto using succ_complete.
      eapply ord_le_lt_trans; [ | apply Hinc; [ apply succ_complete; auto | apply succ_lt ] ].
      apply normal_inflationary; auto using BI_normal.
    - intros z Hz Hfix Hmz. rewrite E.
      apply bphi_succ_le; auto using onePlus_normal, BI_good.
      eapply ord_le_lt_trans; eauto.
  Qed.

  Lemma offStep_correct rec m : BS_nf m -> PHI R 0 ≤ BS_denote m ->
    (forall m', BS_nf m' -> (BS_size m' < BS_size m)%nat -> OffSpec R m' (rec m')) ->
    OffSpec R m (offStep rec R m).
  Proof.
    intros Hm Hge IH.
    destruct m as [|T' y'].
    { elim (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ apply bphi_nonzero, onePlus_normal | exact Hge ]. }
    assert (Hm' := Hm). destruct Hm' as [HT' [Hy' [Hylt HK]]].
    unfold offStep.
    assert (Hc := proj2 (cmp_correct (S (BI_size T' + BI_size R))) T' R ltac:(lia) HT' HR).
    destruct (cmpI (S (BI_size T' + BI_size R)) T' R); simpl in Hc.
    - (* T' < R: recurse on the maximum of y' and the coefficients of T' *)
      destruct (off_max_spec T' y' Hm) as [Hmx [Hsz [Hlt Habove]]].
      destruct (IH _ Hmx Hsz) as [Nt [Hm1 [Ht1 Hmin]]].
      assert (Lz : forall z, complete z -> bfix (addOrd 1) (BI_denote R) z ->
                     BS_denote (off_max y' T') < z -> BS_denote (BN T' y') < z).
      { intros z Hz Hfix Hxz. destruct (Habove z Hxz) as [Hyz HKz].
        assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hz (proj1 Hfix)).
        assert (Hzlt := proj1 (nest z Hinf (S (BI_size T')) T' ltac:(lia) HT' HKz) R HR Hc).
        assert (Hfz := zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hz Hfix).
        eapply ord_lt_le_trans; [ | exact Hfz ].
        apply (normal_increasing _ (BI_normal T')); auto. }
      split; [ exact Nt | split; [ | split; [ exact Ht1 | ] ] ].
      + apply Lz; auto using BS_complete.
      + intros z Hz Hfix Hmz. apply Hmin; auto. exact (ord_lt_trans _ _ _ Hlt Hmz).
    - (* T' = R *)
      destruct (BS_succ_reflects (BS_denote y') y' (conj (ord_eq_refl _) Hy')) as [E1 N1].
      apply (succ_case _ (BS_denote y') _ N1 ltac:(symmetry; exact E1) (BS_complete y')).
      + apply (proj2 (bphi_ieq _ _ _ Hc)).
      + eapply ord_le_lt_trans; [ apply (proj1 (bphi_ieq _ _ _ Hc)) | ].
        apply Hinc; [ apply succ_complete, BS_complete | apply succ_lt ].
    - (* R < T' *)
      assert (HT'ne : T' <> BIZ) by (intro E; subst; inversion Hc).
      assert (Hcb := coefs_below_spec (S (BI_size R + BS_size (BN T' y'))) (BN T' y') R
                       (fun c Hs Hcn => proj1 (cmp_correct (S (BI_size R + BS_size (BN T' y')))) c (BN T' y') ltac:(lia) Hcn Hm) HR).
      destruct (coefs_below (S (BI_size R + BS_size (BN T' y'))) R (BN T' y')).
      + assert (HK' := proj1 Hcb eq_refl).
        assert (Hz := proj1 (nest _ (BN_inf T' y' HT' HT'ne) (S (BI_size R)) R ltac:(lia) HR HK') T' HT' Hc).
        assert (Hfix := zlt_value _ onePlus_normal _ _ (BS_denote y') Hz (BI_good T') (BI_bfam T')
                          (Hinh_of T' HT' HT'ne) (BS_complete y')).
        destruct (BS_succ_reflects _ _ (conj (ord_eq_refl _) Hm)) as [E1 N1].
        apply (succ_case _ (BS_denote (BN T' y')) _ N1 ltac:(symmetry; exact E1) (BS_complete _)).
        * exact Hfix.
        * eapply ord_le_lt_trans; [ apply normal_inflationary; auto using BI_normal, BS_complete | ].
          apply Hinc; [ apply succ_complete, BS_complete | apply succ_lt ].
      + assert (Hd := dominance R BZ _ HRpos (proj2 Hcb eq_refl)).
        apply (succ_case _ 0 _ BS_one_nf BS_one_denote zero_complete Hge).
        eapply ord_le_lt_trans; [ exact Hd | ].
        apply Hinc; [ apply succ_complete, zero_complete | apply succ_lt ].
  Qed.

  Theorem offN_correct : forall fuel m, (BS_size m < fuel)%nat -> BS_nf m -> OffSpec R m (offN fuel R m).
  Proof.
    induction fuel as [|fuel IH]; intros m Hsz Hm; [ lia | ].
    assert (Hp : BS_proper (BN R BZ)) by (split; [ apply (proj2 nf_proper); auto | exact I ]).
    assert (Hm0 := normS_nf _ Hp). assert (E0 := normS_equal _ Hp).
    assert (Hc := BS_compare_correct m _ Hm Hm0).
    change (OffSpec R m (match BS_compare m (normS (BN R BZ)) with
                         | LT => BZ | _ => offStep (offN fuel R) R m end)).
    destruct (BS_compare m (normS (BN R BZ))); cbv beta iota delta [ordering_correct] in Hc.
    - split; [ exact I | split; [ eapply ord_lt_le_trans; [ exact Hc | apply E0 ] | split ] ].
      + apply bphi_nonzero, onePlus_normal.
      + intros z Hz Hfix _. apply bphi_le_fix; auto using onePlus_normal, BI_good.
    - apply offStep_correct; auto.
      + transitivity (BS_denote (normS (BN R BZ))); [ apply E0 | apply Hc ].
      + intros m' Hm' Hs. apply IH; auto. lia.
    - apply offStep_correct; auto.
      + transitivity (BS_denote (normS (BN R BZ))); [ apply E0 | apply ord_lt_le, Hc ].
      + intros m' Hm' Hs. apply IH; auto. lia.
  Qed.

  Corollary BS_offset_correct m : BS_nf m -> OffSpec R m (BS_offset R m).
  Proof. intro Hm. apply offN_correct; auto. Qed.
End offset.

(** ** Examples, by computation *)

(** Above 1, the first ε-number is ε₀ = φ_Ω(0). *)
Example offset_one : BS_offset BI_Ω BS_one = BZ.
Proof. reflexivity. Qed.

(** Above ε₀ = φ_Ω(0), the next one is φ_Ω(1). *)
Example offset_eps0 : BS_offset BI_Ω (BN BI_Ω BZ) = BS_succ BZ.
Proof. reflexivity. Qed.

(** Above ε₀ + 1 = ω^{ε₀} + 1, still φ_Ω(1). *)
Example offset_eps0_plus1 : BS_offset BI_Ω BS_ε0_plus1 = BS_succ BZ.
Proof. reflexivity. Qed.

(** φ_{Ω·2}(0) is a fixpoint of φ_Ω, so the least φ_Ω-value above it is φ_Ω(φ_{Ω·2}(0) + 1). *)
Example offset_fix : BS_offset BI_Ω (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ) =
                     BS_succ (BN (BIC BI_one (BN BIZ BS_one) BIZ) BZ).
Proof. reflexivity. Qed.

(** * One absorption step

P = Ω^e·c is a normal summand and R a normal index whose leading
exponent exceeds e.  The index P + R is improper.  Its common
fixpoints are those of R that lie above the coefficients of P, so
φ_{P+R}(y) = φ_R(t + y) with t = BS_offset R m, m the largest
coefficient of P. *)

Definition lead_gt (R:BIdx) (e:BIdx) : Prop :=
  match R with BIC e' _ _ => ilt e e' | BIZ => False end.

Section absorb.
  Variables (e:BIdx) (c:BSmall) (R:BIdx).
  Hypothesis HP : BI_nf (BIC e c BIZ).
  Hypothesis HR : BI_nf R.
  Hypothesis HRe : lead_gt R e.

  Let P := BIC e c BIZ.
  Let X := BIC e c R.

  Lemma R_lead_big : lead_big R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. simpl in *. intro E; subst. inversion HRe. Qed.

  Lemma X_pos : BI_pos X.
  Proof. destruct HP as [_ [_ [Hc0 _]]]. simpl. split; [ apply BI_nf_pos, HP | split; auto ]. apply BI_nf_pos; auto. Qed.

  Lemma X_inh : inhabited (bsmall (BI_denote X) + bbig (BI_denote X)).
  Proof. apply BI_inh, HP. Qed.

  (** (⊆) Every common fixpoint for P + R is one for R: R's children
      sit below P + (R's children). *)
  Lemma absorb_sub z : complete z -> bfix (addOrd 1) (BI_denote X) z -> bfix (addOrd 1) (BI_denote R) z.
  Proof.
    intros Hz [H1 [H2 H3]]. split; [ exact H1 | split ].
    - intro a. destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a) as [k Hk].
      eapply ord_le_trans; [ | exact (H2 k) ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (bfam_small _ (BI_bfam X) k))).
      change (bsmallSz (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) k) with
        (bsmallSz (BI_denote X) k) in Hk.
      rewrite Hk. apply bsub_absorb.
    - intro d. destruct (badd_big_r (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d) as [k Hk].
      eapply ord_le_trans; [ | exact (H3 k) ].
      apply (proj2 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (bfam_big _ (BI_bfam X) k z))).
      change (bbigSz (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) k z) with
        (bbigSz (BI_denote X) k z). rewrite Hk. apply bsub_absorb.
  Qed.

  (** The values of φ_{P+R} lie above the coefficients of P, which occur
      at positions that are not the end. *)
  Lemma absorb_region y : complete y -> Klt (PHI X y) P.
  Proof.
    intro Hy. apply Klt_of_Kge. intros z Hz.
    assert (HK : Kgs z X).
    { destruct R as [|e' c' r']; [ contradiction | ]. simpl in Hz |- *.
      destruct Hz as [H|[H|[]]]; auto. }
    destruct (Kgs_ctx X X_pos _ HK) as [C [ζ [HC [Hζ [Hzζ Hlt]]]]].
    apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
    - transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
    - eapply ord_lt_le_trans; [ apply (bphi_strict (addOrd 1) onePlus_normal _ (BI_denote X) Hlt (BI_good X) (BI_bfam X)) | ].
      apply (proj1 (bphi_mono_index _ (normal_monotone _ onePlus_normal) _ (BI_bfam X))). apply zero_least.
  Qed.

  Let n0 := S (BI_size P + BI_size P).
  Definition absorb_max : BSmall := match kmax n0 P with Some k => k | None => BZ end.

  Lemma absorb_max_spec : BS_nf absorb_max /\ Kin absorb_max P /\ Kle (BS_denote absorb_max) P.
  Proof.
    assert (H := kmax_spec n0 P HP ltac:(unfold n0; lia)).
    unfold absorb_max. destruct (kmax n0 P) as [k|]; simpl in H; [ | discriminate ].
    destruct H as [H1 H2]. split; [ apply (Kin_nf k P H1 HP) | split; auto ].
  Qed.

  Definition absorb_offset : BSmall := BS_offset R absorb_max.

  (** The hard direction, at notation values: common fixpoints for R above
      the coefficients of P are common fixpoints for P + R.  Assumed here;
      see BachmannImproperPlan.md for the status of its proof. *)
  Hypothesis ABS : forall s, BS_nf s -> Klt (PHI R (BS_denote s)) P ->
    bfix (addOrd 1) (BI_denote X) (PHI R (BS_denote s)).

  Theorem absorb_enum : forall y, BS_nf y ->
    PHI X (BS_denote y) ≈ PHI R (BS_denote absorb_offset + BS_denote y).
  Proof.
    destruct absorb_max_spec as [Hm [Hmin HmK]].
    destruct (BS_offset_correct R HR R_lead_big _ Hm) as [Nt [Hmt [Htt Hleast]]].
    fold absorb_offset in Nt, Hmt, Htt, Hleast.
    set (t := absorb_offset) in *.
    assert (Htc := BS_complete t).
    assert (Hgx := BI_good X). assert (Hgr := BI_good R).
    intro y. induction y as [y IH] using (size_induction (ord BSmall BS_denote)). intro Hy.
    assert (HIy := BS_has_all_interpolants y Hy).
    assert (Hyc := BS_complete y).
    destruct (BS_add_reflects _ t (conj (ord_eq_refl _) Nt) _ y (conj (ord_eq_refl _) Hy)) as [Es Ns].
    set (s := BS_add t y) in *.
    assert (EPs : PHI R (BS_denote s) ≈ PHI R (BS_denote t + BS_denote y))
      by (apply ord_eq_normal; [ apply BI_normal | symmetry; exact Es ]).
    assert (Hsc := BS_complete s).
    rewrite <- EPs. split.
    - rewrite (bphi_unfold _ (BI_denote X)).
      apply (cfe_least (addOrd 1) onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgx)).
      + transitivity (1 + BS_denote s); [ | apply bphi_ge_f ].
        apply onePlus_mono. rewrite <- Es. apply addOrd_le2.
      + apply limit_least. intro j. cbv beta. rewrite <- bphi_unfold.
        destruct (HI_below _ _ HIy (index_lt _ j)) as [n [Hn [HIn [Hjn Hny]]]].
        eapply ord_le_lt_trans; [ apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam X))); exact Hjn | ].
        rewrite (IH n Hny Hn).
        eapply ord_lt_le_trans; [ | apply (proj2 EPs) ].
        apply (normal_increasing _ (BI_normal R)); [ apply addOrd_complete; auto | ].
        apply addOrd_increasing; auto.
      + assert (HK : Klt (PHI R (BS_denote s)) P).
        { apply Kle_lt with (BS_denote absorb_max); auto.
          eapply ord_lt_le_trans; [ exact Hmt | ].
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam R))).
          rewrite <- Es. apply addOrd_le1. }
        destruct (ABS s Ns HK) as [H1 [H2 H3]].
        intros [k|k]; cbn [bphi_fam]; split; auto.
    - set (z := PHI X (BS_denote y)).
      assert (Hzc : complete z) by (apply BS_complete with (x := BN X y)).
      assert (Hzfix := absorb_sub z Hzc (bfix_value_full _ onePlus_normal _ _ Hgx X_inh Hyc)).
      assert (Hreg := absorb_region _ Hyc). fold z in Hreg.
      assert (Hmz : BS_denote absorb_max < z) by (apply (Kge_lt _ _ P (Kin_Kge _ _ Hmin) Hreg)).
      assert (Hlz := Hleast z Hzc Hzfix Hmz).
      assert (Htz : BS_denote t < z) by (eapply ord_lt_le_trans; eauto).
      assert (Hpr := fix_principal R z _ HR R_lead_big Hzc Hzfix Htz).
      rewrite (bphi_unfold _ (BI_denote R)).
      apply (cfe_least (addOrd 1) onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ Hgr)).
      + transitivity (1 + z); [ apply onePlus_mono | apply Hzfix ].
        rewrite <- Es. rewrite <- Hpr. apply addOrd_monotone; [ reflexivity | ].
        apply normal_inflationary; auto using BI_normal.
      + apply limit_least. intro j. cbv beta. rewrite <- bphi_unfold.
        assert (Hj : BS_denote s j < BS_denote t + BS_denote y)
          by (eapply ord_lt_le_trans; [ apply index_lt | apply (proj2 Es) ]).
        assert (Hjc : complete (BS_denote s j)) by (apply complete_subord; auto).
        destruct (addOrd_lt_cases _ _ _ Hj) as [Ha|[j0 Ha]].
        * eapply ord_lt_le_trans; [ | exact Hlz ]. apply (normal_increasing _ (BI_normal R)); auto.
        * destruct (HI_below _ _ HIy (index_lt _ j0)) as [n [Hn [HIn [Hjn Hny]]]].
          apply ord_le_lt_trans with (PHI R (BS_denote t + BS_denote n)).
          { apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam R))).
            rewrite Ha. apply addOrd_monotone; [ reflexivity | exact Hjn ]. }
          rewrite <- (IH n Hny Hn).
          apply (normal_increasing _ (BI_normal X)); auto.
      + destruct Hzfix as [H1 [H2 H3]].
        intros [k|k]; cbn [bphi_fam]; split; auto.
  Qed.
End absorb.

(** ** The hard direction of absorption *)

Lemma bfix_eq T z z' : bgood (addOrd 1) T -> bfam T -> z ≈ z' ->
  bfix (addOrd 1) T z -> bfix (addOrd 1) T z'.
Proof.
  intros Hg Hf E [H1 [H2 H3]]. split; [ | split ].
  - transitivity (1 + z); [ apply onePlus_mono, E | transitivity z; [ exact H1 | apply E ] ].
  - intro a. transitivity (bphi (addOrd 1) (bsmallSz T a) z).
    + apply (proj1 (bphi_mono_index _ onePlus_mono _ (bfam_small _ Hf a))). apply E.
    + transitivity z; [ exact (H2 a) | apply E ].
  - intro d. transitivity (bphi (addOrd 1) (bbigSz T d z) 0).
    + apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_big _ Hf d z))).
      apply bfam_fam; auto. apply E.
    + transitivity z; [ exact (H3 d) | apply E ].
Qed.

Lemma Kgs_lt T k : BI_pos T -> Kgs k T -> k < PHI T 0.
Proof.
  intros HT HK. destruct (Kgs_ctx T HT _ HK) as [C [ζ [HC [Hζ [Hkζ Hlt]]]]].
  apply ord_le_lt_trans with (bphi (addOrd 1) (C ζ) 0).
  - transitivity ζ; auto. apply (bctx_dom (addOrd 1) onePlus_normal C HC ζ Hζ).
  - apply (bphi_strict (addOrd 1) onePlus_normal _ _ Hlt (BI_good T) (BI_bfam T)).
Qed.

Lemma Kend_of T z : BI_nf T -> (forall k, Kge k T -> k ≤ z) -> (forall k, Kgs k T -> k < z) -> Kend z T.
Proof.
  induction T as [|e IHe c r IHr]; intros HT H1 H2; [ exact I | ].
  destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
  destruct r as [|e2 c2 r2].
  - assert (Hcmp := BS_compare_correct c BS_one Hc BS_one_nf).
    destruct (BS_compare c BS_one); cbv beta iota delta [ordering_correct] in Hcmp.
    + exfalso. rewrite BS_one_denote in Hcmp. rewrite ord_lt_unfold in Hcmp. destruct Hcmp as [u Hle].
      apply (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hc0 | exact Hle ].
    + right. split; [ | rewrite Hcmp; apply BS_one_denote ].
      apply IHe; auto.
      * intros k Hk. apply H1. simpl. auto.
      * intros k Hk. apply H2. simpl. right. split; auto. rewrite Hcmp; apply BS_one_denote.
    + left. split.
      * apply Klt_of_Kge. intros k Hk. apply H2. simpl. left. split; auto.
        rewrite <- BS_one_denote. exact Hcmp.
      * apply H1. simpl. right. left. reflexivity.
  - split; [ | split ].
    + apply Klt_of_Kge. intros k Hk. apply H2. simpl. auto.
    + apply H2. simpl. right. left. reflexivity.
    + apply IHr; auto.
      * intros k Hk. apply H1. simpl. auto.
      * intros k Hk. apply H2. simpl. auto.
Qed.

(** Coefficients of T lie below z except at the end, when φ_T(0) ≤ z. *)
Lemma Kend_of_value T z : BI_nf T -> PHI T 0 ≤ z -> Kend z T.
Proof.
  intros HT Hz. apply Kend_of; auto.
  - intros k Hk. rewrite <- Hz. apply (dominance T BZ k (BI_nf_pos T HT) Hk).
  - intros k Hk. eapply ord_lt_le_trans; [ apply (Kgs_lt T k (BI_nf_pos T HT) Hk) | exact Hz ].
Qed.

Lemma Klt_of_value T z : BI_nf T -> PHI T 0 < z -> Klt z T.
Proof.
  intros HT Hz. apply Klt_of_Kge. intros k Hk.
  eapply ord_le_lt_trans; [ apply (dominance T BZ k (BI_nf_pos T HT) Hk) | exact Hz ].
Qed.

Section abs_all.
  Variables (e:BIdx) (c:BSmall).
  Hypothesis HP : BI_nf (BIC e c BIZ).

  Definition ABSw (R:BIdx) : Prop := forall w, BS_nf w ->
    bfix (addOrd 1) (BI_denote R) (BS_denote w) -> Klt (BS_denote w) (BIC e c BIZ) ->
    bfix (addOrd 1) (BI_denote (BIC e c R)) (BS_denote w).

  Lemma lead_gt_big R : lead_gt R e -> lead_big R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. simpl. intros H E. subst. inversion H. Qed.

  Lemma lead_gt_ilt R c'' r'' : lead_gt R e -> ilt (BIC e c'' r'') R.
  Proof. destruct R as [|e' c' r']; [ contradiction | ]. intro H. apply ilt_exp, H. Qed.

  Lemma ABSw_ABS R : BI_nf R -> lead_gt R e -> ABSw R ->
    forall s, BS_nf s -> Klt (PHI R (BS_denote s)) (BIC e c BIZ) ->
    bfix (addOrd 1) (BI_denote (BIC e c R)) (PHI R (BS_denote s)).
  Proof.
    intros HR HRe HA s Hs HK.
    assert (Hp := nf_BN_proper R s HR Hs).
    assert (Ew : BS_denote (normS (BN R s)) ≈ PHI R (BS_denote s)) by (apply normS_equal; auto).
    assert (Hne : R <> BIZ) by (intro E; subst; contradiction).
    apply bfix_eq with (BS_denote (normS (BN R s))); auto using BI_good, BI_bfam.
    apply HA; [ apply normS_nf; auto | | ].
    - apply bfix_eq with (PHI R (BS_denote s)); auto using BI_good, BI_bfam.
      + symmetry; auto.
      + apply bfix_value_full; auto using onePlus_normal, BI_good, BS_complete. apply Hinh_of; auto.
    - apply Klt_mono with (PHI R (BS_denote s)); auto. apply Ew.
  Qed.

  Theorem ABS_all : forall U R, ble (BI_denote R) U -> BI_nf R -> lead_gt R e -> ABSw R.
  Proof.
    intro U. induction U as [U IHU] using (well_founded_induction blt_wf).
    intros R HU HR HRe w Hw Hfix HK.
    assert (HP' := HP). destruct HP' as [He [Hc [Hc0 _]]].
    set (z := BS_denote w) in *.
    assert (Hzc : complete z) by apply BS_complete.
    assert (Hinf := fix_onePlus_finite _ onePlus_normal z Hzc (proj1 Hfix)).
    assert (Hz0 : 0 < z) by (apply ord_lt_le_trans with (natOrdSize 1); [ apply succ_lt | apply Hinf ]).
    assert (Hprin : forall a, a < z -> a + z ≤ z)
      by (intros; apply (fix_principal R z); auto; apply lead_gt_big; auto).
    assert (HKendR : Kend z R).
    { apply Kend_of_value; auto. apply bphi_le_fix; auto using onePlus_normal, BI_good. }
    assert (HKe : Klt z e) by apply HK.
    assert (Hcz : BS_denote c < z) by apply HK.
    (* P fixes z, by nesting *)
    assert (HPz : PHI (BIC e c BIZ) z ≤ z).
    { assert (Hzlt := proj1 (nest z Hinf (S (BI_size (BIC e c BIZ))) (BIC e c BIZ) ltac:(lia) HP HK) R HR
                       (lead_gt_ilt R c BIZ HRe)).
      apply (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hzc Hfix). }
    assert (HfixP := bfix_of_fix _ onePlus_normal _ z (BI_good _) (BI_bfam _) Hzc HPz).
    (* nesting for a normal N below R *)
    assert (Nest : forall N, BI_nf N -> ilt N R -> Klt z N -> PHI N z ≤ z).
    { intros N HN Hlt HKN.
      assert (Hzlt := proj1 (nest z Hinf (S (BI_size N)) N ltac:(lia) HN HKN) R HR Hlt).
      apply (zlt_nest _ onePlus_normal z _ _ Hzlt (BI_good R) (BI_bfam R) Hzc Hfix). }
    assert (NestLe : forall N, BI_nf N -> ilt N R -> Kend z N -> PHI N 0 ≤ z).
    { intros N HN Hlt HKN.
      assert (HB := proj1 (nest_le z Hinf (S (BI_size N)) N ltac:(lia) HN HKN) R HR HKendR Hlt).
      apply (bleZ_sound _ onePlus_normal z _ _ HB (BI_denote R) (bsub_refl _) (BI_good R) (BI_bfam R) Hzc Hfix). }
    (* the classification of P + K' for a normal K' below R *)
    assert (Hcls : forall K', BI_nf K' -> blt (BI_denote K') (BI_denote R) -> bfix (addOrd 1) (BI_denote K') z ->
              (PHI K' z ≤ z -> PHI (BIC e c K') z ≤ z) /\ PHI (BIC e c K') 0 ≤ z).
    { intros K' HK' Hblt HfK.
      assert (HK'0 : PHI K' 0 ≤ z) by (apply bphi_le_fix; auto using onePlus_normal, BI_good).
      assert (HKendK := Kend_of_value K' z HK' HK'0).
      destruct K' as [|e2 c2 r2].
      { split; [ intros _; exact HPz | ].
        eapply ord_le_trans; [ | exact HPz ].
        apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam _))). apply zero_least. }
      assert (HK'' := HK'). destruct HK'' as [He2 [Hc2 [Hc20 [Hr2 Hl2]]]].
      assert (Hsmall_Klt : PHI (BIC e2 c2 r2) z ≤ z -> Klt z (BIC e2 c2 r2)).
      { intro H. apply Klt_of_value; auto. eapply ord_lt_le_trans; [ | exact H ].
        apply (normal_increasing _ (BI_normal _)); auto. }
      assert (Hcmp := proj2 (cmp_correct (S (BI_size e2 + BI_size e))) e2 e ltac:(lia) He2 He).
      destruct (cmpI (S (BI_size e2 + BI_size e)) e2 e); simpl in Hcmp.
      - (* lead(K') < e: P + K' is normal *)
        assert (HN : BI_nf (BIC e c (BIC e2 c2 r2))) by (repeat split; auto).
        split.
        + intro H. apply Nest; auto using lead_gt_ilt. split; [ exact HKe | split; [ exact Hcz | auto ] ].
        + apply NestLe; auto using lead_gt_ilt. split; [ exact HKe | split; [ exact Hcz | exact HKendK ] ].
      - (* lead(K') = e: merge the coefficients *)
        destruct (BS_add_reflects _ c (conj (ord_eq_refl _) Hc) _ c2 (conj (ord_eq_refl _) Hc2)) as [Ea Na].
        set (N := BIC e (BS_add c c2) r2).
        assert (HN : BI_nf N).
        { split; [ exact He | split; [ exact Na | split; [ | split; [ exact Hr2 | ] ] ] ].
          - rewrite <- Ea. eapply ord_lt_le_trans; [ exact Hc0 | apply addOrd_le1 ].
          - apply (lead_below_ieq r2 r2 e2 e); auto using ieq_refl. }
        assert (Heq : bequiv (BI_denote (BIC e c (BIC e2 c2 r2))) (BI_denote N)).
        { change (bequiv (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                              (badd (bmul (bexpΩ (BI_denote e2)) (embed (BS_denote c2))) (BI_denote r2)))
                         (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote (BS_add c c2)))) (BI_denote r2))).
          apply bequiv_trans with (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c)))
                     (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c2))) (BI_denote r2))).
          { apply bequiv_badd; [ apply bequiv_refl | ].
            apply bequiv_badd; [ | apply bequiv_refl ].
            apply bequiv_bmul; [ apply bequiv_bexpΩ, ieq_bequiv; auto | apply bequiv_refl ]. }
          eapply bequiv_trans; [ apply bequiv_merge | ].
          apply bequiv_badd; [ | apply bequiv_refl ].
          apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_embed; auto ]. }
        assert (EN : forall y, PHI (BIC e c (BIC e2 c2 r2)) y ≈ PHI N y)
          by (intro y; apply bphi_bequiv; auto using onePlus_mono, BI_bfam).
        split.
        + intro H. rewrite EN. apply Nest; [ exact HN | apply lead_gt_ilt; auto | ].
          destruct (Hsmall_Klt H) as [HKe2 [Hc2z HKr2]].
          unfold N. split; [ exact HKe | split; [ | exact HKr2 ] ].
          rewrite <- Ea. eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hprin; auto ].
        + rewrite EN. apply NestLe; [ exact HN | apply lead_gt_ilt; auto | ].
          assert (Hc2le : BS_denote c2 ≤ z).
          { destruct r2 as [|e3 c3 r3]; simpl in HKendK.
            - destruct HKendK as [[_ H]|[_ H]]; auto. rewrite H. apply (Hinf 1%nat).
            - apply ord_lt_le, HKendK. }
          assert (Hsum : BS_denote (BS_add c c2) ≤ z).
          { rewrite <- Ea. rewrite <- (Hprin _ Hcz). apply addOrd_monotone; [ reflexivity | exact Hc2le ]. }
          unfold N. destruct r2 as [|e3 c3 r3].
          * left. split; auto.
          * simpl in HKendK. destruct HKendK as [_ [Hc2z HKr3]].
            split; [ exact HKe | split; [ | exact HKr3 ] ].
            rewrite <- Ea. eapply ord_lt_le_trans; [ apply addOrd_increasing; exact Hc2z | apply Hprin; auto ].
      - (* lead(K') > e: absorption with a smaller R-part *)
        assert (Hgt : lead_gt (BIC e2 c2 r2) e) by exact Hcmp.
        assert (HA : ABSw (BIC e2 c2 r2)).
        { apply (IHU (BI_denote (BIC e2 c2 r2))); auto using ble_refl.
          apply blt_le_trans with (BI_denote R); auto. }
        split.
        + intro H.
          assert (Eabs := absorb_enum e c _ HP HK' Hgt (ABSw_ABS _ HK' Hgt HA) w Hw).
          fold z in Eabs. rewrite Eabs.
          destruct (absorb_max_spec e c HP) as [Hm [Hmin _]].
          destruct (BS_offset_correct _ HK' (lead_gt_big _ Hgt) _ Hm) as [Nt [_ [Htt Hleast]]].
          assert (Hmz : BS_denote (absorb_max e c) < z) by (apply (Kge_lt _ _ _ (Kin_Kge _ _ Hmin) HK)).
          assert (Htz : BS_denote (absorb_offset e c (BIC e2 c2 r2)) < z).
          { eapply ord_lt_le_trans; [ exact Htt | apply Hleast; auto ]. }
          eapply ord_le_trans; [ | exact H ].
          apply (proj1 (bphi_mono_index _ onePlus_mono _ (BI_bfam _))). apply Hprin; auto.
        + apply bphi_le_fix; auto using onePlus_normal, BI_good. apply HA; auto. }
    (* now the components of P + R *)
    destruct (cover R HR (proj2 notation_KHI R HR)) as [CS CF].
    assert (HIw := proj1 notation_KHI w Hw).
    destruct HfixP as [_ [HP2 HP3]].
    destruct Hfix as [Hf1 [Hf2 Hf3]].
    split; [ exact Hf1 | split ].
    - intro a.
      change (BI_denote (BIC e c R)) with
        (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) in a |- *.
      destruct (badd_small_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) a)
        as [[a' E]|[b E]]; rewrite E.
      + destruct (badd_small_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero a') as [k Ek].
        specialize (HP2 k). change (BI_denote (BIC e c BIZ)) with
          (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero) in HP2.
        rewrite Ek in HP2. exact HP2.
      + destruct (CS b) as [K' [HK' [_ [_ [Hlo [b' Hup]]]]]].
        assert (HK'z : PHI K' z ≤ z).
        { eapply ord_le_trans; [ | exact (Hf2 b') ].
          apply (proj2 (bphi_mono_index _ onePlus_mono _ (bfam_small _ (BI_bfam R) b'))); auto. }
        assert (Hblt : blt (BI_denote K') (BI_denote R)) by (apply (bsub_child_blt _ _ (inl b')); auto).
        assert (HfK := bfix_of_fix _ onePlus_normal _ z (BI_good K') (BI_bfam K') Hzc HK'z).
        eapply ord_le_trans; [ | apply (proj1 (Hcls K' HK' Hblt HfK)); exact HK'z ].
        apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K')))).
        apply bsub_badd_r; auto.
    - intro d.
      change (BI_denote (BIC e c R)) with
        (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R)) in d |- *.
      destruct (badd_big_cases (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote R) d)
        as [[d' E]|[d' E]]; rewrite E.
      + destruct (badd_big_l (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero d') as [k Ek].
        specialize (HP3 k). change (BI_denote (BIC e c BIZ)) with
          (badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) bzero) in HP3.
        rewrite Ek in HP3. exact HP3.
      + destruct (CF d' w Hw HIw) as [K' [HK' [_ [_ [Hlo [d'' Hup]]]]]].
        fold z in Hlo, Hup.
        assert (Hmem := bfix_member _ onePlus_normal _ d'' z (BI_good R) (BI_bfam R) Hzc (Hf3 d'')).
        assert (HfK := bfix_bsub _ onePlus_normal _ _ z Hup (bfam_big _ (BI_bfam R) d'' z) Hmem).
        assert (Hblt : blt (BI_denote K') (BI_denote R)) by (apply (bsub_child_blt _ _ (inr (d'', z))); auto).
        eapply ord_le_trans; [ | apply (proj2 (Hcls K' HK' Hblt HfK)) ].
        apply (proj2 (bphi_mono_index _ onePlus_mono _ (BI_bfam (BIC e c K')))).
        apply bsub_badd_r; auto.
  Qed.

  (** Absorption, unconditionally. *)
  Theorem absorb : forall R, BI_nf R -> lead_gt R e -> forall y, BS_nf y ->
    PHI (BIC e c R) (BS_denote y) ≈ PHI R (BS_denote (absorb_offset e c R) + BS_denote y).
  Proof.
    intros R HR HRe. apply absorb_enum; auto.
    apply ABSw_ABS; auto. apply (ABS_all (BI_denote R)); auto using ble_refl.
  Qed.
End abs_all.

(** Example: the index 1 + Ω (= Ω^0·1 + Ω) absorbs into Ω with offset 0,
    since ε₀ = φ_Ω(0) already exceeds 1: φ_{1+Ω}(y) = φ_Ω(0 + y). *)
Example absorb_offset_one_Ω : absorb_offset BIZ BS_one BI_Ω = BZ.
Proof. reflexivity. Qed.

(** With coefficient ε₀ = φ_Ω(0) the threshold is ε₀ itself, so the offset
    is 1: φ_{ε₀+Ω}(y) = φ_Ω(1 + y). *)
Example absorb_offset_eps0_Ω : absorb_offset BIZ (BN BI_Ω BZ) BI_Ω = BS_succ BZ.
Proof. reflexivity. Qed.

