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
