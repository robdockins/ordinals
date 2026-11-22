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

Theorem nest_le z : oinf z -> forall n T, (BI_size T < n)%nat -> BI_nf T -> Kend z T ->
  (forall T', BI_nf T' -> Klt z T' -> ilt T T' -> bleZ z (BI_denote T) (BI_denote T')) /\
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
    - intro HK2. apply (proj1 (IH e2 ltac:(lia) He2 HK2)); auto. }
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
  - simpl in Hsz. destruct HKT' as [HKe' _]. destruct HT' as [He' [_ [Hc0' _]]].
    assert (HTe := proj1 HT).
    eapply bleZ_mono_r; [ apply (B (BI_denote e')) | ].
    + split.
      * intro HKe. apply (proj1 (nest z Hz (S (BI_size e)) e ltac:(lia) HTe HKe)); auto.
      * intro HKe. apply (proj1 (IH e ltac:(lia) HTe HKe)); auto.
    + rewrite BI_denote_cons. eapply bsub_trans; [ apply bsub_P_Pz, Hc0' | apply bsub_le_badd ].
  - simpl in Hsz. destruct HKT' as [HKe' [Hcz' HKr']]. destruct HT as [He [Hc [Hc0 [Hr Hl]]]].
    assert (HKe := Klt_ieq z e e' Hee HKe').
    assert (Hcz : BS_denote c < z) by (eapply ord_lt_trans; eauto).
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
    destruct HKT' as [_ [_ HKr']].
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
        assert (HB := proj1 (nest_le _ Hz (S (BI_size T)) T ltac:(lia) HT (N1 eq_refl)) Tm HTm HKm HI).
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
