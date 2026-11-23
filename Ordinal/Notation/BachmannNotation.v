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
@bach f (T + ξ) 0@ is @veblen G ξ 0@, not @G ξ@.

** Layout of the development

- @BachmannNotation.v@: syntax, denotation, normal forms, the
  comparison algorithm and its correctness (this file).
- @BachmannFragment.v@: Schütte's Klammersymbols embed as the indices
  below Ω^Ω; the fragment has order type the Large Veblen Ordinal.
- @BachmannCantor.v@: Cantor decomposition, hence the arithmetic.
- @BachmannBound.v@: every normal form lies below the Bachmann–Howard
  ordinal; dominance of coefficients.
- @BachmannNormalize.v@: normalization of proper terms by rewriting
  (strong normalization, confluence).
- @BachmannInterpolants.v@: fundamental sequences and interpolants.
- @BachmannOrderType.v@: natural product; the normal forms have order
  type the Bachmann–Howard ordinal.
- @BachmannAbsorb.v@: offsets and absorption of the leading summand.
- @BachmannImproper.v@: hereditary absorption and the normalizer
  @normSX@ for improper terms; every notation lies below BHO₁. *)

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

Lemma ord_eq_normal G : normal_function G -> forall x y, x ≈ y -> G x ≈ G y.
Proof. intros HG x y [H1 H2]; split; apply normal_monotone; auto. Qed.

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
