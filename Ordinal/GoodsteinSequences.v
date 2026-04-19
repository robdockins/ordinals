From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Reflection.

Lemma base_term_lt_lemma1 base e1 n1 x1 e2 n2 x2:
  (1 < base)%N ->
  (0 < n1 < base)%N ->
  (0 < n2 < base)%N ->
  (x1 < base^e1)%N ->
  (e1 < e2)%N ->
  (base^e1 * n1 + x1 < base^e2 * n2 + x2)%N.
Proof.
  intros.
  apply N.lt_le_trans with (base ^ e2  * n2)%N; [| lia].
  apply N.lt_le_trans with (base ^ e2 * 1)%N.
  2: { apply N.mul_le_mono_l. lia. }
  ring_simplify.
  apply N.lt_le_trans with (base ^ N.succ e1)%N.
  2: { apply N.pow_le_mono_r; lia. }
  rewrite N.pow_succ_r'.
  apply N.lt_le_trans with (base^e1 * (N.pred base) + base^e1)%N; [|lia].
  apply N.add_le_lt_mono; auto.
  apply N.mul_le_mono_l; lia.
Qed.  

Lemma base_term_lt_lemma2 base e1 n1 x1 e2 n2 x2:
  (1 < base)%N ->
  (0 < n1 < base)%N ->
  (0 < n2 < base)%N ->
  (x1 < base^e1)%N ->
  (e1 = e2)%N ->
  (n1 < n2)%N ->
  (base^e1 * n1 + x1 < base^e2 * n2 + x2)%N.
Proof.
  intros. subst.
  apply N.lt_le_trans with (base^e2 * n2)%N; [|lia].
  apply N.lt_le_trans with (base^e2 * N.succ n1)%N.
  2:{ apply N.mul_le_mono_l. lia. }
  rewrite N.mul_succ_r.
  apply N.add_le_lt_mono; auto; lia.
Qed.  

Lemma base_term_eq_lemma base e1 n1 x1 e2 n2 x2:
  (1 < base)%N ->
  (0 < n1 < base)%N ->
  (0 < n2 < base)%N ->
  (x1 < base^e1)%N ->
  (x2 < base^e2)%N ->

  (base^e1 * n1 + x1 = base^e2 * n2 + x2)%N ->
  e1 = e2 /\ n1 = n2 /\ x1 = x2.
Proof.
  intros.
  destruct (N.le_gt_cases e1 e2).
  2:{ assert ((base ^ e2 * n2 + x2) < (base ^ e1 * n1 + x1))%N.
      apply base_term_lt_lemma1; auto.
      lia. }
  destruct (N.le_gt_cases e2 e1).
  2:{ assert ((base ^ e1 * n1 + x1) < (base ^ e2 * n2 + x2))%N.
      apply base_term_lt_lemma1; auto.
      lia. }
  assert (e1 = e2) by lia.
  destruct (N.le_gt_cases n1 n2).
  2:{ assert ((base ^ e2 * n2 + x2) < (base ^ e1 * n1 + x1))%N.
      apply base_term_lt_lemma2; auto.
      lia. }
  destruct (N.le_gt_cases n2 n1).
  2:{ assert ((base ^ e1 * n1 + x1) < (base ^ e2 * n2 + x2))%N.
      apply base_term_lt_lemma2; auto.
      lia. }
  assert (n1 = n2) by lia.
  subst. lia.
Qed.

Lemma base_term_eq_lemma' base e1 n1 x1 e2 n2 x2:
  (1 < base)%N ->
  (0 < n1 < base)%N ->
  (0 < n2 < base)%N ->
  (0 < x1 <= base^e1)%N ->
  (0 < x2 <= base^e2)%N ->

  (base^e1 * n1 + x1 = base^e2 * n2 + x2)%N ->
  e1 = e2 /\ n1 = n2 /\ x1 = x2.
Proof.
  intros.
  assert (base^e1 * n1 + (x1-1) = base^e2 * n2 + (x2-1))%N by lia.
  assert (e1 = e2 /\ n1 = n2 /\ (x1-1) = (x2-1))%N.
  { apply base_term_eq_lemma with base; auto; lia. }
  lia.
Qed.

Lemma exp_lt_lemma: forall e n base x,
  (0 < n < base)%N ->
  (e < base ^ e * n + x)%N.
Proof.
  intros e n base x [Hn Hnbase].
  apply N.lt_le_trans with (base^e*n)%N; [|lia].
  apply N.lt_le_trans with (base^e*1)%N.
  2: { apply N.mul_le_mono_l; lia. }
  ring_simplify.
  apply N.pow_gt_lin_r; lia.
Qed.

Lemma x_lt_lemma: forall e n base x,
  (0 < n < base)%N ->
  (x < base ^ e * n + x)%N.
Proof.
  intros.
  apply N.lt_le_trans with (1+x)%N; lia.
Qed.


(* Heredirary base notation, with the base held implicitly.
   The intended interpreation of each term is given as:

   HB_Z = 0
   HB_Term e n x = base^e * n + x


   This interpreation is given explicity via `hbn_interp`.
*)
Inductive HBN :=
  HBN_Z : HBN
| HBN_Term: HBN -> N -> HBN -> HBN.

Fixpoint hbn_interp (base: N) (hbn:HBN) : N :=
  match hbn with
  | HBN_Z => 0%N
  | HBN_Term e n x => (base ^ (hbn_interp base e)) * n + hbn_interp base x
  end.

(* Here we explicity give a less-than relation on hereditary base notation,
   directly on the syntax. Later we show that this corresponds directly
   to less than on the interpretation for any appropriate base.
*)
Inductive hbn_lt : HBN -> HBN -> Prop :=
| HBN_LT_Z: forall e n x,
    hbn_lt HBN_Z (HBN_Term e n x)
| HBN_LT_e: forall e1 n1 x1 e2 n2 x2,
    hbn_lt e1 e2 ->
    hbn_lt (HBN_Term e1 n1 x1) (HBN_Term e2 n2 x2)
| HBN_LT_n: forall e1 n1 x1 e2 n2 x2,
    e1 = e2 ->
    (n1 < n2)%N ->
    hbn_lt (HBN_Term e1 n1 x1) (HBN_Term e2 n2 x2)
| HBN_LT_x: forall e1 n1 x1 e2 n2 x2,
    e1 = e2 ->
    n1 = n2 ->
    hbn_lt x1 x2 ->
    hbn_lt (HBN_Term e1 n1 x1) (HBN_Term e2 n2 x2).

Lemma hbn_lt_total: forall a b,
  hbn_lt a b \/ a = b \/ hbn_lt b a.
Proof.    
  induction a as [|e1 He1 n x1 Hx1].
  - intro b. destruct b as [|e2 n2 x2]; auto.
    left. apply HBN_LT_Z.
  - intro b. destruct b as [|e2 n2 x2]; auto.
    { right. right. apply HBN_LT_Z. }
    destruct (He1 e2) as [H|[H|H]].
    + left. apply HBN_LT_e; auto.
    + subst.
      destruct (N.lt_total n n2) as [H|[H|H]].
      * left. apply HBN_LT_n; auto.
      * subst.
        destruct (Hx1 x2) as [H|[H|H]].
        ** left. apply HBN_LT_x; auto.
        ** subst; auto.
        ** right. right.
           apply HBN_LT_x; auto.
      * right. right.
        apply HBN_LT_n; auto.
    + right. right.
      apply HBN_LT_e; auto.
Qed.

Inductive hbn_smaller_exp : HBN -> HBN -> Prop :=
| HBN_smaller_exp_Z: forall e,
    hbn_smaller_exp e HBN_Z
| HBN_smaller_exp_Term: forall e e' n x,
    hbn_lt e' e ->
    hbn_smaller_exp e (HBN_Term e' n x).

(* A term in hereditary base notation is proper if
   each multiplicity within it is nonzero and less
   than the base. Moreover, the addition chain made
   up of HBN terms must have strictly decreasing
   exponents. *)
Inductive hbn_proper (base:N) : HBN -> Prop :=
| HBN_proper_Z :
    hbn_proper base HBN_Z
| HBN_proper_Term : forall e n x,
    hbn_proper base e ->
    (0 < n < base)%N ->
    hbn_proper base x ->
    hbn_smaller_exp e x ->
    hbn_proper base (HBN_Term e n x).

Lemma interp0_iff: forall base x,
  hbn_proper base x ->    
  (hbn_interp base x < 1)%N <-> x = HBN_Z.
Proof.
  intuition; subst; simpl; try lia.
  destruct x; simpl in *; auto.
  inversion H; subst.
  lia.
Qed.  

Lemma lt_equiv base :
  (1 < base)%N ->
  forall sz a b,
    (hbn_interp base a + hbn_interp base b <= sz)%N ->
    hbn_proper base a -> 
    hbn_proper base b ->
    (hbn_lt a b <-> (hbn_interp base a < hbn_interp base b)%N) /\
    (hbn_smaller_exp b a <-> hbn_interp base a < base ^ hbn_interp base b)%N.
Proof.
  intro Hbase.
  induction sz as [sz Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) id)).
  intros [|e1 n1 x1] b Hsz Ha Hb.
  - simpl; split.
    + split; intro H.
      * inversion H; subst; simpl.
        inversion Hb; subst.
        apply N.lt_lt_add_r.
        apply N.mul_pos_pos; intuition.
        apply N.lt_le_trans with (base ^ 0)%N.
        { apply N.pow_gt_lin_r. auto. }
        apply N.pow_le_mono_r; lia.
      * destruct b; simpl in *; try lia.
        apply HBN_LT_Z.
    + split.
      * intro H.
        inversion H; subst.
        apply N.lt_le_trans with (base ^ 0)%N.
        { apply N.pow_gt_lin_r. auto. }
        apply N.pow_le_mono_r; lia.
      * intros. constructor.
  - split.
    + simpl; split; intro H.
      * inversion H; simpl; subst.
        ** inversion Ha; subst.
           inversion Hb; subst.
           apply base_term_lt_lemma1; auto.
           *** destruct Hind with (y:= (hbn_interp base x1 + hbn_interp base e1)%N) (a:= x1) (b:=e1)
                 as [Hi1 Hi2]; auto.
               { red. simpl. split. lia.
                 simpl in *. unfold id.
                 apply N.lt_le_trans with (base ^ hbn_interp base e1 * n1 + hbn_interp base x1)%N.
                 2:{ lia. }
                 apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1 + hbn_interp base x1)%N.
                 ring_simplify.
                 apply N.add_le_lt_mono. lia.
                 apply N.pow_gt_lin_r; auto.
                 apply N.add_le_mono; try lia.
                 apply N.mul_le_mono; lia. }
               lia.
               apply Hi2; auto.
           *** destruct Hind with (y:= (hbn_interp base e1 + hbn_interp base e2)%N) (a:= e1) (b:=e2)
                 as [Hi1 Hi2]; auto.
               { red. simpl. split. lia.
                 unfold id. simpl in *.
                 apply N.lt_le_trans with (base ^ hbn_interp base e1 * n1 + base ^ hbn_interp base e2 * n2)%N.
                 2:{ lia. }
                 apply N.add_le_lt_mono.
                 apply N.lt_le_incl.
                 apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1)%N.
                 ring_simplify.
                 apply N.pow_gt_lin_r; auto.
                 apply N.mul_le_mono; lia.
                 apply N.lt_le_trans with (base ^ hbn_interp base e2 * 1)%N.
                 ring_simplify.
                 apply N.pow_gt_lin_r; auto.
                 apply N.mul_le_mono; lia. }
               lia.
               apply Hi1; auto.
        ** inversion Ha; subst.
           inversion Hb; subst.
           apply base_term_lt_lemma2; auto.
           destruct Hind with (y:= (hbn_interp base x1 + hbn_interp base e2)%N) (a:= x1) (b:=e2)
             as [Hi1 Hi2]; auto.
           { red. simpl. split. lia.
             unfold id. simpl in *.
             apply N.lt_le_trans with (hbn_interp base x1 + base ^ hbn_interp base e2 * n2)%N.
             2:{ lia. }
             apply N.add_le_lt_mono; try lia.
             apply N.lt_le_trans with (base ^ hbn_interp base e2 * 1)%N.
             ring_simplify.
             apply N.pow_gt_lin_r; auto.
             apply N.mul_le_mono; lia. }
           simpl in *; lia.
           apply Hi2; auto.
        ** apply N.add_le_lt_mono; [ lia |].
           inversion Ha; subst.
           inversion Hb; subst.
           destruct Hind with (y:= (hbn_interp base x1 + hbn_interp base x2)%N) (a:= x1) (b:=x2)
             as [Hi1 Hi2]; auto.
           { red. simpl. split. lia.
             unfold id. simpl in *.
             lia. }
           lia.
           apply Hi1; auto.
      * destruct b as [|e2 n2 x2]; simpl in *. lia.
        destruct (hbn_lt_total e1 e2) as [He|[He|He]].
        ** apply HBN_LT_e; auto.
        ** subst.
           destruct (N.lt_total n1 n2) as [Hn|[Hn|Hn]].
           *** apply HBN_LT_n; auto.
           *** subst.
               destruct (hbn_lt_total x1 x2) as [Hx|[Hx|Hx]].
               **** apply HBN_LT_x; auto.
               **** subst. lia.
               **** inversion Ha; subst.
                    inversion Hb; subst.
                    destruct Hind with (y:= (hbn_interp base x2 + hbn_interp base x1)%N) (a:= x2) (b:=x1)
                      as [Hi1 Hi2]; auto.
                    { red. simpl. split. lia.
                      unfold id. lia. }
                    lia.
                    rewrite Hi1 in Hx.
                    lia.
           *** exfalso.
               inversion Ha; subst.
               inversion Hb; subst.

               assert (base ^ hbn_interp base e2 * n2 + hbn_interp base x2 < base ^ hbn_interp base e2 * n1 + hbn_interp base x1)%N.
               { apply base_term_lt_lemma2; auto.
                 destruct Hind with (y:= (hbn_interp base x2 + hbn_interp base e2)%N) (a:= x2) (b:=e2)
                   as [Hi1 Hi2]; auto.
                 { red. simpl. split. lia.
                   unfold id. simpl in *. 
                   apply N.lt_le_trans with (hbn_interp base x2 + base ^ hbn_interp base e2 * n2)%N.
                   2:{ lia. }
                   apply N.add_le_lt_mono; try lia.
                   apply N.lt_le_trans with (base ^ hbn_interp base e2 * 1)%N.
                   ring_simplify.
                   apply N.pow_gt_lin_r; auto.
                   apply N.mul_le_mono; lia. }
                 simpl in *; lia.
                 rewrite Hi2 in  H10.
                 lia. }
               lia.
        ** exfalso.
           inversion Ha; subst.
           inversion Hb; subst.
           destruct Hind with (y:= (hbn_interp base e2 + hbn_interp base e1)%N) (a:= e2) (b:=e1)
             as [Hi1 Hi2]; auto.
           { red. split. lia.
             unfold id. 
             apply N.lt_le_trans with (base ^ hbn_interp base e2 * n2 + base ^ hbn_interp base e1 * n1)%N.
             2: { lia. }
             apply N.add_le_lt_mono.
             apply N.lt_le_incl.
             apply N.lt_le_trans with (base ^ hbn_interp base e2 * 1)%N.
             ring_simplify.
             apply N.pow_gt_lin_r; auto.
             apply N.mul_le_mono; lia.
             apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1)%N.
             ring_simplify.
             apply N.pow_gt_lin_r; auto.
             apply N.mul_le_mono; lia. }
           lia.
           rewrite Hi1 in He.
           assert (base ^ hbn_interp base e2 * n2 + hbn_interp base x2 <
                     base ^ hbn_interp base e1 * n1 + hbn_interp base x1)%N.
           { apply base_term_lt_lemma1; auto.
             destruct Hind with (y:= (hbn_interp base x2 + hbn_interp base e2)%N) (a:= x2) (b:=e2)
               as [Hi3 Hi4]; auto.
             { red. split. lia.
               unfold id.
               apply N.lt_le_trans with (hbn_interp base x2 + base ^ hbn_interp base e2 * n2)%N.
               2:{ lia. }
               apply N.add_le_lt_mono; try lia.
               apply N.lt_le_trans with (base ^ hbn_interp base e2 * 1)%N.
               ring_simplify.
               apply N.pow_gt_lin_r; auto.
               apply N.mul_le_mono; lia. }
             lia.
             rewrite Hi4 in H10.
             lia. }
           lia.
    + split.
      * intro H.
        inversion H; subst.
        inversion Ha; subst.
        destruct Hind with (y:= (hbn_interp base e1 + hbn_interp base b)%N) (a:= e1) (b:=b)
          as [Hi1 Hi2]; auto.
        { red; simpl. split. lia.
          unfold id. simpl in *.
          apply N.lt_le_trans with (base ^ hbn_interp base e1 * n1 + hbn_interp base b)%N.
          apply N.add_lt_le_mono; try lia.
          apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1)%N.
          ring_simplify.
          apply N.pow_gt_lin_r; auto.
          apply N.mul_le_mono; lia.
          lia. }
        simpl in *; lia.
        apply Hi1 in H2; auto.
        simpl.
        destruct Hind with (y:= (hbn_interp base x1 + hbn_interp base e1)%N) (a:= x1) (b:=e1)
          as [Hi3 Hi4]; auto.
        { red; simpl. split. lia.
          unfold id. simpl in *.
          apply N.lt_le_trans with (hbn_interp base x1 + base ^ hbn_interp base e1 * n1)%N.
          2:{ lia. }
          apply N.add_le_lt_mono; try lia.
          apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1)%N.
          ring_simplify.
          apply N.pow_gt_lin_r; auto.
          apply N.mul_le_mono; lia. }
        lia.
        apply Hi4 in H7.
        apply N.lt_le_trans with (base ^ hbn_interp base e1 * n1 + base ^ hbn_interp base e1)%N.
        { apply N.add_le_lt_mono; auto. lia. }
        transitivity (base ^ hbn_interp base e1 * N.succ n1)%N.
        { rewrite N.mul_succ_r; lia. }
        transitivity (base ^ hbn_interp base e1 * base)%N.
        { apply N.mul_le_mono_l. lia. }
        transitivity (base ^ N.succ (hbn_interp base e1))%N.
        { rewrite N.pow_succ_r'. lia. }
        apply N.pow_le_mono_r; lia.
      * intros; simpl.
        constructor.
        inversion Ha; subst.
        destruct Hind with (y:= (hbn_interp base e1 + hbn_interp base b)%N) (a:= e1) (b:=b)
          as [Hi1 Hi2]; auto.
        { red. simpl. split. lia.
          unfold id. simpl in *.
          apply N.lt_le_trans with (base ^ hbn_interp base e1 * n1 + hbn_interp base b)%N.
          2:{ lia. }
          apply N.add_lt_le_mono; try lia.
          apply N.lt_le_trans with (base ^ hbn_interp base e1 * 1)%N.
          ring_simplify.
          apply N.pow_gt_lin_r; auto. 
          apply N.mul_le_mono; lia. }
        simpl in *; lia.
        rewrite Hi1.
        simpl in *.
        destruct (N.lt_total (hbn_interp base e1) (hbn_interp base b)); auto.
        exfalso.
        assert (hbn_interp base b <= hbn_interp base e1)%N by lia.
        clear H0.
        assert (base ^ hbn_interp base e1 * n1 + hbn_interp base x1 < base ^ hbn_interp base e1 * n1)%N.
        2:{ lia. }
        eapply N.lt_le_trans; [ apply H |].
        transitivity (base ^ hbn_interp base e1)%N; auto.
        { apply N.pow_le_mono_r; lia. }
        transitivity (base ^ hbn_interp base e1 * 1)%N; auto.
        lia.
        apply N.mul_le_mono_l. lia.
Qed.

Lemma hbn_lt_equiv base :
  (1 < base)%N ->
  forall a b,
    hbn_proper base a -> 
    hbn_proper base b ->
    (hbn_lt a b <-> (hbn_interp base a < hbn_interp base b)%N).
Proof.
  intros Hbase a b Ha Hb.
  destruct (lt_equiv base Hbase (hbn_interp base a + hbn_interp base b) a b); auto.
  lia.
Qed.

Lemma hbn_smaller_exp_equiv base :
  (1 < base)%N ->
  forall a b,
    hbn_proper base a -> 
    hbn_proper base b ->
    (hbn_smaller_exp b a <-> hbn_interp base a < base ^ hbn_interp base b)%N.
Proof.
  intros Hbase a b Ha Hb.
  destruct (lt_equiv base Hbase (hbn_interp base a + hbn_interp base b) a b); auto.
  lia.
Qed.

Lemma hbn_proper_unique base :
  (1 < base)%N ->
  forall a b,
    hbn_proper base a ->
    hbn_proper base b ->
    hbn_interp base a = hbn_interp base b ->
    a = b.
Proof.
  intros Hbase a b Ha Hb Hinterp_eq.
  destruct (hbn_lt_total a b) as [Hlt|[Heq|Hgt]]; auto.
  - rewrite (hbn_lt_equiv base) in Hlt; auto. lia.
  - rewrite (hbn_lt_equiv base) in Hgt; auto. lia.
Qed.  

Lemma hbn_proper_mono a b x:
  (a <= b)%N ->
  hbn_proper a x ->
  hbn_proper b x.
Proof.
  induction x; simpl; intros Hab Ha.
  - apply HBN_proper_Z.
  - inversion Ha; subst.
    apply HBN_proper_Term; auto. lia.
Qed.

Definition hbn_term (e:HBN) (n:N) (x:HBN) : HBN :=
  if N.eq_dec n 0%N then x else HBN_Term e n x.

Lemma hbn_term_correct: forall base e n x,
  hbn_interp base (hbn_term e n x) = hbn_interp base (HBN_Term e n x).
Proof.
  intros. unfold hbn_term.
  destruct (N.eq_dec n 0); simpl; auto.
  subst. rewrite N.mul_0_r. lia.
Qed.

Section hbn_decompose.
  Variable base: N.
  Hypothesis Hbase: (1 < base)%N.

  Variable sz: N.
  Variable rec: forall n:N, (n < sz)%N -> HBN.

  Program Fixpoint hbn_decompose_step (n i:N) (tail: HBN)
    (Hni: ((n * base^i) <= sz)%N) { wf N.lt n } : HBN :=
    match N.eq_dec n 0 with
    | left _ => tail
    | right Hnz => hbn_decompose_step (n/base) (i+1) (hbn_term (rec i _) (n mod base) tail) _
    end.
  Next Obligation.
    generalize (N.pow_gt_lin_r base i Hbase). intro.
    assert (base^i <= base^i * n)%N.
    { transitivity (base^i * 1)%N. lia.
      apply N.mul_le_mono_l. lia. }
    lia.
  Qed.
  Next Obligation.  
    assert (n / base * base ^ (i + 1) <= n * base ^ i)%N.
    { rewrite N.pow_add_r.
      rewrite N.pow_1_r.
      rewrite (N.div_mod' n base) at 2.
      ring_simplify.
      apply N.le_add_r. }
    lia.
  Qed.
  Next Obligation.
    generalize (N.div_lt n base). lia.
  Qed.
  Next Obligation.
    apply Wf.measure_wf.
    apply N.lt_wf_0.
  Qed.

  Lemma hbn_decompose_step_eq:
    forall n i tail Hni,
    hbn_decompose_step n i tail Hni = 
      match N.eq_dec n 0 with
      | left _ => tail
      | right Hnz =>
          hbn_decompose_step
            (n / base)
            (i+1)
            (hbn_term (rec i (hbn_decompose_step_func_obligation_1 n i Hni Hnz)) (n mod base) tail)
            (hbn_decompose_step_func_obligation_2 n i Hni Hnz)
      end.
  Proof.
    intros.
    unfold hbn_decompose_step, hbn_decompose_step_func.
    rewrite Wf.Fix_eq; simpl.
    destruct (N.eq_dec n 0); auto.
    intros.
    destruct (N.eq_dec (projT1 x) 0); auto.
  Qed.

  Hypothesis rec_correct: forall n H, hbn_interp base (rec n H) = n.

  Lemma hbn_decompose_step_correct: forall n i tail Hni,
      hbn_interp base (hbn_decompose_step n i tail Hni) = (n * base^i + hbn_interp base tail)%N.
  Proof.
    induction n as [n Hind] using (well_founded_induction (Wf.measure_wf lt_wf N.to_nat)).
    intros i tail Hni.
    rewrite (hbn_decompose_step_eq n i tail Hni).
    destruct (N.eq_dec n 0).
    { subst. simpl. reflexivity. }
    rewrite Hind; auto.
    2:{ red.
        assert (n / base < n)%N.
        { apply N.div_lt; lia. }
        lia. }
    rewrite hbn_term_correct. simpl.
    rewrite rec_correct.
    rewrite N.add_1_r.
    rewrite N.pow_succ_r'.
    ring_simplify.
    generalize (N.div_mod n base). lia.
  Qed.

  Hypothesis rec_proper: forall n H, hbn_proper base (rec n H).

  Lemma hbn_decompose_step_proper: forall n i tail Hni,
    (hbn_interp base tail < base ^ i)%N ->
    hbn_proper base tail ->
    hbn_proper base (hbn_decompose_step n i tail Hni).
  Proof.
    induction n as [n Hind] using (well_founded_induction (Wf.measure_wf lt_wf N.to_nat)).
    intros i tail Hni Htail1 Htail2.
    rewrite (hbn_decompose_step_eq n i tail Hni).
    destruct (N.eq_dec n 0); auto.
    apply Hind.
    - red. assert (n / base < n)%N.
      { apply N.div_lt; lia. }
      lia.
    - rewrite hbn_term_correct. simpl.
      rewrite rec_correct.
      rewrite N.pow_add_r.
      rewrite N.pow_1_r.
      apply N.lt_le_trans with (base ^ i * (n mod base) + base ^ i)%N.
      { apply N.add_le_lt_mono; auto; lia. }
      transitivity (base ^ i * N.succ (n mod base))%N.
      { rewrite N.mul_succ_r; lia. }
      apply N.mul_le_mono_l.
      generalize (N.mod_lt n base).
      lia.
    - unfold hbn_term.
      destruct (N.eq_dec (n mod base) 0); auto.
      apply HBN_proper_Term; auto with ord.
      + split. rewrite <- N.neq_0_lt_0; auto.
        apply N.mod_upper_bound.
        lia.

      + rewrite (hbn_smaller_exp_equiv base); auto.
        rewrite rec_correct.
        auto.
  Qed.
End hbn_decompose.

Program Fixpoint hbn_decompose
  (base:N) (Hbase: (1 < base)%N) (n:N) 
  { wf N.lt n } : HBN :=
  
  hbn_decompose_step base Hbase n
    (fun x H => hbn_decompose base Hbase x)
    n 0 HBN_Z _.
Next Obligation.
  lia.
Qed.
Next Obligation.
  apply Wf.measure_wf.
  apply N.lt_wf_0.
Qed.

Lemma hbn_decompose_step_cong:
  forall base Hbase n sz f g i tail Hni,
    (forall x r, f x r = g x r) ->
    hbn_decompose_step base Hbase sz f n i tail Hni =
      hbn_decompose_step base Hbase sz g n i tail Hni.
Proof.
  intros base Hbase.
  induction n as [n Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) id)).
  intros sz f g i tail Hni Hfg.
  rewrite (hbn_decompose_step_eq base Hbase sz f n i tail Hni).
  rewrite (hbn_decompose_step_eq base Hbase sz g n i tail Hni).
  destruct (N.eq_dec n 0); auto.
  rewrite (Hfg i).
  apply Hind; auto.
  red.
  assert (n / base < n)%N.
  { apply N.div_lt; lia. }
  split. lia.
  unfold id. auto.
Qed.  

Lemma hbn_decompose_eq (base:N) (Hbase: (1 < base)%N) :
  forall n, 
    hbn_decompose base Hbase n = 
      hbn_decompose_step base Hbase n (fun x H => hbn_decompose base Hbase x)
                         n 0 HBN_Z (hbn_decompose_func_obligation_2 base Hbase n).
Proof.
  intro n.
  unfold hbn_decompose, hbn_decompose_func.
  simpl. rewrite Wf.Fix_eq; simpl.
  reflexivity.
  intros. apply hbn_decompose_step_cong; auto.
Qed.

Lemma hbn_decompose_correct (base:N) (Hbase: (1 < base)%N) :
  forall n, hbn_interp base (hbn_decompose base Hbase n) = n.
Proof.
  induction n as [n Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) id)).
  rewrite hbn_decompose_eq.
  rewrite hbn_decompose_step_correct.
  - simpl. ring.
  - simpl; intros.
    apply Hind.
    red; auto.
    unfold id. lia.
Qed.

Lemma hbn_decompose_proper  (base:N) (Hbase: (1 < base)%N) :
  forall n, hbn_proper base (hbn_decompose base Hbase n).
Proof.
  induction n as [n Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) id)).
  rewrite hbn_decompose_eq.
  apply hbn_decompose_step_proper; auto.
  + simpl; intros.
    apply hbn_decompose_correct.
  + intros; apply Hind.
    red. simpl; unfold id. lia.
  + constructor.
  + constructor.
Qed.

Lemma hbn_decompose_unique (base:N) (Hbase: (1 < base)%N):
  forall n hbn,
    hbn_proper base hbn ->
    hbn_interp base hbn = n ->
    hbn_decompose base Hbase n = hbn.
Proof.
  intros.
  apply (hbn_proper_unique base Hbase); auto.
  apply hbn_decompose_proper.
  rewrite hbn_decompose_correct; auto.
Qed.

Lemma plus2_base: forall i, (1 < i + 2)%N.
Proof. lia. Qed.

Lemma plus3_base: forall i, (1 < i + 3)%N.
Proof. lia. Qed.

Definition goodstein_sequence (init:N): N -> N :=
  N.recursion init
    (fun i x =>
      let hbn := hbn_decompose (i + 2) (plus2_base i) x in
        (hbn_interp (i + 3) hbn - 1)%N).

Lemma goodstein_sequence0 x:
  goodstein_sequence x 0 = x.
Proof.
  unfold goodstein_sequence.
  rewrite N.recursion_0; auto.
Qed.

Lemma goodstein_sequence_succ x i:
  goodstein_sequence x (N.succ i) =
    let hbn := hbn_decompose (i + 2) (plus2_base i) (goodstein_sequence x i) in
      (hbn_interp (i + 3) hbn - 1)%N.
Proof.
  unfold goodstein_sequence at 1.
  rewrite N.recursion_succ; auto.
  hnf; intros.
  hnf; intros.
  subst; auto.
Qed.  

Definition goodstein_hbn (init:N) (i:N) : HBN :=
  hbn_decompose (i + 2) (plus2_base i) (goodstein_sequence init i).

Lemma goodstein_alt (init:N) (i:N):
  goodstein_sequence init (N.succ i) = (hbn_interp (i + 3) (goodstein_hbn init i) - 1)%N.
Proof.
  intros. rewrite goodstein_sequence_succ. reflexivity.
Qed.  


Inductive hbn_dec (base:N) : HBN -> HBN -> Prop :=
| hbn_dec_Term_x : forall e n x x',
   hbn_dec base x x' ->
   hbn_dec base (HBN_Term e n x) (HBN_Term e n x')
| hbn_dec_Term_n : forall e n x,
   hbn_exp_dec base e x ->
   hbn_dec base (HBN_Term e n HBN_Z) (hbn_term e (N.pred n) x)
with hbn_exp_dec (base:N) : HBN -> HBN -> Prop :=
| hbn_exp_dec_Z:
  hbn_exp_dec base HBN_Z HBN_Z
| hbn_exp_dec_Term_x: forall e e' z,
  hbn_dec base e e' ->
  hbn_exp_dec base e' z ->
  hbn_exp_dec base e (HBN_Term e' (N.pred base) z).


Lemma hbn_dec_correct base (Hbase: (1 < base)%N) :
  forall x x',
    hbn_proper base x ->
    hbn_proper base x' ->
    (hbn_dec base x x' <-> hbn_interp base x = hbn_interp base x' + 1)%N /\
    (hbn_exp_dec base x x' <-> base^hbn_interp base x = hbn_interp base x' + 1)%N.
Proof.
  induction x as [x Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) (hbn_interp base ))).
  
  assert (Hdec: hbn_proper base x -> forall x', hbn_proper base x' ->
    (hbn_dec base x x' <-> hbn_interp base x = (hbn_interp base x' + 1)%N)).
  { intros Hx x' Hx'.
    intuition.
    + inversion H; subst; simpl; auto.
      * inversion Hx; subst.
        inversion Hx'; subst.
        destruct (Hind x0) with x'0; auto.
        ** red. simpl. lia.
        ** rewrite H1 in H0. lia.
      * rewrite N.add_0_r.
        inversion Hx; subst.
        unfold hbn_term in *.
        destruct (N.eq_dec (N.pred n) 0).
        ** assert (n = 1)%N by lia.
           subst n. rewrite N.mul_1_r.
           destruct (Hind e) with x0; auto.
           *** red. simpl. split. lia.
               apply exp_lt_lemma. lia.
           *** intuition.
        ** simpl.
           assert (Hn: (n = N.pred n + 1)%N) by lia.
           rewrite Hn at 1.
           ring_simplify.
           inversion Hx'; subst.
           destruct (Hind e) with x0; auto.
           *** red; simpl. split. lia.
               apply exp_lt_lemma. lia.
           *** rewrite H2 in H0.
               lia.
    + destruct x; simpl in *; [ lia |].
      destruct x'.
      { simpl in *.
        assert (x2 = HBN_Z).
        { assert (hbn_interp base x2 < 1)%N.
          rewrite <- H.
          inversion Hx; subst.
          apply x_lt_lemma. lia.
          rewrite interp0_iff in H0; auto.
          inversion Hx; subst; auto. }
        subst.
        simpl in *.
        assert (n = 1)%N by lia.
        subst.
        ring_simplify in H.
        assert (x1 = HBN_Z).
        { assert (hbn_interp base x1 < 1)%N.
          rewrite <- H.
          apply N.pow_gt_lin_r; lia.
          rewrite interp0_iff in H0; auto.
          inversion Hx; subst; auto. }
        subst.
        apply (hbn_dec_Term_n base HBN_Z 1 HBN_Z).
        apply hbn_exp_dec_Z. }

      simpl in H.
      
      inversion Hx; subst; clear Hx.
      inversion Hx'; subst; clear Hx'.
      
      destruct (N.eq_dec (hbn_interp base x2) 0)%N.
      { rewrite e in H. ring_simplify in H.
        assert (Hx2: (hbn_interp base x2 < 1)%N) by lia.
        rewrite interp0_iff in Hx2; auto.
        subst x2.
        destruct (N.eq_dec n 1).
        { subst n. ring_simplify in H.
          apply (hbn_dec_Term_n base x1 1 (HBN_Term x'1 n0 x'2)).
          destruct (Hind x1 ) with (HBN_Term x'1 n0 x'2); auto.
          - red. split; simpl; try lia.
            ring_simplify.
            apply N.pow_gt_lin_r; lia.
          - apply HBN_proper_Term; auto.
          - rewrite H1. simpl. lia. }
        assert (Hn: (n = N.pred n + 1)%N) by lia.
        rewrite Hn in H.
        ring_simplify in H.
        assert (Hnpred: (N.pred n > 0)%N) by lia.
        assert (hbn_interp base x1 = hbn_interp base x'1 /\ N.pred n = n0 /\ 
                  base ^ hbn_interp base x1 = hbn_interp base x'2 + 1)%N.
        { rewrite (hbn_smaller_exp_equiv base) in *; auto.
          apply base_term_eq_lemma' with base; try lia. }
        intuition subst.
        assert (x'1 = x1).
        { apply hbn_proper_unique with base; auto. }
        subst.
        assert (HBN_Term x1 (N.pred n) x'2 = hbn_term x1 (N.pred n) x'2).
        { unfold hbn_term.
          destruct (N.eq_dec (N.pred n) 0); auto. lia. }
        rewrite H0.
        apply hbn_dec_Term_n.
        destruct (Hind x1) with x'2 as [Hind1 Hind2]; auto.
        { red. simpl. split. lia.
          apply exp_lt_lemma. lia. }
        rewrite Hind2.
        auto.
      } 

      assert (hbn_interp base x1 = hbn_interp base x'1 /\ n = n0 /\ hbn_interp base x2 = hbn_interp base x'2 +1)%N.
      { rewrite (hbn_smaller_exp_equiv base) in *; auto.
        apply base_term_eq_lemma' with base; try lia. }
      intuition subst.
      assert (x'1 = x1).
      { apply hbn_proper_unique with base; auto. }
      subst.
      apply hbn_dec_Term_x.
      destruct (Hind x2) with x'2 as [Hind1 Hind2]; auto.
      { red. simpl. lia. }
      rewrite Hind1.
      auto.
  } 

  intros x' Hx Hx'.
  split. apply Hdec; auto.
  split; intro H.
  - inversion H; subst; simpl; auto.
    inversion Hx'; subst.
    rewrite Hdec in H0; auto.
    rewrite H0.
    rewrite N.add_1_r.
    rewrite N.pow_succ_r'.
    destruct (Hind e') with z as [Hind1 Hind2]; simpl; auto.
    { red. lia. }
    rewrite Hind2 in H1.
    rewrite H1.
    lia.
  - destruct (N.eq_dec (hbn_interp base x) 0)%N.
    { rewrite e in H. simpl in *.
      assert (Hx1: (hbn_interp base x < 1)%N) by lia.
      assert (Hx'1: (hbn_interp base x' < 1)%N) by lia.
      rewrite interp0_iff in Hx1; auto.
      rewrite interp0_iff in Hx'1; auto.
      subst. apply hbn_exp_dec_Z. }
    assert (He': exists e', hbn_proper base e' /\ (hbn_interp base x = hbn_interp base e' + 1)%N).
    { exists (hbn_decompose base Hbase (hbn_interp base x - 1)%N).
      split.
      apply hbn_decompose_proper.
      rewrite hbn_decompose_correct.
      lia. }
    destruct He' as [e' [He'1 He'2]].
    generalize He'2.
    rewrite <- Hdec; auto.
    intro Hxe'.
    rewrite He'2 in H.
    rewrite N.add_1_r in H.
    rewrite N.pow_succ_r' in H.
    assert (Hx'_eq:  x' = HBN_Term e' (N.pred base) (hbn_decompose base Hbase (base ^ hbn_interp base e' - 1))).
    { apply (hbn_proper_unique base Hbase); auto.
      - apply HBN_proper_Term; auto.
        + split; lia.
        + apply hbn_decompose_proper.
        + rewrite (hbn_smaller_exp_equiv base); auto.
          * rewrite hbn_decompose_correct. lia.
          * apply hbn_decompose_proper.
      - simpl.
        rewrite hbn_decompose_correct.
        transitivity (base * base ^ hbn_interp base e' - 1)%N; lia. }
    rewrite Hx'_eq.
    apply hbn_exp_dec_Term_x; auto.
    destruct (Hind e') with (hbn_decompose base Hbase (base ^ hbn_interp base e' - 1)) as [Hind1 Hind2]; auto.
    + red. split; lia.
    + apply hbn_decompose_proper.
    + rewrite Hind2.
      rewrite  hbn_decompose_correct.
      lia.
Qed.

Lemma goodstein_hbn_decreasing:
  forall x i,
    goodstein_hbn x i = HBN_Z \/
      hbn_dec (i + 3) (goodstein_hbn x i) (goodstein_hbn x (N.succ i)).
Proof.
  intros.
  case_eq (goodstein_hbn x i); auto.
  intros. right.
  destruct (hbn_dec_correct (i + 3) (plus3_base i) (goodstein_hbn x i) (goodstein_hbn x (N.succ i))).
  { unfold goodstein_hbn.
    apply hbn_proper_mono with (i + 2)%N. lia.
    apply hbn_decompose_proper. }
  { unfold goodstein_hbn.
    apply hbn_proper_mono with (N.succ i + 2)%N. lia.
    apply hbn_decompose_proper. }
  assert (Hi': (i + 3 = N.succ i + 2)%N) by lia.
  rewrite <- H.
  rewrite H0.	  
  unfold goodstein_hbn at 2.
  rewrite Hi'.
  rewrite hbn_decompose_correct.
  rewrite goodstein_alt.
  rewrite Hi'.
  assert (~(hbn_interp (N.succ i + 2) (goodstein_hbn x i) < 1))%N; [|lia].
  destruct (N.lt_total (hbn_interp (N.succ i + 2) (goodstein_hbn x i)) 1); auto.
  + rewrite interp0_iff in H2; auto.
    congruence.
    unfold goodstein_hbn.
    apply hbn_proper_mono with (i + 2)%N. lia.
    apply hbn_decompose_proper.
  + lia.
Qed.
  
Fixpoint hbn_shadow (hbn:HBN) : Ord :=
  match hbn with
  | HBN_Z => 0
  | HBN_Term e n x => expOrd ω (hbn_shadow e) * nOrd n + hbn_shadow x
  end.

Lemma hbn_dec_shadow_dec base :
  (1 < base)%N ->
  forall x,
    hbn_proper base x ->
    (forall y, hbn_dec base x y -> hbn_proper base y /\ hbn_shadow x > hbn_shadow y) /\
    (forall y, hbn_exp_dec base x y -> hbn_proper base y /\  expOrd ω (hbn_shadow x) > hbn_shadow y).
Proof.
  intro Hbase.
  induction x as [x Hind] using (well_founded_induction (Wf.measure_wf (N.lt_wf 0) (hbn_interp base ))).
  intro Hx.
  assert (Hdec: forall y, hbn_dec base x y -> hbn_proper base y /\ hbn_shadow x > hbn_shadow y).
  { intros y Hxy.
    inversion Hxy; subst; simpl.
    - inversion Hx; subst.
      split.
      + destruct (Hind x0); auto.
        { red. simpl. lia. }
        generalize (H0 _ H); intros [??].
        apply HBN_proper_Term; auto.
        rewrite (hbn_smaller_exp_equiv base); auto.
        destruct (hbn_dec_correct base Hbase x0 x'); auto.
        rewrite H8 in H.
        destruct (hbn_dec_correct base Hbase e x0); auto.
        rewrite (hbn_smaller_exp_equiv base) in H6; auto.
        lia.
      + apply addOrd_increasing.
        destruct (Hind x0); auto.
        { red. simpl. split. lia.
          inversion Hx; subst.
          apply x_lt_lemma; auto. }
        apply H0. auto.
    - inversion Hx; subst.
      unfold hbn_term.
      rewrite addOrd_zero_r.
      destruct (N.eq_dec (N.pred n) 0).
      + assert (n = 1)%N by lia. subst.
        simpl. rewrite mulOrd_one_r.
        destruct (Hind e); auto.
        red. split. lia.
        simpl. apply exp_lt_lemma.
        lia.
      + simpl.
        assert (Hn: nOrd n ≈ nOrd (N.pred n) + 1).
        { assert (Hn: (n = N.pred n + 1)%N) by lia.
          rewrite Hn at 1.
          repeat rewrite nOrd_commute.
          rewrite N2Nat.inj_add.
          rewrite PeanoNat.Nat.add_comm.
          rewrite natOrdSize_add.
          simpl; auto with ord. }
        split.
        * destruct (Hind e); auto.
          { red. simpl. split. lia.
            apply exp_lt_lemma.
            lia. }
          generalize (H1 _ H); intros [??].
          apply HBN_proper_Term; auto. lia.
          rewrite (hbn_smaller_exp_equiv base); auto.
          destruct (hbn_dec_correct base Hbase e x0); auto.
          rewrite H9 in H. lia. 
        * rewrite Hn.
          rewrite addOrd_succ.
          rewrite addOrd_zero_r.
          rewrite mulOrd_succ.
          apply addOrd_increasing.
          destruct (Hind e); auto.
          red. split. lia.
          simpl. apply exp_lt_lemma.
          lia.
          apply H1; auto. }
  split; auto.
  intros y Hxy.
  inversion Hxy; subst; simpl; auto with ord.
  - split.
    + apply HBN_proper_Z.
    + apply expOrd_nonzero.
  - generalize (Hdec e' H). intros [??].
    destruct (Hind e'); auto.
    { red. split. lia.
      destruct (hbn_dec_correct base Hbase x e'); auto.
      rewrite H3 in H. lia. }
    generalize (H4 _ H0); intros [??].
    split.
    + apply HBN_proper_Term; auto.
      lia.
      intuition.
      rewrite (hbn_smaller_exp_equiv base); auto.
      destruct (hbn_dec_correct base Hbase e' z); auto.
      rewrite H8 in H0. lia.
    + apply ord_lt_le_trans with (expOrd ω (succOrd (hbn_shadow e'))).
      2:{ apply expOrd_monotone.
          apply succ_least; auto. }
      rewrite expOrd_succ; auto with ord.
      apply ord_le_lt_trans with (expOrd ω (hbn_shadow e') * (nOrd (N.pred base) + 1)).
      2:{ apply mulOrd_increasing2.
          apply expOrd_nonzero.
          rewrite nOrd_commute.
          
          apply ord_le_lt_trans with (natOrdSize (N.to_nat (N.pred base) + 1)).
          - rewrite PeanoNat.Nat.add_comm.
            rewrite natOrdSize_add.
            simpl. auto with ord.
          - rewrite ord_lt_unfold. simpl. eauto with ord.
      }
    rewrite addOrd_succ.
    rewrite addOrd_zero_r.
    rewrite mulOrd_succ.
    apply addOrd_monotone; auto with ord.
Qed.    

Lemma shadow_le0_hbn_Z base hbn:
  hbn_proper base hbn ->
  hbn_shadow hbn <= 0 ->
  hbn = HBN_Z.
Proof.
  destruct hbn; simpl in *; auto.
  intros.
  elim (ord_lt_irreflexive 0).
  rewrite <- H0 at 2.
  rewrite <- addOrd_le1.
  inversion H; subst.
  apply ord_lt_le_trans with (expOrd ω (hbn_shadow hbn1) * nOrd 1).
  - simpl. rewrite mulOrd_one_r.
    apply expOrd_nonzero.
  - apply mulOrd_monotone2; auto with ord.
    repeat rewrite nOrd_commute.
    apply natOrdSize_monotone. lia.
Qed.  
    
Lemma hbn_decompose_zero base (Hbase: (1 < base)%N) x:
  hbn_decompose base Hbase x = HBN_Z ->
  x = 0%N.
Proof.
  intros.
  assert (hbn_interp base (hbn_decompose base Hbase x) = hbn_interp base HBN_Z) by congruence.
  rewrite hbn_decompose_correct in H0. simpl in *.
  auto.
Qed.

Lemma goodstein_hbn_zero:
  forall o x i,
    hbn_shadow (goodstein_hbn x i) <= o ->
    exists j, hbn_shadow (goodstein_hbn x j) <= 0.
Proof.
  induction o as [o Hind] using ordinal_induction.
  intros x i H.
  destruct (goodstein_hbn_decreasing x i).
  - exists i. rewrite H0. simpl. auto with ord.
  - destruct (hbn_dec_shadow_dec (i + 3)) with (goodstein_hbn x i); auto.
    + lia.
    + unfold goodstein_hbn.
      apply hbn_proper_mono with (i + 2)%N; [lia|].
      apply hbn_decompose_proper.
    + generalize (H1 _ H0); intros [??].
      apply (Hind (hbn_shadow (goodstein_hbn x (N.succ i)))) with (N.succ i); auto with ord.
      eapply ord_lt_le_trans. apply H4. auto.
Qed.

Theorem goodstein_zero:
  forall x, exists i, goodstein_sequence x i = 0%N.
Proof.
  intro x.
  destruct (goodstein_hbn_zero (hbn_shadow (goodstein_hbn x 0)) x 0) as [i Hi]; auto with ord.
  exists i.
  unfold goodstein_hbn in Hi.
  apply (shadow_le0_hbn_Z (i + 2)) in Hi.
  - apply hbn_decompose_zero in Hi; auto.
  - apply hbn_decompose_proper.
Qed.
