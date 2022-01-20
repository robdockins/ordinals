Require Import Morphisms.
Require Import Coq.Program.Basics.
Require Import NArith.
Require Import List.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.

Open Scope ord_scope.

Inductive CantorForm : Set :=
  | CantorSum : list CantorForm -> CantorForm.

Fixpoint cantorOrd (cf:CantorForm) : Ord :=
  match cf with
  | CantorSum xs =>
      fold_right (fun (x:CantorForm) o => expOrd ω (cantorOrd x) + o) 0 xs
  end.

Canonical Structure CF :=
  ord CantorForm cantorOrd.

Import ListNotations.
Open Scope list.

Inductive ordering := LT | EQ | GT.

Definition ordering_swap (o:ordering) : ordering :=
  match o with
  | LT => GT
  | EQ => EQ
  | GT => LT
  end.

Definition lexCompare (o1:ordering) (o2:ordering) : ordering :=
  match o1 with
  | LT => LT
  | EQ => o2
  | GT => GT
  end.

Fixpoint cantorCompare (x:CantorForm) (y:CantorForm) {struct x} : ordering :=
  match x, y with
  | CantorSum xs0, CantorSum ys0 =>
    (fix cantorSumCompare (xs:list CantorForm) (ys:list CantorForm) {struct xs} : ordering :=
       match xs, ys with
       | [], [] => EQ
       | [], (y::ys) => LT
       | (x::xs), [] => GT
       | (x::xs), (y::ys) =>
         lexCompare (cantorCompare x y) (cantorSumCompare xs ys)
       end) xs0 ys0
  end.

Definition cantorSumCompare : list CantorForm -> list CantorForm -> ordering :=
  fix cantorSumCompare (xs:list CantorForm) (ys:list CantorForm) {struct xs} : ordering :=
  match xs, ys with
  | [], [] => EQ
  | [], (y::ys) => LT
  | (x::xs), [] => GT
  | (x::xs), (y::ys) =>
    lexCompare (cantorCompare x y) (cantorSumCompare xs ys)
  end.

Lemma cantorCompare_unfold xs ys : cantorCompare (CantorSum xs) (CantorSum ys) = cantorSumCompare xs ys.
Proof.
  reflexivity.
Qed.


Fixpoint cantorIsNormal (cf:CantorForm) : Prop :=
  match cf with
  | CantorSum [] => True
  | CantorSum (x0::xs0) => cantorIsNormal x0 /\
    (fix check (x:CantorForm) (xs:list CantorForm) : Prop :=
      match xs with
      | [] => True
      | (x'::xs') => cantorIsNormal x' /\ cantorOrd x >= cantorOrd x' /\ check x' xs'
      end) x0 xs0
  end.

Definition CantorNormalForm : Set := { cf:CantorForm | cantorIsNormal cf }.

Definition CNF_denote (x:CantorNormalForm) := cantorOrd (proj1_sig x).

Canonical Structure CNF := ord CantorNormalForm CNF_denote.

Lemma cantorCompare_swap : forall (x y:CantorForm),
  cantorCompare x y = ordering_swap (cantorCompare y x).
Proof.
  fix Hind 1.
  intros [xs] [ys].
  revert ys.
  induction xs as [|x xs]; intros.
  - destruct ys as [|y ys]; simpl in *; auto.
  - destruct ys as [|y ys]; simpl in *; auto.
    replace (cantorCompare x y) with (ordering_swap (cantorCompare y x)).
    + destruct (cantorCompare y x); simpl in * ; auto.
    + symmetry. apply Hind.
Qed.

Lemma CantorForm_complete : forall a, complete (cantorOrd a).
Proof.
  fix Hind 1.
  intros [ls]. simpl.
  induction ls.
  - apply zero_complete.
  - simpl fold_right.
    apply addOrd_complete; auto.
    apply expOrd_complete; auto.
    apply (index_lt ω 0%nat).
    apply omega_complete.
Qed.

Lemma cantorOrd_shrink : forall x, cantorOrd x < expOrd ω (cantorOrd x).
Proof.
  fix Hind 1.
  intros [xs]. revert xs.
  fix Hind_xs 1.
  intros [|x xs].
  - simpl cantorOrd.
    apply expOrd_nonzero.
  - simpl cantorOrd.
    apply expOmega_additively_closed.
    + apply (CantorForm_complete (CantorSum (x::xs))).
    + rewrite expOrd_add.
      apply ord_lt_le_trans with (expOrd ω (expOrd ω (cantorOrd x)) * 1).
      rewrite mulOrd_one_r.
      apply expOrd_increasing. apply omega_gt1.
      apply Hind.
      apply mulOrd_monotone2.
      apply succ_least. apply expOrd_nonzero.
    + rewrite expOrd_add.
      apply ord_lt_le_trans with
          (1 * expOrd ω (fold_right
                           (fun (x0 : CantorForm) (o : Ord) => expOrd ω (cantorOrd x0) + o) 0 xs)).
      rewrite mulOrd_one_l.
      apply (Hind_xs xs).
      apply mulOrd_monotone1.
      apply succ_least. apply expOrd_nonzero.
Qed.

Lemma epslion_additively_closed : forall x, complete x -> additively_closed (ε x).
Proof.
  intros. hnf; intros.
  rewrite ε_fixpoint.
  apply expOmega_additively_closed.
  - apply ε_complete; auto.
  - rewrite <- ε_fixpoint. auto.
  - rewrite <- ε_fixpoint. auto.
Qed.

Theorem cantorForm_below_epsilon : forall (x:CF), x < ε 0.
Proof.
  induction x using size_induction.
  destruct x as [xs].
  unfold sz. simpl ordSize.
  induction xs.
  - simpl fold_right.
    rewrite ε_fixpoint.
    apply expOrd_nonzero.
  - simpl fold_right.
    apply epslion_additively_closed.
    apply zero_complete.
    rewrite ε_fixpoint.
    apply expOrd_increasing.
    apply omega_gt1.
    apply H.
    simpl.
    rewrite <- addOrd_le1.
    apply cantorOrd_shrink.
    apply IHxs.
    intros.
    apply H.
    simpl.
    rewrite <- addOrd_le2.
    auto.
Qed.


Definition CantorNormalForm_lt (x y:CantorNormalForm) :=
  cantorCompare (proj1_sig x) (proj1_sig y) = LT.

Definition CantorNormalForm_le (x y:CantorNormalForm) :=
  cantorCompare (proj1_sig x) (proj1_sig y) <> GT.

Lemma CNF_compare_correct_lemma a lsb : 
  forall c,
    cantorIsNormal (CantorSum (c :: lsb)) ->
    cantorIsNormal a ->
    cantorIsNormal c ->
    cantorOrd c < cantorOrd a ->
    fold_right (fun (x : CantorForm) (o : Ord) => expOrd ω (cantorOrd x) + o) 0
               lsb < expOrd ω (cantorOrd a).
Proof.
  induction lsb; simpl fold_right; intros.
  - apply expOrd_nonzero.
  - apply expOmega_additively_closed.
    { apply CantorForm_complete. }
    { apply expOrd_increasing; auto.
      apply omega_gt1.
      apply ord_le_lt_trans with (cantorOrd c); auto.
      simpl in *; intuition. }

    apply IHlsb with a0; simpl in *; intuition.
    apply ord_le_lt_trans with (cantorOrd c); auto.
Qed.

Lemma CNF_compare_correct :
  forall (a b:CF),
    cantorIsNormal a ->
    cantorIsNormal b ->
    match cantorCompare a b with
    | LT => cantorOrd a < cantorOrd b
    | EQ => cantorOrd a ≈ cantorOrd b
    | GT => cantorOrd a > cantorOrd b
    end.
Proof.
  induction a as [[xs] Hind] using size_induction.
  induction xs as [|a lsa].
  - intros [lsb]; destruct lsb; simpl; intros; auto with ord.
    + reflexivity.
    + rewrite <- addOrd_le1.
      apply expOrd_nonzero.
  - intros [lsb]; destruct lsb; intros.
    + simpl.
      rewrite <- addOrd_le1.
      apply expOrd_nonzero.
    + simpl cantorCompare.
      assert (Hlsa : cantorIsNormal (CantorSum lsa)).
      { simpl in H. simpl. destruct lsa; intuition. }
      assert (Hlsb : cantorIsNormal (CantorSum lsb)).
      { simpl in H0. simpl. destruct lsb; intuition. }
      assert (Ha : cantorIsNormal a).
      { simpl in H; intuition. }
      assert (Hc : cantorIsNormal c).
      { simpl in H0; intuition. }
      assert (Hlt : a ◃ (CantorSum (a :: lsa))).
      { simpl. rewrite <- addOrd_le1. apply cantorOrd_shrink. }
      generalize (Hind a Hlt c Ha Hc).
      destruct (cantorCompare a c); simpl.
      * intros.
        eapply ord_lt_le_trans; [ | apply addOrd_le1 ].
        apply expOmega_additively_closed.
        apply CantorForm_complete.
        apply expOrd_increasing; auto.
        apply omega_gt1.

        apply CNF_compare_correct_lemma with a; auto.

      * intro Hac.
        assert (match cantorCompare (CantorSum lsa) (CantorSum lsb) with
                  | LT => cantorOrd (CantorSum lsa) < cantorOrd (CantorSum lsb)
                  | EQ => cantorOrd (CantorSum lsa) ≈ cantorOrd (CantorSum lsb)
                  | GT => cantorOrd (CantorSum lsb) < cantorOrd (CantorSum lsa)
                end).
        apply IHlsa; auto.
        { intros. apply Hind; auto. simpl.
          rewrite <- addOrd_le2. auto. }
        simpl in H1.
        destruct ((fix cantorSumCompare (xs ys : list CantorForm) {struct xs} : ordering :=
            match xs with
            | [] => match ys with
                    | [] => EQ
                    | _ :: _ => LT
                    end
            | x :: xs0 =>
                match ys with
                | [] => GT
                | y :: ys0 =>
                    lexCompare (cantorCompare x y) (cantorSumCompare xs0 ys0)
                end
            end) lsa lsb).
        ** apply ord_le_lt_trans with
            (expOrd ω (cantorOrd c) +
                      fold_right (fun (x : CantorForm) (o : Ord) => expOrd ω (cantorOrd x) + o) 0 lsa).
           apply addOrd_monotone; auto with ord.
           apply expOrd_monotone; apply Hac.
           apply addOrd_increasing. auto.
        ** intros.
           apply addOrd_eq_mor; auto.
           split; apply expOrd_monotone; apply Hac.
        ** apply ord_le_lt_trans with
               (expOrd ω (cantorOrd a) +
                fold_right (fun (x : CantorForm) (o : Ord) => expOrd ω (cantorOrd x) + o) 0 lsb).
           apply addOrd_monotone; auto with ord.
           apply expOrd_monotone; apply Hac.
           apply addOrd_increasing. auto.

      * intros.
        eapply ord_lt_le_trans; [ | apply addOrd_le1 ].
        apply expOmega_additively_closed.
        apply CantorForm_complete.
        apply expOrd_increasing; auto.
        apply omega_gt1.
        apply CNF_compare_correct_lemma with c; auto.
Qed.

Lemma CNF_lt_reflects : reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> PROP) ord_lt CantorNormalForm_lt.
Proof.
  simpl. intros x [a Ha] Hxa y [b Hb] Hyb.
  unfold CNF_denote, CantorNormalForm_lt in *; simpl in *.
  generalize (CNF_compare_correct a b Ha Hb).
  intuition.
  - destruct (cantorCompare a b); auto.
    + elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with y; auto.
      rewrite Hyb. rewrite <- H. apply Hxa.
    + elim (ord_lt_irreflexive x).
      apply ord_lt_le_trans with y; auto.
      rewrite Hyb. rewrite Hxa. auto with ord.
  - rewrite H0 in H. rewrite Hxa. rewrite Hyb.
    auto.
Qed.

Lemma CNF_le_reflects : reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> PROP) ord_le CantorNormalForm_le.
Proof.
  simpl. intros x [a Ha] Hxa y [b Hb] Hyb.
  unfold CNF_denote, CantorNormalForm_le in *; simpl in *.
  generalize (CNF_compare_correct a b Ha Hb).
  intuition.
  - rewrite H1 in H.
    elim (ord_lt_irreflexive x).
    apply ord_le_lt_trans with y; auto.
    rewrite Hyb. rewrite Hxa.
    auto.
  - destruct (cantorCompare a b); intuition.
    + rewrite Hxa. rewrite Hyb. auto with ord.
    + rewrite Hxa. rewrite Hyb. apply H.
Qed.


Definition CF_zero  := CantorSum [].
Definition CF_one   := CantorSum [ CF_zero ].
Definition CF_omega := CantorSum [ CF_one ].

Lemma CF_zero_normal : cantorIsNormal CF_zero.
Proof.
  simpl. auto.
Qed.

Lemma CF_one_normal : cantorIsNormal CF_one.
Proof.
  simpl. auto.
Qed.

Lemma CF_omega_normal : cantorIsNormal CF_omega.
Proof.
  simpl. auto.
Qed.

Definition CNF_zero  : CNF := exist _ CF_zero  CF_zero_normal.
Definition CNF_one   : CNF := exist _ CF_one   CF_one_normal.
Definition CNF_omega : CNF := exist _ CF_omega CF_omega_normal.

Lemma CNF_reflects_zero : reflects CantorNormalForm CNF_denote ORD 0 CNF_zero.
Proof.
  red; simpl.
  unfold CNF_denote. simpl. reflexivity.
Qed.

Opaque expOrd.
Opaque mulOrd.
Opaque addOrd.

Lemma CNF_reflects_one : reflects CantorNormalForm CNF_denote ORD 1 CNF_one.
  red; simpl.
  unfold CNF_denote.
  simpl.
  rewrite expOrd_zero.
  rewrite <- addOrd_zero_r.
  reflexivity.
Qed.

Lemma CNF_reflects_omega : reflects CantorNormalForm CNF_denote ORD ω CNF_omega.
Proof.
  red; simpl.
  unfold CNF_denote.
  simpl.
  rewrite <- addOrd_zero_r.
  transitivity (expOrd ω 1).
  rewrite expOrd_succ.
  rewrite expOrd_zero.
  rewrite mulOrd_one_l. reflexivity.
  apply (index_lt ω 0%nat).
  split; apply expOrd_monotone.
  rewrite <- addOrd_zero_r.
  rewrite expOrd_zero; auto with ord.
  rewrite <- addOrd_zero_r.
  rewrite expOrd_zero; auto with ord.
Qed.


Definition cantorIsFinite (x:CF) : option nat :=
  match x with
  | CantorSum [] => Some 0%nat
  | CantorSum (CantorSum [] :: xs) => Some (length xs + 1)%nat
  | _ => None
  end.

Lemma cantorIsFinite_fin : forall (x:CF) n,
    cantorIsNormal x ->
    cantorIsFinite x = Some n -> x ≈ natOrdSize n.
Proof.
  intros [xs] n.
  destruct xs.
  - intros H Hn. simpl in Hn. inversion Hn. simpl. reflexivity.
  - destruct c as [cs]. destruct cs; try discriminate.
    intros. simpl in H0. inversion H0.
    simpl.
    rewrite expOrd_zero.
    rewrite natOrdSize_add.
    apply addOrd_eq_mor; try reflexivity.
    clear n H0 H2.
    induction xs; simpl; try reflexivity.
    rewrite IHxs. clear IHxs.
    assert (Ha : cantorOrd a ≈ 0).
    { split; auto with ord.
      simpl in H; intuition. }
    rewrite Ha.
    rewrite expOrd_zero.
    transitivity (natOrdSize (length xs + 1)).
    { symmetry; apply natOrdSize_add. }
    replace (length xs + 1)%nat with (1 + length xs)%nat by auto with arith.
    simpl. reflexivity.

    simpl in H; simpl; destruct xs; intuition.
    rewrite H3. rewrite H1.
    auto with ord.
Qed.

Lemma cantorIsFinite_inf : forall (x:CF),
    cantorIsFinite x = None -> 1 + x ≈ x.
Proof.
  intros [xs].
  destruct xs; simpl; intuition; try discriminate.
  destruct c as [cs]; destruct cs; try discriminate.
  rewrite addOrd_assoc.
  apply addOrd_eq_mor; try reflexivity.
  split.
  - apply additively_closed_collapse.
    apply expOmega_additively_closed.
    apply CantorForm_complete.
    assert (cantorOrd (CantorSum (c::cs)) >= 1).
    { simpl. rewrite <- addOrd_le1.
      apply succ_least. apply expOrd_nonzero. }
    rewrite <- H0.
    rewrite expOrd_one'.
    apply (index_lt _ 1%nat).
    apply (index_lt _ 0%nat).
  - apply addOrd_le2.
Qed.


Fixpoint cantorSum_add xs ys :=
  match xs with
  | [] => ys
  | (x::xs') =>
    match cantorSum_add xs' ys with
    | [] => [x]
    | (z::zs) => match cantorCompare x z with
                 | LT => z::zs
                 | EQ => x::z::zs
                 | GT => x::z::zs
                 end
    end
  end.

Lemma cantorSum_add_normal xs : forall ys,
    cantorIsNormal (CantorSum xs) ->
    cantorIsNormal (CantorSum ys) ->
    cantorIsNormal (CantorSum (cantorSum_add xs ys)).
Proof.
  induction xs; simpl cantorSum_add; intros; auto.
  assert (cantorIsNormal (CantorSum xs)).
  { simpl in H; destruct xs; simpl in *; intuition. }
  generalize (IHxs ys H1 H0).
  destruct (cantorSum_add xs ys).
  - simpl in *; intuition.
  - generalize (CNF_compare_correct a c).
    case_eq (cantorCompare a c); simpl in * ; intuition.
    apply H3.
Qed.

Lemma cantorSum_add_correct xs : forall ys,
    cantorIsNormal (CantorSum xs) ->
    cantorIsNormal (CantorSum ys) ->
    cantorOrd (CantorSum xs) + cantorOrd (CantorSum ys) ≈ cantorOrd (CantorSum (cantorSum_add xs ys)).
Proof.
  induction xs; simpl cantorSum_add; simpl cantorOrd; intros.
  - rewrite <- addOrd_zero_l. reflexivity.
  - assert (cantorIsNormal (CantorSum xs)).
    { simpl in H; destruct xs; simpl in *; intuition. }
    generalize (IHxs ys H1 H0).
    intros. rewrite <- addOrd_assoc.
    rewrite H2.
    generalize (cantorSum_add_normal xs ys H1 H0).
    destruct (cantorSum_add xs ys); simpl cantorOrd.
    + reflexivity.
    + generalize (CNF_compare_correct a c).
      case_eq (cantorCompare a c); intros; try reflexivity.
      simpl fold_right.
      rewrite addOrd_assoc.
      apply addOrd_eq_mor; try reflexivity.
      split.
      * apply expOrd_add_collapse; auto.
        apply CantorForm_complete.
        apply H4; simpl in *; intuition.
      * apply addOrd_le2.
Qed.

Definition CF_add (x y:CF) :=
  match x, y with
  | CantorSum xs, CantorSum ys => CantorSum (cantorSum_add xs ys)
  end.

Lemma CF_add_normal x y :
  cantorIsNormal x -> cantorIsNormal y -> cantorIsNormal (CF_add x y).
Proof.
  destruct x; destruct y; apply cantorSum_add_normal; auto.
Qed.

Lemma CF_add_correct : forall (x y:CF),
  cantorIsNormal x ->
  cantorIsNormal y ->
  cantorOrd x + cantorOrd y ≈ cantorOrd (CF_add x y).
Proof.
  intros [xs] [ys] Hx Hy.
  apply (cantorSum_add_correct xs ys); auto.
Qed.


Definition CNF_add (x y : CNF) : CNF
  := exist _ (CF_add (proj1_sig x) (proj1_sig y))
           (CF_add_normal _ _ (proj2_sig x) (proj2_sig y)).

Lemma CNF_add_reflects : reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> ORD) addOrd CNF_add.
Proof.
  hnf; simpl. unfold CNF_denote. intros x [a Ha] Hxa y [b Hb] Hyb; simpl in *.
  rewrite Hxa. rewrite Hyb.
  destruct a as [xs]. destruct b as [ys].
  apply (cantorSum_add_correct xs ys); auto.
Qed.

Definition CF_mul_single (x:CF) (e:CF) : CF :=
  match x, e with
  | CantorSum [], _  => CantorSum []
  | _ , CantorSum [] => x
  | CantorSum (x::_), _ => CantorSum [ CF_add x e ]
  end.

Definition CF_mul (x:CF) (y:CF) : CF :=
  match y with
  | CantorSum ys => fold_right (fun y s => CF_add (CF_mul_single x y) s) CF_zero ys
  end.

Lemma CF_mul_single_normal : forall x e,
  cantorIsNormal x ->
  cantorIsNormal e ->
  cantorIsNormal (CF_mul_single x e).
Proof.
  intros [xs] [es] Hx He.
  simpl.
  destruct xs.
  - simpl; intuition.
  - destruct es; auto.
    simpl in *; intuition.
    apply CF_add_normal; intuition.
    simpl; auto.
Qed.

Lemma CF_mul_normal : forall x y,
  cantorIsNormal x ->
  cantorIsNormal y ->
  cantorIsNormal (CF_mul x y).
Proof.
  intros x [ys].
  unfold CF_mul.
  induction ys.
  - simpl. auto.
  - intros.
    simpl fold_right.
    apply CF_add_normal.
    apply (CF_mul_single_normal x a); auto.
    simpl in H0; intuition.
    apply IHys; auto.
    destruct ys; simpl in *; intuition.
Qed.

Lemma cantorFirstTerm_dominates x xs :
  cantorIsNormal (CantorSum (x :: xs)) ->
  cantorOrd (CantorSum xs) ≤ expOrd ω (cantorOrd x) * sz (length xs).
Proof.
  induction xs.
  - simpl; intros; auto with ord.
  - intros.
    transitivity (expOrd ω (cantorOrd x) * (natOrdSize (length xs + 1))).
    + rewrite natOrdSize_add.
      rewrite ordDistrib_left.
      rewrite mulOrd_one_r.
      simpl in *; intuition.
      apply addOrd_monotone; auto.
      * apply expOrd_monotone.
        generalize (CNF_compare_correct x a H0 H).
        destruct (cantorCompare x a); intuition.
      * apply H4; auto.
        destruct xs; intuition.
        transitivity (cantorOrd a); auto.
    + apply mulOrd_monotone2.
      replace (length xs + 1)%nat with (1 + length xs)%nat by auto with arith.
      simpl; reflexivity.
Qed.

Lemma CF_mul_single_correct : forall x e,
  cantorIsNormal x ->
  cantorIsNormal e ->
  cantorOrd (CF_mul_single x e) ≈ cantorOrd x * expOrd ω (cantorOrd e).
Proof.
  intros [xs] [es] Hx He.
  destruct xs.
  - simpl. rewrite mulOrd_zero_l. reflexivity.
  - destruct es.
    + simpl fold_right.
      rewrite expOrd_zero.
      rewrite mulOrd_one_r.
      reflexivity.
    + unfold CF_mul_single.
      transitivity (expOrd ω (cantorOrd (CF_add c (CantorSum (c0::es))))).
      { generalize (CF_add c (CantorSum (c0::es))).
        intros. simpl.
        rewrite <- addOrd_zero_r. reflexivity. }
      transitivity (expOrd ω (cantorOrd c + cantorOrd (CantorSum (c0::es)))).
      { assert (cantorOrd (CF_add c (CantorSum (c0::es))) ≈
                          (cantorOrd c + cantorOrd (CantorSum (c0 :: es)))).
        symmetry; apply CF_add_correct; simpl in *; intuition.
        split; apply expOrd_monotone; apply H. }
      rewrite expOrd_add.
      split.
      * apply mulOrd_monotone1.
        simpl cantorOrd.
        apply addOrd_le1.
      * simpl cantorOrd at 1.
        apply expOrd_omega_collapse with (length xs).
        ** apply CantorForm_complete.
        ** simpl.
           rewrite <- addOrd_le1.
           apply expOrd_nonzero.
        ** apply cantorFirstTerm_dominates; auto.
Qed.

Lemma CF_mul_correct : forall x y,
    cantorIsNormal x ->
    cantorIsNormal y ->
    cantorOrd (CF_mul x y) ≈ cantorOrd x * cantorOrd y.
Proof.
  intros x [ys].
  induction ys; simpl CF_mul; intros.
  - simpl cantorOrd.
    rewrite mulOrd_zero_r. reflexivity.
  - simpl cantorOrd.
    rewrite ordDistrib_left.
    rewrite <- CF_add_correct.
    apply addOrd_eq_mor.
    apply CF_mul_single_correct; auto.
    simpl in H0; intuition.
    apply IHys; auto.
    destruct ys; simpl in * ; intuition.
    apply CF_mul_single_normal; auto.
    simpl in H0; intuition.
    apply (CF_mul_normal x (CantorSum ys)); auto.
    destruct ys; simpl in * ; intuition.
Qed.

Definition CNF_mul (x y : CNF) : CNF
  := exist _ (CF_mul (proj1_sig x) (proj1_sig y))
           (CF_mul_normal _ _ (proj2_sig x) (proj2_sig y)).

Lemma CNF_mul_reflects : reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> ORD) mulOrd CNF_mul.
Proof.
  hnf; simpl. unfold CNF_denote. intros x [a Ha] Hxa y [b Hb] Hyb; simpl in *.
  rewrite Hxa. rewrite Hyb.
  symmetry. apply CF_mul_correct; auto.
Qed.


Definition CF_nat (n:nat) : CF := CantorSum (repeat CF_zero n).

Lemma CF_nat_normal : forall n, cantorIsNormal (CF_nat n).
Proof.
  induction n; simpl; intuition.
  destruct n; simpl in *; intuition.
Qed.

Lemma CF_nat_correct : forall n, CF_nat n ≈ natOrdSize n.
Proof.
  induction n; simpl; try reflexivity.
  rewrite expOrd_zero.
  rewrite IHn.
  transitivity (natOrdSize (n+1)%nat).
  rewrite natOrdSize_add. reflexivity.
  replace (n+1)%nat with (1+n)%nat by auto with arith.
  simpl. reflexivity.
Qed.


Definition CF_exp_single (x:CF) (e:CF) : CF :=
  match x with

    (* 0 ^ (ω^e) = 1 *)
  | CantorSum [] => CF_one

    (* 1 ^ (ω^e) = 1 *)
  | CantorSum [ CantorSum [] ] => CF_one

  | CantorSum (CantorSum [] :: _ ) =>
    match cantorIsFinite e with
      (* n ^ (ω^0) = n *)
    | Some 0 => x

      (* n ^ (ω^(1+m)) = ω^(ω^m) for finite n > 1, finite m *)
    | Some (S m) => CantorSum [CantorSum [ CF_nat m ]]

      (* n ^ (ω^e) = ω^(ω^e)  for e >= ω, finite n > 1 *)
    | None => CantorSum [CantorSum [e]]
    end

  | CantorSum (x1 :: _) =>
    match cantorIsFinite e with
      (* x^ (ω^0) = x *)
    | Some 0 => x

      (* (ω^x₁ + b) ^ (ω^e) = ω^(x₁ * ω^e)  when x₁ >= 1, e > 0 *)
    | _ => CantorSum [ CF_mul x1 (CantorSum [e]) ]
    end
  end.

Definition CF_exp (x:CF) (y:CF) : CF :=
  match y with
  | CantorSum ys => fold_right (fun y s => CF_mul (CF_exp_single x y) s) CF_one ys
  end.

Opaque CF_add.
Opaque CF_mul.

Lemma CF_exp_single_normal e x :
  cantorIsNormal x ->
  cantorIsNormal e ->
  cantorIsNormal (CF_exp_single x e).
Proof.
  intros. unfold CF_exp_single.
  destruct x as [xs].
  destruct xs as [|x xs].
  { apply CF_one_normal. }
  destruct x as [ls].
  destruct ls as [|l ls].
  - destruct xs.
    + apply CF_one_normal.
    + destruct (cantorIsFinite e).
      destruct n; auto.
      * generalize (CF_nat_normal n).
        simpl; intuition.
      * simpl; intuition.
  - destruct (cantorIsFinite e).
    destruct n; auto.
    simpl; intuition.
    apply CF_mul_normal; simpl in *; intuition.
    simpl; intuition.
    apply CF_mul_normal; simpl in *; intuition.
Qed.

Lemma CF_exp_normal x y :
  cantorIsNormal x ->
  cantorIsNormal y ->
  cantorIsNormal (CF_exp x y).
Proof.
  destruct y as [ys]. induction ys; simpl; intuition.
  apply CF_mul_normal; auto.
  apply CF_exp_single_normal; auto.
  apply H0. destruct ys; simpl in *; intuition.
Qed.

Lemma CF_exp_single_correct x e :
  cantorIsNormal x ->
  cantorIsNormal e ->
  cantorOrd (CF_exp_single x e) ≈ expOrd (cantorOrd x) (expOrd ω (cantorOrd e)).
Proof.
  unfold CF_exp_single. intros.
  destruct x as [xs].
  destruct e as [es].
  destruct xs as [|x xs].
  - simpl; intros.
    rewrite <- addOrd_zero_r.
    rewrite expOrd_zero.
    split.
    apply succ_least. apply expOrd_nonzero.
    rewrite expOrd_unfold.
    apply lub_least; auto with ord.
    apply sup_least. intro i.
    rewrite mulOrd_zero_r.
    apply ord_lt_le; apply succ_lt.
  - destruct x as [ls].
    destruct ls as [|l ls].
    destruct xs.
    + simpl.
      rewrite <- addOrd_zero_r.
      rewrite expOrd_zero.
      symmetry; apply expOrd_one_base.
    + case_eq (cantorIsFinite (CantorSum es)). intros n Hn.
      * rewrite (cantorIsFinite_fin (CantorSum es) n H0 Hn).
        destruct n.
        ** rewrite expOrd_zero.
           rewrite expOrd_one'. reflexivity.
           simpl. rewrite <- addOrd_le1.
           apply expOrd_nonzero.
        ** rewrite (cantorIsFinite_fin (CantorSum (CantorSum [] :: c :: xs)) _ H (refl_equal _)).
           change (S n) with (1+n)%nat.
           replace (1+n)%nat with (n+1)%nat by auto with arith.
           rewrite (natOrdSize_add n).
           rewrite expNatToOmegaPow.
           rewrite <- CF_nat_correct.
           simpl.
           repeat rewrite <- addOrd_zero_r.
           reflexivity.
           simpl.
           rewrite ord_lt_unfold; exists tt. simpl.
           rewrite natOrdSize_add.
           apply addOrd_le1.
      * intros.
        rewrite (cantorIsFinite_fin (CantorSum (CantorSum [] :: c :: xs)) _ H (refl_equal _)).
        symmetry.
        simpl cantorOrd.
        repeat rewrite <- addOrd_zero_r.
        apply expNatToOmegaInf.
        ** simpl.
           rewrite ord_lt_unfold; exists tt. simpl.
           rewrite natOrdSize_add.
           apply addOrd_le1.
        ** rewrite (cantorIsFinite_inf (CantorSum es) H1).
           reflexivity.
    + cut (cantorOrd (CantorSum es) > 0 ->
           cantorOrd (CantorSum [CF_mul (CantorSum (l :: ls)) (CantorSum [CantorSum es])]) ≈
                     expOrd (cantorOrd (CantorSum (CantorSum (l :: ls) :: xs)))
                     (expOrd ω (cantorOrd (CantorSum es)))).
      { intros Hmain.
        case_eq (cantorIsFinite (CantorSum es)).
        - intros n Hn.
          destruct n.
          + rewrite (cantorIsFinite_fin (CantorSum es) 0%nat H0 Hn).
            rewrite expOrd_zero.
            rewrite expOrd_one'.
            reflexivity.
            simpl.
            rewrite <- addOrd_le1.
            apply expOrd_nonzero.
          + apply Hmain.
            rewrite (cantorIsFinite_fin (CantorSum es) (S n) H0 Hn).
            simpl.
            rewrite ord_lt_unfold; exists tt; auto with ord.
        - intro. apply Hmain.
          rewrite <- (cantorIsFinite_inf (CantorSum es) H1).
          rewrite <- addOrd_le1.
          apply succ_lt. }
      intro.
      simpl cantorOrd at 1.
      rewrite CF_mul_correct.
      rewrite <- addOrd_zero_r.
      rewrite expOrd_mul.
      split.
      * simpl. rewrite <- addOrd_zero_r.
        apply expOrd_monotone_base.
        apply addOrd_le1.
      * simpl.
        repeat rewrite <- addOrd_zero_r.
        apply expToOmega_collapse_tower with (length xs); auto.
        ** transitivity (expOrd ω 1).
           { rewrite expOrd_one'.
             transitivity (natOrdSize (1+length xs)).
             rewrite natOrdSize_add. reflexivity.
             apply index_le.
             apply (index_lt _ 0%nat). }
           apply expOrd_monotone.
           rewrite <- addOrd_le1.
           apply succ_least. apply expOrd_nonzero.
        ** change (cantorOrd (CantorSum xs) ≤
                       expOrd ω (cantorOrd (CantorSum (l::ls))) * sz (length xs)).
           apply cantorFirstTerm_dominates; auto.
        ** apply (CantorForm_complete (CantorSum es)).
      * simpl in *; intuition.
      * simpl; intuition.
Qed.

Lemma CF_exp_correct : forall x y,
  cantorIsNormal x ->
  cantorIsNormal y ->
  cantorOrd (CF_exp x y) ≈ expOrd (cantorOrd x) (cantorOrd y).
Proof.
  intros x [ys]. induction ys; simpl; intuition.
  - do 2 rewrite expOrd_zero. rewrite <- addOrd_zero_r. reflexivity.
  - rewrite CF_mul_correct.
    + rewrite CF_exp_single_correct; auto.
      rewrite expOrd_add.
      apply mulOrd_eq_mor; try reflexivity.
      apply H0.
      destruct ys; intuition.
      simpl; intuition.
    + apply CF_exp_single_normal; auto.
    + apply (CF_exp_normal x (CantorSum ys)); auto.
      destruct ys; intuition.
      simpl; intuition.
Qed.

Definition CNF_exp (x y:CNF) : CNF :=
  exist _ (CF_exp (proj1_sig x) (proj1_sig y))
          (CF_exp_normal _ _ (proj2_sig x) (proj2_sig y)).

Theorem CNF_exp_reflects : reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> ORD) expOrd CNF_exp.
Proof.
  hnf; simpl. unfold CNF_denote. intros x [a Ha] Hxa y [b Hb] Hyb; simpl in *.
  rewrite Hxa. rewrite Hyb.
  symmetry. apply CF_exp_correct; auto.
Qed.


Theorem CNF_reflects_KnuthUp2_impossible :
  ~exists f, reflects CantorNormalForm CNF_denote (ORD ==> ORD ==> ORD) (KnuthUp 2) f.
Proof.
  intros [f Hf].
  hnf in Hf.
  specialize (Hf ω CNF_omega CNF_reflects_omega).
  hnf in Hf.
  specialize (Hf ω CNF_omega CNF_reflects_omega).
  red in Hf.
  rewrite KnuthUp_epsilon in Hf.
  apply (ord_lt_irreflexive (ε 0)).
  rewrite Hf at 1.
  apply cantorForm_below_epsilon.
Qed.


Lemma CNF_limit : limitOrdinal CNF.
Proof.
  red. simpl. split.
  exact (inhabits CNF_zero).
  hnf. simpl; intros.
  exists (CNF_add a CNF_one).
  destruct a as [a Ha]; simpl.
  unfold CNF_denote; simpl.
  rewrite <- CF_add_correct; auto.
  simpl.
  rewrite <- addOrd_zero_r.
  rewrite expOrd_zero.
  Transparent addOrd. unfold addOrd. Opaque addOrd.
  rewrite foldOrd_succ. rewrite foldOrd_zero.
  apply succ_lt.
  intros. rewrite H. apply ord_lt_le; apply succ_lt.
  apply CF_one_normal.
Qed.

Theorem CNF_expOmega_fixpoint : expOrd ω CNF ≤ CNF.
Proof.
  transitivity (expOrd ω (supOrd CNF_denote)).
  - apply expOrd_monotone.
    apply ord_isLimit.
    apply CNF_limit.
  - etransitivity; [ apply expOrd_continuous |].
    exact CNF_zero.
    apply sup_least; intro cnf.
    transitivity (CNF_denote (CNF_exp CNF_omega cnf)); [ | apply index_le ].
    apply CNF_exp_reflects.
    apply CNF_reflects_omega.
    simpl; reflexivity.
Qed.

Theorem CNF_is_ε0 : CNF ≈ ε 0.
Proof.
  split.
  - rewrite ord_le_unfold; intro cnf.
    apply cantorForm_below_epsilon.
  - apply ε0_least_expOmega_closed.
    apply CNF_expOmega_fixpoint.
Qed.

Remark ε0_least_exp_closed :
  forall X denote zeroX succX expOmegaX,
    reflects X denote ORD 0 zeroX ->
    reflects X denote (ORD ==> ORD) succOrd succX ->
    reflects X denote (ORD ==> ORD) (expOrd ω) expOmegaX ->

    ε 0 ≤ ord X denote.
Proof.
  intros X denote zeroX succX expOmegaX Hzero Hsucc HexpOmega.

  assert (Hlimit : limitOrdinal (ord X denote)).
  { simpl; split.
    - exact (inhabits zeroX).
    - hnf; simpl; intros.
      exists (succX a).
      apply ord_lt_le_trans with (succOrd (denote a)).
      apply succ_lt.
      apply Hsucc.
      simpl; reflexivity. }
  
  apply ε0_least_expOmega_closed; auto.
  transitivity (expOrd ω (supOrd denote)).
  - apply expOrd_monotone.
    apply ord_isLimit; auto.
  - etransitivity; [ apply expOrd_continuous |].
    exact zeroX.
    apply sup_least; intro x.
    transitivity (denote (expOmegaX x)).
    apply HexpOmega. simpl; reflexivity.
    apply (index_le (ord X denote)).
Qed.


Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Theorem CNF_has_enough_notations (EM:excluded_middle) :
  forall x, x < ε 0 -> exists c:CNF, x ≈ c.
Proof.
  intros.
  induction x using ordinal_induction.
  destruct (cantor_decomposition EM x) as [ls [H1 H2]].
  cut (exists ca:CNF, cantor_denote ls ≈ sz ca).
  { intros. destruct H3 as [ca Hca] ; auto.
    exists ca. rewrite <- H2. auto. }

  destruct H2. clear H3.
  induction ls; intros.
  - simpl.
    exists CNF_zero.
    reflexivity.
  - simpl.
    assert (a < x).
    { destruct (classical.order_total EM x a); auto.
      elim (ord_lt_irreflexive (ε 0)).
      apply ord_le_lt_trans with x; auto.
      simpl. unfold fixOrd.
      apply sup_least. intro i.
      induction i; simpl.
      - rewrite ord_le_unfold; intros [].
      - unfold powOmega.
        rewrite IHi.
        simpl in H1. destruct H1.
        rewrite <- H2 at 2.
        simpl.
        rewrite <- addOrd_le1.
        apply expOrd_monotone; auto. }

    destruct (H0 a H3) as [ac Hac].
    transitivity x; auto.
    destruct IHls as [cls Hcls]; auto.
    simpl in H1; intuition.
    destruct ls; simpl in *; intuition.
    transitivity a; auto.
    simpl in H2.
    rewrite <- H2.
    apply addOrd_le2.
    exists (CNF_add (CNF_exp CNF_omega ac) cls).
    apply CNF_add_reflects; auto.
    apply CNF_exp_reflects; auto.
    apply CNF_reflects_omega.
Qed.

Theorem CNF_has_enough_notations_is_classical :
  (forall x, x < ε 0 -> exists c:CNF, x ≈ c) ->
  excluded_middle.
Proof.
  intros H P.
  destruct (H (classical.truth_ord P)).
  - simpl. unfold fixOrd.
    rewrite <- (sup_le _ _ 2%nat).
    unfold iter_f.
    unfold powOmega.
    apply ord_lt_le_trans with ω.
    rewrite ord_lt_unfold.
    exists 1%nat.
    simpl.
    unfold classical.truth_ord.
    rewrite ord_le_unfold.
    simpl; intros.
    apply succ_lt.
    transitivity (expOrd ω 1).
    rewrite expOrd_one'. reflexivity.
    apply (index_lt _ 0%nat).
    apply expOrd_monotone.
    apply succ_least. apply expOrd_nonzero.

  - destruct x as [x Hx].
    simpl in *. unfold CNF_denote in H0.
    simpl in *.
    destruct x as [xs].
    destruct xs as [|x xs]; simpl in *.
    + right; intro HP.
      destruct H0.
      rewrite ord_le_unfold in H0.
      specialize (H0 HP).
      rewrite ord_lt_unfold in H0.
      destruct H0 as [[] _].
    + left.
      assert (0 < classical.truth_ord P).
      { rewrite H0.
        rewrite <- addOrd_le1.
        apply expOrd_nonzero. }
      rewrite ord_lt_unfold in H1.
      destruct H1 as [HP _]; auto.
Qed.

Theorem CNF_has_enough_notations_is_classical_for_complete_ordinals :
  (forall x, complete x -> x < ε 0 -> exists c:CNF, x ≈ c) ->
  excluded_middle.
Proof.
  intros H P.
  destruct (H (classical.truth_ord' P)).
  - apply classical.truth_ord'_complete.
  - simpl.
    unfold fixOrd.
    rewrite <- (sup_le _ _ 3%nat).
    unfold iter_f.
    unfold powOmega.
    apply ord_le_lt_trans with ω.
    unfold classical.truth_ord'.
    apply sup_least.
    intro n.
    apply lub_least.
    apply (index_le _ 1%nat).
    rewrite ord_le_unfold; intro  HP.
    simpl.
    apply index_lt.
    apply ord_le_lt_trans with (expOrd ω 1).
    rewrite expOrd_one'. auto with ord.
    apply (index_lt _ 0%nat).
    apply expOrd_increasing.
    apply (index_lt _ 1%nat).
    apply ord_lt_le_trans with (expOrd ω 1).
    rewrite expOrd_one'.
    apply (index_lt _ 1%nat).
    apply (index_lt _ 0%nat).
    apply expOrd_monotone.
    apply succ_least. apply expOrd_nonzero.
  - case_eq (cantorIsFinite (proj1_sig x)).
    + intros.
      right; intro.
      simpl in H0.
      unfold CNF_denote in  H0.
      apply cantorIsFinite_fin in H1.
      rewrite H1 in H0.
      destruct H0.
      apply (ord_lt_irreflexive ω).
      apply ord_le_lt_trans with (natOrdSize n).
      rewrite <- H0.
      unfold classical.truth_ord'.
      rewrite ord_le_unfold; intro i.
      rewrite <- (sup_le _ _ i).
      rewrite <- lub_le2.
      rewrite ord_lt_unfold. exists H2.
      simpl. reflexivity.
      apply index_lt.
      apply proj2_sig.
    + intro. left.
      destruct H0.
      assert (1 < classical.truth_ord' P).
      apply cantorIsFinite_inf in H1.
      apply ord_lt_le_trans with (sz x); auto.
      simpl.
      unfold CNF_denote.
      rewrite <- H1.
      rewrite <- H1.
      rewrite addOrd_assoc.
      rewrite <- addOrd_le1.
      Transparent addOrd. unfold addOrd. Opaque addOrd.
      rewrite foldOrd_succ.
      rewrite foldOrd_zero.
      apply succ_lt.
      intros. rewrite H3. apply ord_lt_le. apply succ_lt.
      rewrite ord_lt_unfold in H3.
      destruct H3 as [[n q] Hq]; simpl in *.
      destruct q.
      elim (ord_lt_irreflexive 1); auto with ord.
      apply ord_le_lt_trans with 0; auto.
      apply succ_lt.
      auto.
Qed.
