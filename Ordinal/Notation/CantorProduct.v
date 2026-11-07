From Stdlib Require Import Morphisms.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.

Import ListNotations.
Open Scope list.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorDecomposition.

From Stdlib Require Import ClassicalFacts.

Open Scope ord_scope.

(** * The natural product on Cantor normal forms

  The semantic natural product [nmulOrd] of NaturalProduct.v satisfies
  distributivity and the successor law only classically; their lower
  halves imply weak excluded middle, even for complete ordinals.  Here we
  compute instead.  For a notation system with a Cantor decomposition,
  the standard algorithm multiplies normal forms term by term: the
  product of [ω^α1 + ... + ω^αm] and [ω^β1 + ... + ω^βn] is the sorted
  list of all [ω^(αi ⊕ βj)].

  - The algorithm denotes the natural sum of the pairwise terms
    ([cantor_nmul_correct]), constructively.
  - On notations, it satisfies the usual laws constructively:
    commutativity, associativity, distributivity over the natural sum,
    unit and zero, the exponent law and the successor law.  These rest on
    the uniqueness of Cantor normal forms ([cantor_nadd_unique]), which
    the decidable comparison of notations makes constructive.
  - Given interpolants, it reflects [nmulOrd] constructively
    ([cantor_nmul_reflects]), so the semantic product does satisfy all
    these laws on notations.  Interpolants are needed only at epsilon
    notations ([cantor_nmul_reflects_epsilons]).  With excluded middle, interpolants are not
    needed ([cantor_nmul_reflects_EM]).

  The constructive reflection works because, on trees whose children are
  hereditarily notations, every comparison that the classical proofs
  decide with excluded middle is a comparison of notations
  (NaturalProduct.v, section [decidable_universe]); interpolants make the
  denoted trees equivalent to such trees.

  We write [V xs] for the natural sum of the ω-powers of a list of
  exponents. *)

Local Abbreviation V := NaturalArith.cantor_denote_nadd.

(** ** The algebra of pairwise products of exponent lists *)

Lemma nadd_middle_swap p q r s : (p ⊕ q) ⊕ (r ⊕ s) ≈ (p ⊕ r) ⊕ (q ⊕ s).
Proof.
  rewrite <- !naddOrd_assoc. apply naddOrd_eq_mor; [reflexivity|].
  rewrite !naddOrd_assoc. apply naddOrd_eq_mor; [apply naddOrd_comm | reflexivity].
Qed.

Lemma V_app xs ys : V (xs ++ ys) ≈ V xs ⊕ V ys.
Proof. apply NaturalArith.cantor_denote_nadd_app. Qed.

Lemma V_perm xs ys : Permutation xs ys -> V xs ≈ V ys.
Proof.
  induction 1; simpl.
  - reflexivity.
  - rewrite IHPermutation. reflexivity.
  - rewrite !naddOrd_assoc. rewrite (naddOrd_comm (expOrd ω y)). reflexivity.
  - rewrite IHPermutation1. auto.
Qed.

Lemma V_eq2 xs ys : Forall2 ord_eq xs ys -> V xs ≈ V ys.
Proof.
  induction 1; simpl; [reflexivity|]. rewrite H, IHForall2. reflexivity.
Qed.

Lemma Forall2_map_eq (g h:Ord -> Ord) zs :
  (forall z, g z ≈ h z) -> Forall2 ord_eq (map g zs) (map h zs).
Proof. intro H. induction zs; simpl; constructor; auto. Qed.

Lemma V_cnf_nil_r xs : V (cnf_prod xs []) ≈ 0.
Proof. induction xs; simpl; auto with ord. Qed.

Lemma V_cnf_cons_l a xs ys :
  V (cnf_prod (a::xs) ys) ≈ V (map (fun b => a ⊕ b) ys) ⊕ V (cnf_prod xs ys).
Proof. unfold cnf_prod. simpl. apply V_app. Qed.

Lemma V_cnf_cons_r xs b ys :
  V (cnf_prod xs (b::ys)) ≈ V (map (fun a => a ⊕ b) xs) ⊕ V (cnf_prod xs ys).
Proof.
  induction xs as [|a xs IH].
  - simpl. rewrite naddOrd_zero_l. reflexivity.
  - rewrite !V_cnf_cons_l, IH. cbn [map NaturalArith.cantor_denote_nadd].
    apply nadd_middle_swap.
Qed.

Lemma V_cnf_comm xs ys : V (cnf_prod xs ys) ≈ V (cnf_prod ys xs).
Proof.
  induction xs as [|a xs IH].
  - simpl. symmetry. apply V_cnf_nil_r.
  - rewrite V_cnf_cons_l, V_cnf_cons_r, IH.
    apply naddOrd_eq_mor; [|reflexivity].
    apply V_eq2, Forall2_map_eq. intro; apply naddOrd_comm.
Qed.

Lemma V_cnf_app_r xs ys zs :
  V (cnf_prod xs (ys ++ zs)) ≈ V (cnf_prod xs ys) ⊕ V (cnf_prod xs zs).
Proof.
  induction ys as [|b ys IH]; simpl.
  - rewrite V_cnf_nil_r, naddOrd_zero_l. reflexivity.
  - rewrite !V_cnf_cons_r, IH. apply naddOrd_assoc.
Qed.

Lemma V_cnf_app_l xs ys zs :
  V (cnf_prod (xs ++ ys) zs) ≈ V (cnf_prod xs zs) ⊕ V (cnf_prod ys zs).
Proof. rewrite !(V_cnf_comm _ zs). apply V_cnf_app_r. Qed.

(** Two exponent lists are interchangeable in products. *)
Local Abbreviation prod_equiv L1 L2 :=
  (forall ws, V (cnf_prod ws L1) ≈ V (cnf_prod ws L2)).

Lemma prod_equiv_refl L : prod_equiv L L.
Proof. intro; reflexivity. Qed.

Lemma prod_equiv_sym L1 L2 : prod_equiv L1 L2 -> prod_equiv L2 L1.
Proof. intros H ws. symmetry; auto. Qed.

Lemma prod_equiv_trans L1 L2 L3 :
  prod_equiv L1 L2 -> prod_equiv L2 L3 -> prod_equiv L1 L3.
Proof. intros H1 H2 ws. rewrite H1; auto. Qed.

Lemma prod_equiv_eq2 L1 L2 : Forall2 ord_eq L1 L2 -> prod_equiv L1 L2.
Proof.
  induction 1; intro ws; [reflexivity|].
  rewrite !V_cnf_cons_r, IHForall2.
  apply naddOrd_eq_mor; [|reflexivity].
  apply V_eq2. induction ws; simpl; constructor; auto.
  rewrite H. reflexivity.
Qed.

Lemma prod_equiv_perm L1 L2 : Permutation L1 L2 -> prod_equiv L1 L2.
Proof.
  induction 1; intro ws.
  - reflexivity.
  - rewrite !V_cnf_cons_r, IHPermutation. reflexivity.
  - rewrite !V_cnf_cons_r. rewrite !naddOrd_assoc.
    rewrite (naddOrd_comm (V (map (fun a => a ⊕ y) ws))). reflexivity.
  - rewrite IHPermutation1. auto.
Qed.

Lemma prod_equiv_l L1 L2 ws :
  prod_equiv L1 L2 -> V (cnf_prod L1 ws) ≈ V (cnf_prod L2 ws).
Proof. intro H. rewrite !(V_cnf_comm _ ws). auto. Qed.

Lemma prod_equiv_V L1 L2 : prod_equiv L1 L2 -> V L1 ≈ V L2.
Proof.
  intro H. specialize (H [0]).
  unfold cnf_prod in H. simpl in H. rewrite !app_nil_r in H.
  rewrite (V_eq2 (map (fun b => 0 ⊕ b) L1) L1), (V_eq2 (map (fun b => 0 ⊕ b) L2) L2) in H;
    auto; clear H; [induction L2 | induction L1]; simpl; constructor; auto;
    apply naddOrd_zero_l.
Qed.

Lemma cnf_prod_single a b : V (cnf_prod [a] [b]) ≈ expOrd ω (a ⊕ b).
Proof. simpl. rewrite !naddOrd_zero_r. reflexivity. Qed.

Lemma V_cnf_assoc xs ys zs :
  V (cnf_prod (cnf_prod xs ys) zs) ≈ V (cnf_prod xs (cnf_prod ys zs)).
Proof.
  apply V_eq2.
  induction xs as [|a xs IH]; simpl; [constructor|].
  unfold cnf_prod at 1. rewrite flat_map_app. fold (cnf_prod (map (fun b => a ⊕ b) ys) zs).
  fold (cnf_prod (cnf_prod xs ys) zs).
  unfold cnf_prod at 3. simpl. fold (cnf_prod xs (cnf_prod ys zs)).
  apply Forall2_app; auto.
  clear IH. induction ys as [|b ys IH]; simpl; [constructor|].
  unfold cnf_prod at 2. simpl. fold (cnf_prod ys zs).
  rewrite map_app. apply Forall2_app; auto.
  rewrite map_map. apply Forall2_map_eq. intro; symmetry; apply naddOrd_assoc.
Qed.

(** ** Uniqueness of Cantor normal forms, and the algorithm *)

Section cantor_product.
  Variable A : Type.
  Variable f : A -> Ord.
  Variable P : A -> Prop.
  Variable X : has_cantor_decomposition f P.

  Lemma V_map_complete : forall a, complete (f a).
  Proof. apply (cantor_decomp_complete X). Qed.

  Lemma ordered_head_le : forall xs x,
      cantor_ordered f (x::xs) -> forall z, In z (x::xs) -> f z ≤ f x.
  Proof.
    induction xs as [|y ys IH]; intros x Hord z Hz.
    - destruct Hz as [Hz|[]]. subst. reflexivity.
    - destruct Hord as [Hxy Hord].
      destruct Hz as [Hz|Hz]; [subst; reflexivity|].
      rewrite (IH y Hord z Hz). auto.
  Qed.

  Lemma V_below_power : forall xs e d,
      (forall z, In z xs -> f z ≤ e) -> e < d -> complete d ->
      V (map f xs) < expOrd ω d.
  Proof.
    induction xs as [|x xs IH]; intros e d Hxs Hed Hd; simpl.
    - apply expOrd_nonzero.
    - apply nadd_closed_con; auto.
      + apply expOrd_increasing; auto with ord.
        apply ord_le_lt_trans with e; auto. apply Hxs; simpl; auto.
      + apply IH with e; auto. intros; apply Hxs; simpl; auto.
  Qed.

  (** Two normal forms with the same value agree term by term.  The
      comparison of the leading exponents is decided by the notation
      system; a strictly smaller leading exponent bounds the whole sum
      below the other's leading power, by closure under natural sum. *)
  Theorem cantor_nadd_unique : forall xs ys,
      each P xs -> each P ys ->
      cantor_ordered f xs -> cantor_ordered f ys ->
      V (map f xs) ≈ V (map f ys) ->
      Forall2 ord_eq (map f xs) (map f ys).
  Proof.
    induction xs as [|x xs IH]; intros [|y ys] Hxs Hys Hox Hoy Heq; simpl in *.
    - constructor.
    - elim (ord_lt_irreflexive 0). rewrite Heq at 2.
      apply ord_lt_le_trans with (expOrd ω (f y)); [apply expOrd_nonzero | apply naddOrd_le1].
    - elim (ord_lt_irreflexive 0). rewrite <- Heq at 2.
      apply ord_lt_le_trans with (expOrd ω (f x)); [apply expOrd_nonzero | apply naddOrd_le1].
    - destruct Hxs as [Hx Hxs], Hys as [Hy Hys].
      assert (Hlt : forall u us v vs, P u -> P v ->
                cantor_ordered f (u::us) -> f u < f v ->
                ~ V (map f (u::us)) ≈ V (map f (v::vs))).
      { intros u us v vs Hu Hv Hou Huv H.
        apply (ord_lt_irreflexive (expOrd ω (f v))).
        apply ord_le_lt_trans with (V (map f (u::us))).
        - rewrite H. simpl. apply naddOrd_le1.
        - apply V_below_power with (f u); auto.
          + apply ordered_head_le; auto.
          + apply V_map_complete. }
      generalize (cantor_decomp_compare_correct X x y Hx Hy).
      destruct (cantor_decomp_compare X x y); simpl; intro Hc.
      + elim (Hlt x xs y ys); auto.
      + constructor; auto.
        apply IH; auto.
        * destruct xs; simpl in *; intuition.
        * destruct ys; simpl in *; intuition.
        * rewrite Hc in Heq.
          split; apply (naddOrd_cancel_le _ _ (expOrd ω (f y)));
            rewrite !(naddOrd_comm _ (expOrd ω (f y))); apply Heq.
      + elim (Hlt y ys x xs); auto. symmetry; auto.
  Qed.

  Lemma dec_value x : P x -> f x ≈ V (map f (cantor_decompose X x)).
  Proof.
    intro Hx. destruct (cantor_decompose_correct X x Hx) as [H1 [H2 H3]].
    rewrite H3. rewrite (cantor_denote_nadd_eq X); auto.
    rewrite cantor_denote_nadd_map. reflexivity.
  Qed.

  Lemma dec_equiv x L :
    P x -> each P L -> cantor_ordered f L -> f x ≈ V (map f L) ->
    prod_equiv (map f (cantor_decompose X x)) (map f L).
  Proof.
    intros Hx HL HoL H.
    destruct (cantor_decompose_correct X x Hx) as [H1 [H2 H3]].
    apply prod_equiv_eq2, cantor_nadd_unique; auto.
    rewrite <- dec_value; auto.
  Qed.

  Lemma nadd_list_perm : forall xs ys,
      Permutation (cantor_nadd_list X xs ys) (xs ++ ys).
  Proof.
    induction xs as [|x xs IHx]; [intros [|y ys]; simpl; reflexivity|].
    induction ys as [|y ys IHy]; simpl.
    - rewrite app_nil_r. reflexivity.
    - destruct (cantor_decomp_compare X x y).
      + rewrite IHy. exact (Permutation_middle (x::xs) ys y).
      + constructor. apply IHx.
      + constructor. apply IHx.
  Qed.

  Definition cantor_sort (l:list A) : list A :=
    fold_right (fun e acc => cantor_nadd_list X [e] acc) [] l.

  Lemma cantor_sort_correct : forall l,
      each P l ->
      each P (cantor_sort l) /\ cantor_ordered f (cantor_sort l) /\
      Permutation (cantor_sort l) l.
  Proof.
    induction l as [|e l IH]; intros Hl.
    - simpl. intuition.
    - destruct Hl as [He Hl]. destruct (IH Hl) as [H1 [H2 H3]].
      destruct (cantor_nadd_list_correct X [e] (cantor_sort l)) as [H4 [H5 _]];
        try exact H1; try exact H2; try (simpl; tauto).
      change (cantor_sort (e::l)) with (cantor_nadd_list X [e] (cantor_sort l)).
      split; [|split]; auto.
      rewrite nadd_list_perm. simpl. constructor. auto.
  Qed.

  Definition cantor_pairs (xs ys:list A) : list A :=
    flat_map (fun x => map (fun y => cantor_nadd X x y) ys) xs.

  Lemma cantor_pairs_correct : forall xs ys,
      each P xs -> each P ys ->
      each P (cantor_pairs xs ys) /\
      Forall2 ord_eq (map f (cantor_pairs xs ys)) (cnf_prod (map f xs) (map f ys)).
  Proof.
    induction xs as [|x xs IH]; intros ys Hxs Hys; simpl; [split; auto; constructor|].
    destruct Hxs as [Hx Hxs]. destruct (IH ys Hxs Hys) as [H1 H2].
    unfold cantor_pairs in *. simpl. rewrite map_app.
    split.
    - apply each_app. split; auto. clear -Hx Hys.
      induction ys; simpl in *; intuition. apply cantor_nadd_correct; auto.
    - unfold cnf_prod. simpl. apply Forall2_app; auto.
      clear -Hx Hys. induction ys as [|y ys IH]; simpl in *; constructor; intuition.
      apply cantor_nadd_correct; auto.
  Qed.

  Definition cantor_nmul (x y:A) : A :=
    cantor_recompose X (cantor_sort (cantor_pairs (cantor_decompose X x) (cantor_decompose X y))).

  Lemma cantor_nmul_terms x y : P x -> P y ->
      exists L, each P L /\ cantor_ordered f L /\
        P (cantor_nmul x y) /\ f (cantor_nmul x y) ≈ V (map f L) /\
        prod_equiv (map f L) (cnf_prod (map f (cantor_decompose X x)) (map f (cantor_decompose X y))).
  Proof.
    intros Hx Hy.
    destruct (cantor_decompose_correct X x Hx) as [Hx1 [Hx2 Hx3]].
    destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
    destruct (cantor_pairs_correct (cantor_decompose X x) (cantor_decompose X y)) as [Hp1 Hp2]; auto.
    destruct (cantor_sort_correct _ Hp1) as [Hs1 [Hs2 Hs3]].
    destruct (cantor_recompose_correct X _ Hs1 Hs2) as [Hr1 Hr2].
    exists (cantor_sort (cantor_pairs (cantor_decompose X x) (cantor_decompose X y))).
    split; [|split; [|split; [|split]]]; auto.
    - unfold cantor_nmul. rewrite <- Hr2.
      rewrite (cantor_denote_nadd_eq X); auto.
      rewrite cantor_denote_nadd_map. reflexivity.
    - eapply prod_equiv_trans; [apply prod_equiv_perm, Permutation_map, Hs3|].
      apply prod_equiv_eq2; auto.
  Qed.

  (** The algorithm computes the natural sum of the pairwise terms. *)
  Theorem cantor_nmul_correct x y : P x -> P y ->
      P (cantor_nmul x y) /\
      f (cantor_nmul x y) ≈ V (cnf_prod (map f (cantor_decompose X x)) (map f (cantor_decompose X y))).
  Proof.
    intros Hx Hy.
    destruct (cantor_nmul_terms x y Hx Hy) as [L [H1 [H2 [H3 [H4 H5]]]]].
    split; auto. rewrite H4. apply prod_equiv_V; auto.
  Qed.

  Lemma cantor_nmul_dec x y : P x -> P y ->
      prod_equiv (map f (cantor_decompose X (cantor_nmul x y))) (cnf_prod (map f (cantor_decompose X x)) (map f (cantor_decompose X y))).
  Proof.
    intros Hx Hy.
    destruct (cantor_nmul_terms x y Hx Hy) as [L [H1 [H2 [H3 [H4 H5]]]]].
    eapply prod_equiv_trans; [|exact H5]. apply dec_equiv; auto.
  Qed.

  Lemma dec_proper x y : P x -> P y -> f x ≈ f y ->
      prod_equiv (map f (cantor_decompose X x)) (map f (cantor_decompose X y)).
  Proof.
    intros Hx Hy H.
    destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
    apply dec_equiv; auto. rewrite <- dec_value; auto.
  Qed.

  (** ** The laws, constructively *)

  Theorem cantor_nmul_proper x x' y y' :
    P x -> P x' -> P y -> P y' -> f x ≈ f x' -> f y ≈ f y' ->
    f (cantor_nmul x y) ≈ f (cantor_nmul x' y').
  Proof.
    intros Hx Hx' Hy Hy' Hxx Hyy.
    rewrite (proj2 (cantor_nmul_correct x y Hx Hy)), (proj2 (cantor_nmul_correct x' y' Hx' Hy')).
    rewrite (dec_proper y y'); auto.
    apply prod_equiv_l, dec_proper; auto.
  Qed.

  Theorem cantor_nmul_comm x y : P x -> P y ->
    f (cantor_nmul x y) ≈ f (cantor_nmul y x).
  Proof.
    intros Hx Hy.
    rewrite (proj2 (cantor_nmul_correct x y Hx Hy)), (proj2 (cantor_nmul_correct y x Hy Hx)).
    apply V_cnf_comm.
  Qed.

  Theorem cantor_nmul_assoc x y z : P x -> P y -> P z ->
    f (cantor_nmul (cantor_nmul x y) z) ≈ f (cantor_nmul x (cantor_nmul y z)).
  Proof.
    intros Hx Hy Hz.
    destruct (cantor_nmul_correct x y Hx Hy) as [Hxy _].
    destruct (cantor_nmul_correct y z Hy Hz) as [Hyz _].
    rewrite (proj2 (cantor_nmul_correct _ z Hxy Hz)), (proj2 (cantor_nmul_correct x _ Hx Hyz)).
    rewrite (prod_equiv_l _ _ _ (cantor_nmul_dec x y Hx Hy)).
    rewrite (cantor_nmul_dec y z Hy Hz).
    apply V_cnf_assoc.
  Qed.

  Theorem cantor_nmul_nadd_r x y z : P x -> P y -> P z ->
    f (cantor_nmul x (cantor_nadd X y z)) ≈
    f (cantor_nadd X (cantor_nmul x y) (cantor_nmul x z)).
  Proof.
    intros Hx Hy Hz.
    destruct (cantor_nadd_correct X y z Hy Hz) as [Hyz Hyz'].
    destruct (cantor_nmul_correct x y Hx Hy) as [Hxy Hxy'].
    destruct (cantor_nmul_correct x z Hx Hz) as [Hxz Hxz'].
    destruct (cantor_nadd_correct X _ _ Hxy Hxz) as [_ ->].
    rewrite Hxy', Hxz', (proj2 (cantor_nmul_correct x _ Hx Hyz)).
    destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
    destruct (cantor_decompose_correct X z Hz) as [Hz1 [Hz2 Hz3]].
    destruct (cantor_nadd_list_correct X (cantor_decompose X y) (cantor_decompose X z)) as [Hm1 [Hm2 Hm3]]; auto.
    rewrite (dec_equiv (cantor_nadd X y z) (cantor_nadd_list X (cantor_decompose X y) (cantor_decompose X z))); auto.
    - rewrite (prod_equiv_perm _ _ (Permutation_map f (nadd_list_perm (cantor_decompose X y) (cantor_decompose X z)))).
      rewrite map_app. apply V_cnf_app_r.
    - rewrite Hyz', !dec_value; auto.
      rewrite !cantor_denote_nadd_map in Hm3. symmetry. exact Hm3.
  Qed.

  Theorem cantor_nmul_nadd_l x y z : P x -> P y -> P z ->
    f (cantor_nmul (cantor_nadd X x y) z) ≈
    f (cantor_nadd X (cantor_nmul x z) (cantor_nmul y z)).
  Proof.
    intros Hx Hy Hz.
    destruct (cantor_nadd_correct X x y Hx Hy) as [Hxy _].
    destruct (cantor_nmul_correct x z Hx Hz) as [Hxz _].
    destruct (cantor_nmul_correct y z Hy Hz) as [Hyz _].
    destruct (cantor_nmul_correct z x Hz Hx) as [Hzx _].
    destruct (cantor_nmul_correct z y Hz Hy) as [Hzy _].
    rewrite cantor_nmul_comm, cantor_nmul_nadd_r; auto.
    destruct (cantor_nadd_correct X _ _ Hzx Hzy) as [_ ->].
    destruct (cantor_nadd_correct X _ _ Hxz Hyz) as [_ ->].
    rewrite !(cantor_nmul_comm z); auto. reflexivity.
  Qed.

  Theorem cantor_nmul_zero x : P x ->
    f (cantor_nmul x (cantor_zero X)) ≈ 0.
  Proof.
    intros Hx. destruct (cantor_zero_reflects X) as [Hz1 Hz2].
    rewrite (proj2 (cantor_nmul_correct x _ Hx Hz2)).
    rewrite (dec_equiv (cantor_zero X) [] Hz2 I I ltac:(symmetry; exact Hz1)).
    apply V_cnf_nil_r.
  Qed.

  Theorem cantor_nmul_one x : P x ->
    f (cantor_nmul x (cantor_nat X 1)) ≈ f x.
  Proof.
    intros Hx. destruct (cantor_nat_correct X 1) as [H1 H2].
    destruct (cantor_zero_reflects X) as [Hz1 Hz2].
    rewrite (proj2 (cantor_nmul_correct x _ Hx H2)).
    assert (Hone : f (cantor_nat X 1) ≈ V (map f [cantor_zero X])).
    { simpl. rewrite H1, <- Hz1, expOrd_zero, naddOrd_zero_r. reflexivity. }
    rewrite (dec_equiv (cantor_nat X 1) [cantor_zero X] H2 ltac:(simpl; auto) ltac:(simpl; auto) Hone).
    simpl map. rewrite V_cnf_cons_r, V_cnf_nil_r, naddOrd_zero_r.
    rewrite (dec_value x Hx).
    apply V_eq2. clear -Hz1.
    induction (map f (cantor_decompose X x)); simpl; constructor; auto.
    rewrite <- Hz1. apply naddOrd_zero_r.
  Qed.

  (** The exponent law, for single powers [ω^a]. *)
  Theorem cantor_nmul_exp a b : P a -> P b ->
    f (cantor_nmul (cantor_recompose X [a]) (cantor_recompose X [b])) ≈ f (cantor_recompose X [cantor_nadd X a b]).
  Proof.
    intros Ha Hb.
    destruct (cantor_nadd_correct X a b Ha Hb) as [Hab Hab'].
    destruct (cantor_recompose_correct X [a]) as [Ha1 Ha2]; simpl; auto.
    destruct (cantor_recompose_correct X [b]) as [Hb1 Hb2]; simpl; auto.
    destruct (cantor_recompose_correct X [cantor_nadd X a b]) as [Hc1 Hc2]; simpl; auto.
    rewrite (proj2 (cantor_nmul_correct _ _ Ha1 Hb1)).
    rewrite (prod_equiv_l _ _ _ (dec_equiv (cantor_recompose X [a]) [a] Ha1 ltac:(simpl; auto) ltac:(simpl; auto)
                                   ltac:(rewrite <- Ha2; simpl; rewrite addOrd_zero_r, naddOrd_zero_r; reflexivity))).
    rewrite (dec_equiv (cantor_recompose X [b]) [b]); simpl; auto.
    - rewrite <- Hc2. simpl. rewrite Hab', addOrd_zero_r, !naddOrd_zero_r. reflexivity.
    - rewrite <- Hb2. simpl. rewrite addOrd_zero_r, naddOrd_zero_r. reflexivity.
  Qed.

  (** The successor law: [x ⊗ (y+1) = x ⊗ y ⊕ x]. *)
  Theorem cantor_nmul_succ x y : P x -> P y ->
    f (cantor_nmul x (cantor_succ X y)) ≈ f (cantor_nadd X (cantor_nmul x y) x).
  Proof.
    intros Hx Hy.
    destruct (cantor_succ_reflects X (conj (ord_eq_refl (f y)) Hy)) as [Hs1 Hs2].
    destruct (cantor_nat_correct X 1) as [H1 H2].
    destruct (cantor_nadd_correct X y _ Hy H2) as [Hy1 Hy1'].
    destruct (cantor_nmul_correct x y Hx Hy) as [Hxy _].
    destruct (cantor_nmul_correct x _ Hx H2) as [Hx1 _].
    rewrite (cantor_nmul_proper x x (cantor_succ X y) (cantor_nadd X y (cantor_nat X 1))); auto.
    - rewrite cantor_nmul_nadd_r; auto.
      destruct (cantor_nadd_correct X _ _ Hxy Hx1) as [_ ->].
      destruct (cantor_nadd_correct X _ _ Hxy Hx) as [_ ->].
      rewrite cantor_nmul_one; auto. reflexivity.
    - reflexivity.
    - rewrite <- Hs1, Hy1', H1. simpl.
      rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
  Qed.

  (** ** Reflection of the semantic product, classically *)

  Lemma cantor_ordered_sequence L : each P L -> cantor_ordered f L ->
    exists b, cantor_sequence b (map f L).
  Proof.
    destruct L as [|x L]; intros HL Ho; [exists 0; simpl; auto|].
    exists (f x). simpl. split; [reflexivity|].
    apply cantor_sequence_dec_weaken, (cantor_ordered_dec X); auto.
  Qed.

  Theorem cantor_nmul_reflects_EM (EM:excluded_middle) :
    reflects A f P (ORD ==> ORD ==> ORD) nmulOrd cantor_nmul.
  Proof.
    simpl. intros u x [Hu Hx] v y [Hv Hy].
    destruct (cantor_nmul_correct x y Hx Hy) as [H1 H2].
    split; auto. rewrite H2, Hu, Hv.
    destruct (cantor_decompose_correct X x Hx) as [Hx1 [Hx2 Hx3]].
    destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
    destruct (cantor_ordered_sequence _ Hx1 Hx2) as [bx Hbx].
    destruct (cantor_ordered_sequence _ Hy1 Hy2) as [b2 Hby].
    rewrite Hx3, Hy3, !cantor_denote_map.
    apply nmulOrd_cantor with bx b2; auto.
  Qed.

End cantor_product.

(** ** The lower half of the reflection, constructively

  Given interpolants, a notation's value is equivalent to the tree [T z]
  whose children are exactly the notations below it, recursively.  On
  such trees every corner and every move of the product game is a
  notation, so the comparisons in the proof of superdistributivity are
  decided by the notation system ([nmulOrd_distrib_lower_Q]).  The
  exponent law's lower bound then follows by induction, using
  interpolants to bound children by notations and closure under natural
  sum; assembling the pairwise terms gives
  [f (cantor_nmul x y) ≤ nmulOrd (f x) (f y)]. *)

Lemma nadd_lt_elim z x y : z < x ⊕ y ->
  (exists i, z ≤ x i ⊕ y) \/ (exists j, z ≤ x ⊕ y j).
Proof.
  rewrite naddOrd_unfold. intro H. apply lub_lt in H.
  destruct H as [H|H]; rewrite ord_lt_unfold in H; destruct H as [i Hi];
    [left | right]; exists i; exact Hi.
Qed.

Section cantor_product_lower.
  Variable A : Type.
  Variable f : A -> Ord.
  Variable P : A -> Prop.
  Variable X : has_cantor_decomposition f P.
  Hypothesis Hinterp : has_all_interpolants f P.

  Definition Qn (z:Ord) := exists a, P a /\ z ≈ f a.

  Lemma Qn_eq x y : x ≈ y -> Qn x -> Qn y.
  Proof. intros H [a [Ha Hx]]. exists a. split; auto. rewrite <- H; auto. Qed.

  Lemma Qn_dec x y : Qn x -> Qn y -> x < y \/ y ≤ x.
  Proof.
    intros [a [Ha Hx]] [b [Hb Hy]].
    generalize (cantor_decomp_compare_correct X a b Ha Hb).
    destruct (cantor_decomp_compare X a b); simpl; intro H;
      rewrite Hx, Hy; [left; auto | right; apply H | right; apply ord_lt_le; auto].
  Qed.

  Lemma Qn_zero : Qn 0.
  Proof. destruct (cantor_zero_reflects X) as [H1 H2]. exists (cantor_zero X); auto. Qed.

  Lemma Qn_nadd x y : Qn x -> Qn y -> Qn (x ⊕ y).
  Proof.
    intros [a [Ha Hx]] [b [Hb Hy]].
    destruct (cantor_nadd_correct X a b Ha Hb) as [H1 H2].
    exists (cantor_nadd X a b). split; auto. rewrite H2, Hx, Hy. reflexivity.
  Qed.

  Let QHn := QH Qn.

  Lemma QHn_nadd x y : QHn x -> QHn y -> QHn (x ⊕ y).
  Proof. exact (QH_nadd Qn Qn_nadd x y). Qed.

  Lemma QHn_zero : QHn 0.
  Proof. apply QH_zero, Qn_zero. Qed.

  (** The canonical tree of notations below [z]. *)
  Fixpoint Trec (z:Ord) (H:Acc ord_lt z) {struct H} : Ord :=
    match H with
    | Acc_intro _ H' =>
        ord {b:A & (P b /\ f b < z)}
            (fun bh => Trec (f (projT1 bh)) (H' _ (proj2 (projT2 bh))))
    end.

  Lemma Trec_le : forall z H, Trec z H ≤ z.
  Proof.
    induction z as [z IH] using ordinal_induction. intros [H]. simpl.
    rewrite ord_le_unfold. intros [b [Hb Hlt]]. simpl.
    apply ord_le_lt_trans with (f b); auto.
  Qed.

  Lemma Trec_ge : forall z H, has_interpolants f P z -> z ≤ Trec z H.
  Proof.
    induction z as [z IH] using ordinal_induction. intros [H] Hz.
    rewrite ord_le_unfold. intro i.
    rewrite has_interpolants_unfold in Hz.
    destruct (Hz (ordSize z i)) as [y [Hy1 [Hy2 [Hy3 Hy4]]]]; [apply index_lt|].
    simpl. rewrite ord_lt_unfold.
    exists (existT _ y (conj Hy1 Hy3)). simpl.
    rewrite Hy2. apply IH; auto.
  Qed.

  Lemma Trec_eq z H a : P a -> z ≈ f a -> Trec z H ≈ z.
  Proof.
    intros Ha Hz. split; [apply Trec_le|]. apply Trec_ge.
    rewrite Hz. apply Hinterp; auto.
  Qed.

  Lemma Trec_HQ : forall z H, HQ Qn (Trec z H).
  Proof.
    induction z as [z IH] using ordinal_induction. intros [H]. simpl.
    intros [b [Hb Hlt]]. simpl. split; auto.
    exists b. split; auto. apply Trec_eq with b; auto. reflexivity.
  Qed.

  Definition Tn (z:Ord) := Trec z (ord_lt_wf z).

  Lemma Tn_QH a : P a -> QHn (Tn (f a)).
  Proof.
    intro Ha. split; [|apply Trec_HQ].
    exists a. split; auto. apply Trec_eq with a; auto. reflexivity.
  Qed.

  Lemma Tn_eq a : P a -> Tn (f a) ≈ f a.
  Proof. intro Ha. apply Trec_eq with a; auto. reflexivity. Qed.

  (** The tree of the power [ω^a]. *)
  Definition En (a:A) := Tn (f (cantor_recompose X [a])).

  Lemma En_props a : P a -> QHn (En a) /\ En a ≈ expOrd ω (f a).
  Proof.
    intro Ha. destruct (cantor_recompose_correct X [a]) as [H1 H2]; simpl; auto.
    split; [apply Tn_QH; auto|].
    unfold En. rewrite Tn_eq; auto. rewrite <- H2. simpl. apply addOrd_zero_r.
  Qed.

  Lemma nrep_power_below k a a' : P a -> f a' < f a ->
    nrep k (expOrd ω (f a')) < expOrd ω (f a).
  Proof.
    intros Ha H. induction k; simpl.
    - apply expOrd_nonzero.
    - apply nadd_closed_con; auto.
      + apply (cantor_decomp_complete X).
      + apply expOrd_increasing; auto with ord.
  Qed.

  Theorem exp_lower_n : forall a b, P a -> P b ->
    expOrd ω (f a ⊕ f b) ≤ nmulOrd (En a) (En b).
  Proof.
    intros a0 b0 Ha0 Hb0.
    generalize (ord_le_refl (f a0 ⊕ f b0)). generalize (f a0 ⊕ f b0) at 2 as o.
    intro o. revert a0 b0 Ha0 Hb0.
    induction o as [o IH] using ordinal_induction.
    intros a b Ha Hb Ho.
    destruct (En_props a Ha) as [HEa HEa'].
    destruct (En_props b Hb) as [HEb HEb'].
    assert (Hnrep := nmul_nrep_lower_Q Qn Qn_eq Qn_dec Qn_zero Qn_nadd).
    rewrite expOrd_unfold. apply lub_least.
    { rewrite <- (nmulOrd_one 1) at 1.
      apply nmulOrd_monotone; apply succ_least;
        [rewrite HEa' | rewrite HEb']; apply expOrd_nonzero. }
    apply sup_least. intro i.
    rewrite mulOrd_unfold. apply sup_least. intro n.
    rewrite <- mulOrd_succ. rewrite (mul_nat_le_nrep _ (S n)).
    destruct (nadd_lt_elim _ _ _ (index_lt (f a ⊕ f b) i)) as [[j Hj]|[j Hj]].
    - generalize (Hinterp a Ha). rewrite has_interpolants_unfold. intro HI.
      destruct (HI (ordSize (f a) j)) as [a1 [Ha1 [Ha1le [Ha1lt _]]]]; [apply index_lt|].
      destruct (En_props a1 Ha1) as [HE1 HE1eq].
      assert (Hlt : f a1 ⊕ f b < o).
      { eapply ord_lt_le_trans; [apply naddOrd_increasing1; exact Ha1lt | exact Ho]. }
      rewrite Hj, Ha1le.
      rewrite (nrep_mono _ _ _ (IH (f a1 ⊕ f b) Hlt a1 b Ha1 Hb (ord_le_refl _))).
      rewrite Hnrep; auto.
      apply nmulOrd_monotone; [|reflexivity].
      rewrite HEa'. apply ord_lt_le.
      rewrite (nrep_mono _ _ _ (proj1 HE1eq)).
      apply nrep_power_below; auto.
    - generalize (Hinterp b Hb). rewrite has_interpolants_unfold. intro HI.
      destruct (HI (ordSize (f b) j)) as [b1 [Hb1 [Hb1le [Hb1lt _]]]]; [apply index_lt|].
      destruct (En_props b1 Hb1) as [HE1 HE1eq].
      assert (Hlt : f a ⊕ f b1 < o).
      { eapply ord_lt_le_trans; [apply naddOrd_increasing2; exact Hb1lt | exact Ho]. }
      rewrite Hj, Hb1le.
      rewrite (nrep_mono _ _ _ (IH (f a ⊕ f b1) Hlt a b1 Ha Hb1 (ord_le_refl _))).
      rewrite (nmulOrd_comm (En a) (En b1)), (nmulOrd_comm (En a) (En b)).
      rewrite Hnrep; auto.
      apply nmulOrd_monotone; [|reflexivity].
      rewrite HEb'. apply ord_lt_le.
      rewrite (nrep_mono _ _ _ (proj1 HE1eq)).
      apply nrep_power_below; auto.
  Qed.

  Fixpoint VE (xs:list A) : Ord :=
    match xs with [] => 0 | x::xs' => En x ⊕ VE xs' end.

  Lemma VE_props xs : each P xs -> QHn (VE xs) /\ VE xs ≈ V (map f xs).
  Proof.
    induction xs as [|x xs IH]; simpl; intro H.
    - split; [apply QHn_zero | reflexivity].
    - destruct H as [Hx Hxs]. destruct (IH Hxs) as [H1 H2].
      destruct (En_props x Hx) as [H3 H4].
      split; [apply QHn_nadd; auto|]. rewrite H2, H4. reflexivity.
  Qed.

  Lemma pairs_lower : forall xs ys, each P xs -> each P ys ->
    V (cnf_prod (map f xs) (map f ys)) ≤ nmulOrd (VE xs) (VE ys).
  Proof.
    assert (Hdl := nmulOrd_distrib_lower_Q Qn Qn_eq Qn_dec Qn_zero).
    assert (Hrow : forall x ys, P x -> each P ys ->
              V (map (fun b => f x ⊕ b) (map f ys)) ≤ nmulOrd (En x) (VE ys)).
    { intros x ys Hx. induction ys as [|y ys IH]; simpl; intro Hys.
      - apply zero_least.
      - destruct Hys as [Hy Hys].
        destruct (VE_props ys Hys) as [H1 _].
        destruct (En_props x Hx) as [H2 _]. destruct (En_props y Hy) as [H3 _].
        rewrite <- Hdl; auto.
        apply naddOrd_monotone; [apply exp_lower_n; auto | apply IH; auto]. }
    induction xs as [|x xs IH]; intros ys Hxs Hys.
    - apply zero_least.
    - destruct Hxs as [Hx Hxs]. simpl map. rewrite V_cnf_cons_l.
      destruct (VE_props ys Hys) as [H1 _]. destruct (VE_props xs Hxs) as [H2 _].
      destruct (En_props x Hx) as [H3 _].
      simpl VE. rewrite !(nmulOrd_comm _ (VE ys)).
      rewrite <- Hdl; auto.
      rewrite !(nmulOrd_comm (VE ys)).
      apply naddOrd_monotone; [apply Hrow | apply IH]; auto.
  Qed.

  (** The algorithm's value is a lower bound for the semantic product. *)
  Theorem cantor_nmul_lower x y : P x -> P y ->
    f (cantor_nmul A f P X x y) ≤ nmulOrd (f x) (f y).
  Proof.
    intros Hx Hy.
    destruct (cantor_decompose_correct X x Hx) as [Hx1 _].
    destruct (cantor_decompose_correct X y Hy) as [Hy1 _].
    rewrite (proj2 (cantor_nmul_correct A f P X x y Hx Hy)).
    rewrite pairs_lower; auto.
    rewrite (proj2 (VE_props _ Hx1)), (proj2 (VE_props _ Hy1)).
    rewrite <- (dec_value A f P X x Hx), <- (dec_value A f P X y Hy). reflexivity.
  Qed.

  (** ** The upper half

    Subdistributivity over a Cantor normal form [ω^e + c] uses the split
    of the chain that sends [v < ω^e] to the left and [ω^e + p] to the
    right; reading [p] off the normal form of [v] is where the notation
    system is needed.  The exponent law's upper bound then follows by
    subadditivity and closure, by induction. *)

  Lemma ordered_tail l x : cantor_ordered f (x::l) -> cantor_ordered f l.
  Proof. destruct l; simpl; intuition. Qed.

  Lemma denote_V l : each P l -> cantor_ordered f l -> cantor_denote f l ≈ V (map f l).
  Proof.
    intros H1 H2. rewrite (cantor_denote_nadd_eq X); auto.
    rewrite cantor_denote_nadd_map. reflexivity.
  Qed.

  Lemma rec_value l : each P l -> cantor_ordered f l ->
    P (cantor_recompose X l) /\ f (cantor_recompose X l) ≈ cantor_denote f l.
  Proof.
    intros H1 H2. destruct (cantor_recompose_correct X l H1 H2). split; auto. symmetry; auto.
  Qed.

  (** Subtracting a leading power from a notation. *)
  Lemma head_sub e rest w :
    P e -> each P rest -> cantor_ordered f (e::rest) -> P w ->
    expOrd ω (f e) ≤ f w -> f w < expOrd ω (f e) + cantor_denote f rest ->
    exists p, Qn p /\ f w ≈ expOrd ω (f e) + p /\ p < cantor_denote f rest.
  Proof.
    intros He Hrest Hord Hw Hle Hlt.
    destruct (cantor_decompose_correct X w Hw) as [Hw1 [Hw2 Hw3]].
    destruct (cantor_decompose X w) as [|d ds] eqn:Hdw.
    { elim (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [apply expOrd_nonzero|].
      rewrite Hle, Hw3. reflexivity. }
    destruct Hw1 as [Hd Hds].
    generalize (cantor_decomp_compare_correct X d e Hd He).
    destruct (cantor_decomp_compare X d e); simpl; intro Hc.
    - elim (ord_lt_irreflexive (f w)). eapply ord_lt_le_trans; [|exact Hle].
      rewrite Hw3, denote_V; simpl; auto.
      apply (V_below_power A f (d::ds) (f d)); auto with ord.
      + apply (ordered_head_le A f); auto.
      + apply (cantor_decomp_complete X).
    - exists (cantor_denote f ds). split; [|split].
      + destruct (rec_value ds Hds (ordered_tail ds d Hw2)) as [H1 H2].
        exists (cantor_recompose X ds). split; auto. symmetry; auto.
      + rewrite Hw3. simpl. rewrite Hc. reflexivity.
      + apply addOrd_cancel_lt with (expOrd ω (f e)).
        eapply ord_le_lt_trans; [|exact Hlt].
        rewrite Hw3. simpl. rewrite Hc. reflexivity.
    - elim (ord_lt_irreflexive (f w)). eapply ord_lt_le_trans; [exact Hlt|].
      apply ord_lt_le. apply ord_lt_le_trans with (expOrd ω (f d)).
      + change (cantor_denote f (e::rest) < expOrd ω (f d)).
        rewrite denote_V; [|simpl; auto | auto].
        apply (V_below_power A f (e::rest) (f e)); auto.
        { apply (ordered_head_le A f); auto. }
        { apply (cantor_decomp_complete X). }
      + rewrite Hw3, denote_V; simpl; auto. apply naddOrd_le1.
  Qed.

  Lemma head_split_upper a e rest : QHn a -> P e -> each P rest -> cantor_ordered f (e::rest) ->
    nmulOrd a (Tn (f (cantor_recompose X (e::rest)))) ≤
    nmulOrd a (En e) ⊕ nmulOrd a (Tn (f (cantor_recompose X rest))).
  Proof.
    intros Ha He Hrest Hord.
    assert (Hel : each P (e::rest)) by (simpl; auto).
    destruct (rec_value _ Hel Hord) as [HPl Hl].
    destruct (rec_value _ Hrest (ordered_tail rest e Hord)) as [HPr Hr].
    destruct (En_props e He) as [HEe HEe'].
    set (E := expOrd ω (f e)) in *.
    set (c := cantor_denote f rest) in *.
    set (T0 := Tn (f (cantor_recompose X (e::rest)))).
    assert (HT0 : T0 ≈ E + c) by (unfold T0; rewrite Tn_eq, Hl; auto; reflexivity).
    assert (HTr : Tn (f (cantor_recompose X rest)) ≈ c) by (rewrite Tn_eq; auto).
    assert (HQE : Qn E).
    { destruct (cantor_recompose_correct X [e]) as [H1 H2]; simpl; auto.
      exists (cantor_recompose X [e]). split; auto. rewrite <- H2. simpl.
      rewrite addOrd_zero_r. reflexivity. }
    set (Sp := fun v (s:bool) p => if s then v < E /\ p ≈ v else E ≤ v /\ v ≈ E + p).
    rewrite (nmul_rk a T0), (nmul_rk a (En e)), (nmul_rk a (Tn _)).
    apply (covers_rk_Q Qn Qn_eq Qn_dec T0 Sp).
    - intros v HQv HvT.
      destruct (Qn_dec v E HQv HQE) as [H|H].
      + exists true, v. simpl. split; auto. reflexivity.
      + destruct HQv as [w [Hw Hvw]].
        destruct (head_sub e rest w He Hrest Hord Hw) as [p [_ [Hp1 Hp2]]].
        * rewrite <- Hvw. auto.
        * rewrite <- Hvw. eapply ord_lt_le_trans; [exact HvT|]. rewrite HT0. reflexivity.
        * exists false, p. simpl. split; auto. rewrite Hvw. auto.
    - intros v w [|] p q _ _; simpl; intros [H1 H2] [H3 H4] Hvw.
      + rewrite H2, H4. auto.
      + apply addOrd_cancel_lt with E. rewrite <- H2, <- H4. auto.
    - intros r [Hr0|[]]; subst r; simpl. split; auto.
      unfold T0. apply Tn_QH; auto.
    - intros u v [r [[Hr0|[]] [Hu Hv]]] _. subst r. simpl in Hu, Hv.
      split; auto.
      intros [|] p; simpl; intros [H1 H2].
      + exists (a, En e). simpl. split; auto. split; auto.
        rewrite H2, HEe'. auto.
      + exists (a, Tn (f (cantor_recompose X rest))). simpl. split; auto. split; auto.
        rewrite HTr. apply addOrd_cancel_lt with E. rewrite <- H2, <- HT0. auto.
  Qed.

  Fixpoint VS (a:Ord) (l:list A) : Ord :=
    match l with [] => 0 | t::l' => nmulOrd a (En t) ⊕ VS a l' end.

  Lemma list_split_upper a : forall l, QHn a -> each P l -> cantor_ordered f l ->
    nmulOrd a (Tn (f (cantor_recompose X l))) ≤ VS a l.
  Proof.
    induction l as [|t l IH]; intros Ha Hl Hord.
    - simpl. destruct (rec_value [] I I) as [H1 H2].
      rewrite (Tn_eq _ H1), H2. simpl. rewrite nmulOrd_zero. reflexivity.
    - destruct Hl as [Ht Hl]. simpl VS.
      rewrite head_split_upper; auto.
      apply naddOrd_monotone; [reflexivity|]. apply IH; auto.
      apply ordered_tail with t; auto.
  Qed.

  Lemma below_power_dec a1 a : P a1 -> P a -> f a1 < expOrd ω (f a) ->
    forall t, In t (cantor_decompose X a1) -> f t < f a.
  Proof.
    intros Ha1 Ha H.
    destruct (cantor_decompose_correct X a1 Ha1) as [H1 [H2 H3]].
    destruct (cantor_decompose X a1) as [|d ds] eqn:Hd; [intros _ []|].
    intros t Ht. destruct H1 as [Hd1 Hds].
    apply ord_le_lt_trans with (f d); [exact (ordered_head_le A f ds d H2 t Ht)|].
    generalize (cantor_decomp_compare_correct X d a Hd1 Ha).
    destruct (cantor_decomp_compare X d a); simpl; intro Hc; auto;
      elim (ord_lt_irreflexive (f a1)); eapply ord_lt_le_trans; try exact H;
      rewrite H3, denote_V; simpl; auto;
      rewrite <- naddOrd_le1; apply expOrd_monotone; auto; [apply Hc | apply ord_lt_le; auto].
  Qed.

  Lemma sum_below_power a b l :
    P a -> P b -> each P l -> (forall t, In t l -> f t < f a) ->
    V (map (fun s => f b ⊕ s) (map f l)) < expOrd ω (f a ⊕ f b).
  Proof.
    intros Ha Hb Hl Hlt.
    destruct (cantor_nadd_correct X a b Ha Hb) as [Hab Hab'].
    rewrite <- Hab'.
    induction l as [|t l IH]; simpl in *.
    - apply expOrd_nonzero.
    - destruct Hl as [Ht Hl].
      apply nadd_closed_con; [apply (cantor_decomp_complete X)| |apply IH; auto].
      apply expOrd_increasing; auto with ord. rewrite Hab'.
      rewrite naddOrd_comm. apply naddOrd_increasing1. apply Hlt; auto.
  Qed.

  Lemma each_in l t : each P l -> In t l -> P t.
  Proof. induction l; simpl; intuition; subst; auto. Qed.

  Lemma VS_upper b l : P b -> each P l ->
    (forall t, In t l -> nmulOrd (En b) (En t) ≤ expOrd ω (f b ⊕ f t)) ->
    VS (En b) l ≤ V (map (fun s => f b ⊕ s) (map f l)).
  Proof.
    intros Hb. induction l as [|t l IH]; simpl; intros Hl H; [reflexivity|].
    destruct Hl. apply naddOrd_monotone; auto.
  Qed.

  Theorem exp_upper_n : forall a b, P a -> P b ->
    nmulOrd (En a) (En b) ≤ expOrd ω (f a ⊕ f b).
  Proof.
    intros a0 b0 Ha0 Hb0.
    generalize (ord_le_refl (f a0 ⊕ f b0)). generalize (f a0 ⊕ f b0) at 2 as o.
    intro o. revert a0 b0 Ha0 Hb0.
    induction o as [o IH] using ordinal_induction.
    intros a b Ha Hb Ho.
    destruct (En_props a Ha) as [HEa HEa'].
    destruct (En_props b Hb) as [HEb HEb'].
    (* bounds for one side, by the induction hypothesis *)
    assert (Hside : forall a b u, P a -> P b -> f a ⊕ f b ≤ o -> QHn u -> u < En a ->
              nmulOrd (En b) u < expOrd ω (f a ⊕ f b)).
    { intros a' b' u Ha' Hb' Ho' Hu Hlt.
      destruct (proj1 Hu) as [a1 [Ha1 Hua1]].
      destruct (En_props a' Ha') as [_ HEa''].
      assert (Hlt1 : f a1 < expOrd ω (f a')) by (rewrite <- Hua1, <- HEa''; auto).
      destruct (cantor_decompose_correct X a1 Ha1) as [Hd1 [Hd2 Hd3]].
      destruct (rec_value _ Hd1 Hd2) as [HPr Hr].
      assert (Hu' : u ≈ Tn (f (cantor_recompose X (cantor_decompose X a1)))).
      { rewrite Tn_eq, Hr, <- Hd3; auto. }
      rewrite Hu'. rewrite list_split_upper; auto; [|apply (proj1 (En_props b' Hb'))].
      apply ord_le_lt_trans with (V (map (fun s => f b' ⊕ s) (map f (cantor_decompose X a1)))).
      - apply VS_upper; auto. intros t Ht.
        assert (HPt := each_in _ _ Hd1 Ht).
        apply (IH (f b' ⊕ f t)); auto with ord.
        eapply ord_lt_le_trans; [|exact Ho'].
        rewrite (naddOrd_comm (f a')). apply naddOrd_increasing2.
        apply (below_power_dec a1 a' Ha1 Ha' Hlt1); auto.
      - apply sum_below_power; auto. apply below_power_dec; auto. }
    rewrite nmul_rk. apply ord_le_intro. intros i Hi.
    destruct (rk_lt_elim _ i Hi) as [m Hm].
    destruct (mv_elim _ m) as [r [[Hr|[]] [c [d Hp]]]]. subst r.
    set (p := mvpt [(En a, En b)] m) in *.
    simpl in Hp.
    assert (Hpx : QHn (fst p) /\ fst p < En a).
    { rewrite Hp. simpl. split; [apply QH_child; auto | apply index_lt]. }
    assert (Hpy : QHn (snd p) /\ snd p < En b).
    { rewrite Hp. simpl. split; [apply QH_child; auto | apply index_lt]. }
    apply ord_le_lt_trans with (rk (cut p [(En a, En b)])); auto.
    apply ord_le_lt_trans with (rk ([(fst p, En b)] ++ [(En a, snd p)])).
    { apply rk_mono. intros r Hr. right. simpl in Hr.
      destruct Hr as [Hr|[Hr|[]]]; subst r; simpl.
      - exists (fst p, En b). simpl; split; auto. split; [apply glb_le2 | reflexivity].
      - exists (En a, snd p). simpl; split; auto. split; [reflexivity | apply glb_le2]. }
    rewrite rk_app_le. rewrite <- !nmul_rk.
    destruct (cantor_nadd_correct X a b Ha Hb) as [Hab Hab'].
    rewrite <- Hab'. apply nadd_closed_con; [apply (cantor_decomp_complete X)| |]; rewrite Hab'.
    - rewrite nmulOrd_comm. exact (Hside a b (fst p) Ha Hb Ho (proj1 Hpx) (proj2 Hpx)).
    - rewrite (naddOrd_comm (f a) (f b)).
      apply (Hside b a (snd p) Hb Ha); [rewrite naddOrd_comm; exact Ho | apply Hpy | apply Hpy].
  Qed.

  (** The semantic product is at most the algorithm's value. *)
  Theorem cantor_nmul_upper x y : P x -> P y ->
    nmulOrd (f x) (f y) ≤ f (cantor_nmul A f P X x y).
  Proof.
    intros Hx Hy.
    destruct (cantor_decompose_correct X x Hx) as [Hx1 [Hx2 Hx3]].
    destruct (cantor_decompose_correct X y Hy) as [Hy1 [Hy2 Hy3]].
    destruct (rec_value _ Hx1 Hx2) as [HPx Hrx].
    destruct (rec_value _ Hy1 Hy2) as [HPy Hry].
    rewrite (proj2 (cantor_nmul_correct A f P X x y Hx Hy)).
    rewrite V_cnf_comm.
    rewrite <- (Tn_eq x Hx) at 1.
    assert (Hy' : f y ≈ Tn (f (cantor_recompose X (cantor_decompose X y)))).
    { rewrite Tn_eq, Hry; auto. }
    rewrite Hy'. rewrite list_split_upper; auto; [|apply Tn_QH; auto].
    assert (Hx' : Tn (f x) ≈ Tn (f (cantor_recompose X (cantor_decompose X x)))).
    { rewrite !Tn_eq, Hrx; auto. }
    clear Hy' Hy3 HPy Hry. revert Hy1 Hy2.
    induction (cantor_decompose X y) as [|t l IHl]; intros Hy1 Hy2.
    - simpl. reflexivity.
    - destruct Hy1 as [Ht Hl].
      change (VS (Tn (f x)) (t::l)) with (nmulOrd (Tn (f x)) (En t) ⊕ VS (Tn (f x)) l).
      change (map f (t::l)) with (f t :: map f l).
      rewrite V_cnf_cons_l.
      apply naddOrd_monotone; [|apply IHl; auto; apply ordered_tail with t; auto].
      rewrite nmulOrd_comm, Hx'. rewrite list_split_upper; auto;
        [|apply (proj1 (En_props t Ht))].
      apply VS_upper; auto. intros s0 Hs0. apply exp_upper_n; auto.
      apply each_in with (cantor_decompose X x); auto.
  Qed.

  (** Together: the algorithm reflects the semantic natural product. *)
  Theorem cantor_nmul_reflects :
    reflects A f P (ORD ==> ORD ==> ORD) nmulOrd (cantor_nmul A f P X).
  Proof.
    simpl. intros u x [Hu Hx] v y [Hv Hy].
    destruct (cantor_nmul_correct A f P X x y Hx Hy) as [H1 _].
    split; auto. rewrite Hu, Hv. split.
    - apply cantor_nmul_upper; auto.
    - apply cantor_nmul_lower; auto.
  Qed.

End cantor_product_lower.

(** ** Interpolants are needed only at epsilon numbers

  A notation that is not an epsilon number ([f x ≈ ω^(f x)]) has a
  normal form whose exponents all denote strictly smaller ordinals, and
  interpolants are preserved by [ω^-] and [+].  So interpolants at the
  epsilon notations give interpolants everywhere, and the reflection of
  the natural product needs nothing more. *)

Lemma le_expOmega : forall x, x ≤ expOrd ω x.
Proof.
  induction x as [B g IH]. rewrite ord_le_unfold. intro b.
  apply ord_le_lt_trans with (expOrd ω (g b)); auto.
  apply expOrd_increasing; auto with ord.
Qed.

Section epsilon_interpolants.
  Variable A : Type.
  Variable f : A -> Ord.
  Variable P : A -> Prop.
  Variable X : has_cantor_decomposition f P.

  Lemma repeat_props e n : P e ->
    each P (repeat e n) /\ cantor_ordered f (repeat e n).
  Proof.
    intro He. induction n as [|n IH]; simpl; [split; auto|].
    destruct IH as [H1 H2]. split; [split; auto|].
    split; auto. destruct n; simpl; auto. reflexivity.
  Qed.

  Lemma denote_repeat e n :
    cantor_denote f (repeat e (S n)) ≈ expOrd ω (f e) * natOrdSize (S n).
  Proof.
    induction n as [|n IH].
    - simpl. rewrite addOrd_zero_r, mulOrd_one_r. reflexivity.
    - change (cantor_denote f (repeat e (S (S n))))
        with (expOrd ω (f e) + cantor_denote f (repeat e (S n))).
      rewrite IH.
      replace (S (S n)) with (S n + 1)%nat by lia.
      rewrite natOrdSize_add, ordDistrib_left, mulOrd_one_r. reflexivity.
  Qed.

  Lemma interp_zero : has_interpolants f P 0.
  Proof.
    rewrite has_interpolants_unfold. intros i Hi. elim (zero_lt i Hi).
  Qed.

  Lemma interp_power e : P e ->
    (forall y, P y -> f y < expOrd ω (f e) -> has_interpolants f P (f y)) ->
    has_interpolants f P (f e) ->
    has_interpolants f P (expOrd ω (f e)).
  Proof.
    intros He IH Hie.
    rewrite has_interpolants_unfold. intros i Hi.
    rewrite expOrd_unfold in Hi. apply lub_lt in Hi. destruct Hi as [Hi|Hi].
    - destruct (cantor_zero_reflects X) as [Hz1 Hz2].
      exists (cantor_zero X). split; auto.
      assert (Hfz : f (cantor_zero X) < expOrd ω (f e)) by (rewrite <- Hz1; apply expOrd_nonzero).
      split; [|split; auto].
      rewrite <- Hz1. rewrite ord_lt_unfold in Hi. destruct Hi as [[] Hi]. exact Hi.
    - apply sup_lt in Hi. destruct Hi as [j Hi].
      rewrite mulOrd_unfold in Hi. apply sup_lt in Hi. destruct Hi as [n Hi].
      rewrite <- mulOrd_succ in Hi.
      rewrite has_interpolants_unfold in Hie.
      destruct (Hie (ordSize (f e) j)) as [e' [He' [He'1 [He'2 _]]]]; [apply index_lt|].
      destruct (repeat_props e' (S n) He') as [Hr1 Hr2].
      destruct (cantor_recompose_correct X _ Hr1 Hr2) as [Hy Hfy].
      set (y := cantor_recompose X (repeat e' (S n))) in *.
      assert (Hfy' : f y ≈ expOrd ω (f e') * natOrdSize (S n)).
      { rewrite <- Hfy. apply denote_repeat. }
      assert (Hylt : f y < expOrd ω (f e)).
      { rewrite Hfy'. apply mul_nat_below_power; auto. apply (cantor_decomp_complete X). }
      exists y. split; auto. split; [|split; auto].
      rewrite Hfy'. apply ord_lt_le. eapply ord_lt_le_trans; [exact Hi|].
      apply mulOrd_monotone1. apply expOrd_monotone. auto.
  Qed.

  Lemma interp_denote : forall l, each P l ->
    (forall t, In t l -> has_interpolants f P (expOrd ω (f t))) ->
    has_interpolants f P (cantor_denote f l).
  Proof.
    induction l as [|t l IH]; intros Hl Ht; simpl.
    - apply interp_zero.
    - destruct Hl as [Htp Hl].
      destruct (cantor_recompose_correct X [t]) as [Hp1 Hp2]; simpl; auto.
      assert (Hp : f (cantor_recompose X [t]) ≈ expOrd ω (f t)).
      { rewrite <- Hp2. simpl. apply addOrd_zero_r. }
      rewrite <- Hp.
      apply (has_interpolants_add (cantor_add_reflects X)); auto.
      + rewrite Hp. apply Ht. simpl; auto.
      + apply IH; auto. intros; apply Ht; simpl; auto.
  Qed.

  Theorem interpolants_from_epsilons :
    (forall x, P x -> f x ≈ expOrd ω (f x) -> has_interpolants f P (f x)) ->
    has_all_interpolants f P.
  Proof.
    intros Heps x0 Hx0.
    generalize (ord_le_refl (f x0)). generalize (f x0) at 2 as o.
    intro o. revert x0 Hx0.
    induction o as [o IH] using ordinal_induction.
    intros x Hx Ho.
    destruct (cantor_decompose_correct X x Hx) as [Hd1 [Hd2 Hd3]].
    destruct (cantor_decompose X x) as [|d ds] eqn:Hdx.
    { rewrite Hd3. apply interp_zero. }
    destruct Hd1 as [Hd Hds].
    assert (Hdx' : expOrd ω (f d) ≤ f x) by (rewrite Hd3; simpl; apply addOrd_le1).
    generalize (cantor_decomp_compare_correct X d x Hd Hx).
    destruct (cantor_decomp_compare X d x); simpl; intro Hc.
    - (* not an epsilon number: every exponent is smaller *)
      assert (Hsmall : forall y, P y -> f y < f x -> has_interpolants f P (f y)).
      { intros y Hy Hlt. apply (IH (f y)); auto. eapply ord_lt_le_trans; [exact Hlt | exact Ho].
        reflexivity. }
      rewrite Hd3. apply interp_denote; [simpl; auto|].
      intros t Ht.
      assert (Htd : f t ≤ f d) by (apply (ordered_head_le A f ds d); auto).
      assert (HPt : P t).
      { destruct Ht as [Ht|Ht]; [subst; auto|].
        clear -Hds Ht. induction ds; simpl in *; intuition; subst; auto. }
      apply interp_power; auto.
      + intros y Hy Hlt. apply Hsmall; auto.
        eapply ord_lt_le_trans; [exact Hlt|]. rewrite <- Hdx'.
        apply expOrd_monotone; auto.
      + apply Hsmall; auto. apply ord_le_lt_trans with (f d); auto.
    - (* an epsilon number *)
      apply Heps; auto. split; [apply le_expOmega|].
      rewrite <- Hc at 1. auto.
    - elim (ord_lt_irreflexive (f x)).
      eapply ord_lt_le_trans; [exact Hc|].
      rewrite <- Hdx'. apply le_expOmega.
  Qed.

  (** Hence the natural product reflects as soon as the epsilon notations
      have interpolants; in particular, unconditionally for a system
      without epsilon notations. *)
  Corollary cantor_nmul_reflects_epsilons :
    (forall x, P x -> f x ≈ expOrd ω (f x) -> has_interpolants f P (f x)) ->
    reflects A f P (ORD ==> ORD ==> ORD) nmulOrd (cantor_nmul A f P X).
  Proof.
    intro H. apply cantor_nmul_reflects. apply interpolants_from_epsilons; auto.
  Qed.

  Corollary cantor_nmul_reflects_no_epsilons :
    (forall x, P x -> ~ f x ≈ expOrd ω (f x)) ->
    reflects A f P (ORD ==> ORD ==> ORD) nmulOrd (cantor_nmul A f P X).
  Proof.
    intro H. apply cantor_nmul_reflects_epsilons.
    intros x Hx Heq. elim (H x Hx Heq).
  Qed.

End epsilon_interpolants.

(** ** Remarks

  Every notation system of this development has interpolants, so its
  natural product reflects [nmulOrd] constructively (see [VF_reflects_nmul]
  in each notation file).

  Interpolants matter only at epsilon notations
  ([interpolants_from_epsilons]); a system without them needs no
  hypothesis at all ([cantor_nmul_reflects_no_epsilons]).  Whether they
  can be dropped at epsilon notations is open:

  - An epsilon notation is where a system can depend on an undecided
    proposition.  For instance, a system with one free atom [ε], denoting
    [e = sup_n ω^ω^...^b] with [b] equal to [1], or [ε0 + 1] if [P], has
    decidable comparisons ([e] is [ε0], or [ε1] if [P]) but no
    interpolants at [ε].
  - At such an [e], the classical strategy for superdistributivity must
    compare a child of [e] (whose value depends on [P]) with a deeper
    descendant (whose value does not): choosing the tallest rectangle
    covering a column.  This is the kind of choice that yields the
    reverse results elsewhere, so a counterexample to reflection, if
    there is one, would be a game of transfinite height played at such
    an atom.  The Kripke instances checked so far
    (tools/kripke/pdep_widths.py) have finite heights and are all forced. *)
