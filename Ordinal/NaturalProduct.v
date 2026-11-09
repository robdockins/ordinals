From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import List.
Import ListNotations.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import NaturalArith.

From Stdlib Require Import ClassicalFacts.
From Ordinal Require Import Classical.

Open Scope ord_scope.

(** * The natural (Hessenberg) product, constructively

  Classically, the natural product [a ⊗ b] is the maximal order type of
  the product partial order [a × b] (de Jongh and Parikh), which is also
  the rank of the tree of bad sequences in [a × b].  We define [nmulOrd]
  by playing that game directly: a position is a down-closed region of
  the plane, given as a finite union of rectangles; a move picks a point
  of the region and deletes the upward cone above it.

  The cone is removed from each rectangle using the (constructive)
  binary glb, so no decisions about whether the point lies inside a
  rectangle are needed:

      (x × y) \ ↑p  =  ((x ⊓ px) × y)  ∪  (x × (y ⊓ py)).

  Termination is by structural recursion on an explicit fuel ordinal;
  the fuel is bounded by the "one-sided" recursion [gbound] (the
  [incorrect_nmul] of NaturalArith.v), which makes it provably
  sufficient, and the result is independent of the fuel.

  ** Guide to the results

  Constructive (no axioms):
  - [nmulOrd_comm], [nmulOrd_monotone], [nmulOrd_increasing1],
    [nmulOrd_increasing2], [nmulOrd_zero], [nmulOrd_one];
  - [nmulOrd_succ_upper]: [a ⊗ (b+1) ≤ a ⊗ b ⊕ a];
  - [covers_rk]: the upper half of distributivity, given any split of
    [b ⊕ c] into two strictly increasing pieces;
  - the game machinery: fuel independence ([nmulOrd_fuel]), the
    fuel-free rank [rk], subadditivity ([rk_app_le]) and the chain
    lemma ([rk_chain]);
  - on a universe [Q] with a decidable order: superdistributivity
    ([nmulOrd_distrib_lower_Q]) and subdistributivity given a split at
    the points of [Q] ([covers_rk_Q]).

  Classical (excluded middle as an explicit hypothesis):
  - [nmulOrd_succ_classical]: [a ⊗ (b+1) ≈ a ⊗ b ⊕ a];
  - [nmulOrd_distrib]: [a ⊗ (b ⊕ c) ≈ a ⊗ b ⊕ a ⊗ c];
  - [nmulOrd_exp]: [ω^α ⊗ ω^β ≈ ω^(α ⊕ β)];
  - [nmulOrd_is_hessenberg]: on Cantor normal forms, [a ⊗ b] is the
    natural sum of [ω^(αi ⊕ βj)] over all pairs of terms, i.e.
    [nmulOrd] is Hessenberg's natural product.

  Reverse results:
  - [succ_lower_WEM]: the lower half of the successor law, for all
    ordinals, implies weak excluded middle; hence so does the lower half
    of distributivity ([distrib_lower_WEM]).  The witness is an ordinal
    with two children whose order depends on [P]; it was found by a
    search in a two-world Kripke model (tools/kripke);
  - [succ_lower_complete_WEM], [distrib_lower_complete_WEM]: the same,
    even restricted to complete ordinals.  The witness is a limit of
    an increasing sequence of directed ordinals;
  - [split_WEM]: a total split of [b ⊕ c], as used by [covers_rk],
    implies weak excluded middle;
  - [row_lower_EM]: the lower half of the row lemma over an arbitrary
    region implies excluded middle.

  ** Remarks

  So the natural product has no constructive successor law, even for
  complete ordinals; it holds only classically.  The obstruction is
  in the game: matching [a ⊗ b ⊕ a] inside [a ⊗ (b+1)] requires choosing
  a column of the top row before seeing the opponent's next move, and
  over a limit no single column is safe.  The upper halves remain
  constructive.

  On ordinals built from a universe with a decidable order the classical
  proofs go through: superdistributivity and the restricted
  subdistributivity of section [decidable_universe] are constructive.
  For notation systems with interpolants, Notation/CantorProduct.v uses
  them to show constructively that the term-by-term product of Cantor
  normal forms reflects [nmulOrd]; so on notations [nmulOrd] satisfies
  all the usual laws.
 *)

Definition region := list (Ord * Ord).

(** Moves: choose a rectangle and a child in each coordinate. *)
Fixpoint mv (D:region) : Type :=
  match D with
  | [] => False
  | r :: D' => (ordCarrier (fst r) * ordCarrier (snd r)) + mv D'
  end.

Fixpoint mvpt (D:region) : mv D -> Ord * Ord :=
  match D as D return mv D -> Ord * Ord with
  | [] => fun m => False_rect _ m
  | r :: D' => fun m =>
      match m with
      | inl cd => (ordSize (fst r) (fst cd), ordSize (snd r) (snd cd))
      | inr m' => mvpt D' m'
      end
  end.

Definition cut (p:Ord*Ord) (D:region) : region :=
  flat_map (fun r => [ (fst r ⊓ fst p, snd r) ; (fst r, snd r ⊓ snd p) ]) D.

Fixpoint grank (fuel:Ord) (D:region) : Ord :=
  match fuel with
  | ord F h => ord (F * mv D) (fun km => grank (h (fst km)) (cut (mvpt D (snd km)) D))
  end.

(** The fuel bound: the "one-sided" recursion (essentially
    [incorrect_nmul]).  It overestimates the natural product, which is
    exactly what fuel needs; see [grank_le_measure]. *)
Fixpoint gbound (x:Ord) : Ord -> Ord :=
  fix inner (y:Ord) : Ord :=
    match x, y with
    | ord A f, ord B g =>
        ord (A*B) (fun ab => gbound (f (fst ab)) y ⊕ inner (g (snd ab)))
    end.

Definition nmulOrd (a b:Ord) : Ord := grank (succOrd (gbound a b)) [(a,b)].


(** ** Moves and points *)

Lemma mv_intro : forall D r, In r D ->
  forall (c:ordCarrier (fst r)) (d:ordCarrier (snd r)),
    exists m:mv D, mvpt D m = (ordSize (fst r) c, ordSize (snd r) d).
Proof.
  induction D as [|r0 D IH]; simpl; intros r Hr c d.
  - elim Hr.
  - destruct Hr as [Hr|Hr].
    + subst r0. exists (inl (c,d)). reflexivity.
    + destruct (IH r Hr c d) as [m Hm].
      exists (inr m). exact Hm.
Qed.

Lemma mv_elim : forall D (m:mv D), exists r, In r D /\
  exists (c:ordCarrier (fst r)) (d:ordCarrier (snd r)),
    mvpt D m = (ordSize (fst r) c, ordSize (snd r) d).
Proof.
  induction D as [|r0 D IH]; simpl; intros m.
  - elim m.
  - destruct m as [[c d]|m].
    + exists r0. split; auto. exists c, d. reflexivity.
    + destruct (IH m) as [r [Hr Hcd]].
      exists r. split; auto.
Qed.


(** ** Region inclusion

  A rectangle of [D] is either empty (one side ≤ 0) or is dominated
  componentwise by some rectangle of [E].  *)

Definition rle (r s:Ord*Ord) := fst r ≤ fst s /\ snd r ≤ snd s.

Definition rsub (D E:region) :=
  forall r, In r D -> (fst r ≤ 0 \/ snd r ≤ 0) \/ exists s, In s E /\ rle r s.

Lemma rsub_refl D : rsub D D.
Proof.
  intros r Hr. right. exists r. split; auto. split; reflexivity.
Qed.

Lemma rsub_trans D E F : rsub D E -> rsub E F -> rsub D F.
Proof.
  intros HDE HEF r Hr.
  destruct (HDE r Hr) as [Hz|[s [Hs [H1 H2]]]]; auto.
  destruct (HEF s Hs) as [[Hz|Hz]|[t [Ht [H3 H4]]]].
  - left. left. rewrite H1. auto.
  - left. right. rewrite H2. auto.
  - right. exists t. split; auto. split; etransitivity; eauto.
Qed.

Lemma cut_mono p p' D E :
  rle p p' -> rsub D E -> rsub (cut p D) (cut p' E).
Proof.
  intros [Hp1 Hp2] HDE r Hr.
  unfold cut in Hr.
  apply in_flat_map in Hr.
  destruct Hr as [r0 [Hr0 Hr]].
  destruct (HDE r0 Hr0) as [[Hz|Hz]|[s [Hs [H1 H2]]]].
  - simpl in Hr. left.
    destruct Hr as [Hr|[Hr|[]]]; subst r; simpl.
    + left. rewrite glb_le1. auto.
    + left. auto.
  - simpl in Hr. left.
    destruct Hr as [Hr|[Hr|[]]]; subst r; simpl.
    + right. auto.
    + right. rewrite glb_le1. auto.
  - right. simpl in Hr.
    destruct Hr as [Hr|[Hr|[]]]; subst r.
    + exists (fst s ⊓ fst p', snd s). split.
      * unfold cut. apply in_flat_map. exists s. simpl; auto.
      * split; simpl; auto.
        rewrite H1. rewrite Hp1. reflexivity.
    + exists (fst s, snd s ⊓ snd p'). split.
      * unfold cut. apply in_flat_map. exists s. simpl; auto.
      * split; simpl; auto.
        rewrite H2. rewrite Hp2. reflexivity.
Qed.


(** ** Monotonicity in fuel and in the region (constructive) *)

Lemma grank_unfold_lt β D (k:ordCarrier β) (m:mv D) :
  grank (β k) (cut (mvpt D m) D) < grank β D.
Proof.
  destruct β as [F h]. simpl.
  rewrite ord_lt_unfold.
  exists (k,m). simpl. reflexivity.
Qed.

Lemma grank_mono : forall β β' D E,
  β ≤ β' -> rsub D E -> grank β D ≤ grank β' E.
Proof.
  induction β as [F h IH]; intros β' D E Hβ HDE.
  simpl. rewrite ord_le_unfold. simpl.
  intros [k m]. simpl.
  rewrite ord_le_unfold in Hβ. simpl in Hβ.
  generalize (Hβ k). rewrite ord_lt_unfold. intros [k' Hk'].
  destruct (mv_elim D m) as [r [Hr [c [d Hm]]]].
  destruct (HDE r Hr) as [[Hz|Hz]|[s [Hs [H1 H2]]]].
  - elim (zero_lt (ordSize (fst r) c)). rewrite <- Hz. apply index_lt.
  - elim (zero_lt (ordSize (snd r) d)). rewrite <- Hz. apply index_lt.
  - assert (Hc : ordSize (fst r) c < fst s).
    { rewrite <- H1. apply index_lt. }
    assert (Hd : ordSize (snd r) d < snd s).
    { rewrite <- H2. apply index_lt. }
    rewrite ord_lt_unfold in Hc. destruct Hc as [c' Hc].
    rewrite ord_lt_unfold in Hd. destruct Hd as [d' Hd].
    destruct (mv_intro E s Hs c' d') as [m' Hm'].
    apply ord_le_lt_trans with (grank (β' k') (cut (mvpt E m') E)).
    + apply IH; auto.
      apply cut_mono; auto.
      rewrite Hm, Hm'. split; simpl; auto.
    + apply grank_unfold_lt.
Qed.

Lemma grank_le_fuel : forall β D, grank β D ≤ β.
Proof.
  induction β as [F h IH]; intro D.
  simpl. rewrite ord_le_unfold. simpl. intros [k m]. simpl.
  rewrite ord_lt_unfold. simpl. exists k. apply IH.
Qed.

(** A region with no moves has rank zero. *)
Lemma grank_nomoves β D : (mv D -> False) -> grank β D ≈ 0.
Proof.
  intro H. split; [|apply zero_least].
  destruct β as [F h]. simpl. rewrite ord_le_unfold. simpl.
  intros [k m]. elim (H m).
Qed.

(** ** Fuel independence

  Once the fuel is sufficient ([grank β D < β]), adding more fuel changes
  nothing.  This is fully constructive.  *)
Lemma grank_stable : forall β' β D,
  grank β D < β -> grank β' D ≤ grank β D.
Proof.
  induction β' as [F' h' IH]; intros β D Hsuff.
  simpl. rewrite ord_le_unfold. simpl. intros [k' m]. simpl.
  destruct β as [F h].
  rewrite ord_lt_unfold in Hsuff. destruct Hsuff as [k Hk].
  apply ord_le_lt_trans with (grank (h k) (cut (mvpt D m) D)).
  - apply IH.
    apply ord_lt_le_trans with (grank (ord F h) D); auto.
    apply (grank_unfold_lt (ord F h) D k m).
  - apply (grank_unfold_lt (ord F h) D k m).
Qed.

Lemma grank_stable_eq β β' D :
  grank β D < β -> β ≤ β' -> grank β' D ≈ grank β D.
Proof.
  intros Hsuff Hle. split.
  - apply grank_stable; auto.
  - apply grank_mono; auto. apply rsub_refl.
Qed.



(** Any fuel at least as large as the value already computed is enough.
    Also constructive. *)
Lemma grank_value_fuel : forall γ β D,
  grank β D ≤ γ -> grank β D ≤ grank γ D.
Proof.
  induction γ as [G j IH]; intros β D H.
  destruct β as [F h].
  simpl. rewrite ord_le_unfold. simpl. intros [k m]. simpl.
  assert (Hv : grank (h k) (cut (mvpt D m) D) < ord G j).
  { apply ord_lt_le_trans with (grank (ord F h) D); auto.
    apply (grank_unfold_lt (ord F h) D k m). }
  rewrite ord_lt_unfold in Hv. destruct Hv as [jj Hjj]. simpl in Hjj.
  apply ord_le_lt_trans with (grank (j jj) (cut (mvpt D m) D)).
  - apply IH; auto.
  - apply (grank_unfold_lt (ord G j) D jj m).
Qed.


(** ** A constructive bound on the rank *)

Lemma gbound_unfold x y :
  gbound x y = ord (ordCarrier x * ordCarrier y)
                   (fun ab => gbound (x (fst ab)) y ⊕ gbound x (y (snd ab))).
Proof.
  destruct x; destruct y; reflexivity.
Qed.

Lemma gbound_monotone : forall x x' y y',
  x ≤ x' -> y ≤ y' -> gbound x y ≤ gbound x' y'.
Proof.
  induction x as [A f IHx]. intros x' y. revert x'.
  induction y as [B g IHy]. intros x' y' Hx Hy.
  rewrite gbound_unfold. rewrite ord_le_unfold. simpl. intros [a b]. simpl.
  rewrite ord_le_unfold in Hx. generalize (Hx a). rewrite ord_lt_unfold. intros [a' Ha'].
  rewrite ord_le_unfold in Hy. generalize (Hy b). rewrite ord_lt_unfold. intros [b' Hb'].
  simpl in Ha', Hb'.
  rewrite (gbound_unfold x' y'). rewrite ord_lt_unfold. exists (a',b'). simpl.
  apply naddOrd_monotone.
  - apply IHx; auto; rewrite ord_le_unfold; auto.
  - apply IHy; auto; rewrite ord_le_unfold; auto.
Qed.

Fixpoint gmeasure (D:region) : Ord :=
  match D with
  | [] => 0
  | r :: D' => gbound (fst r) (snd r) ⊕ gmeasure D'
  end.

Lemma gmeasure_app l1 l2 : gmeasure (l1 ++ l2) ≈ gmeasure l1 ⊕ gmeasure l2.
Proof.
  induction l1 as [|r l1 IH]; simpl.
  - symmetry. apply naddOrd_zero_l.
  - rewrite IH. apply naddOrd_assoc.
Qed.

Lemma cut_piece_le p r1 r0 :
  In r0 [ (fst r1 ⊓ fst p, snd r1) ; (fst r1, snd r1 ⊓ snd p) ] -> rle r0 r1.
Proof.
  intros [H|[H|[]]]; subst r0; split; simpl;
    first [ apply glb_le1 | reflexivity ].
Qed.

Lemma cut_split D (m:mv D) :
  exists D', rsub (cut (mvpt D m) D) D' /\ gmeasure D' < gmeasure D.
Proof.
  destruct (mv_elim D m) as [r [Hr [c [d Hm]]]]. rewrite Hm.
  destruct (in_split r D Hr) as [l1 [l2 HD]].
  set (p1 := (fst r ⊓ ordSize (fst r) c, snd r)).
  set (p2 := (fst r, snd r ⊓ ordSize (snd r) d)).
  exists (l1 ++ p1 :: p2 :: l2). split.
  { intros r0 Hr0. right.
    unfold cut in Hr0. apply in_flat_map in Hr0.
    destruct Hr0 as [r1 [Hr1 Hin]].
    rewrite HD in Hr1. apply in_app_or in Hr1.
    destruct Hr1 as [Hr1|[Hr1|Hr1]].
    - exists r1. split; [apply in_or_app; auto|].
      eapply cut_piece_le; eauto.
    - subst r1. exists r0. split; [|split; reflexivity].
      apply in_or_app. right.
      destruct Hin as [Hin|[Hin|[]]]; subst r0; simpl; auto.
    - exists r1. split; [apply in_or_app; simpl; auto|].
      eapply cut_piece_le; eauto. }
  rewrite HD. rewrite !gmeasure_app. simpl.
  apply naddOrd_increasing2.
  rewrite naddOrd_assoc. apply naddOrd_increasing1.
  rewrite (gbound_unfold (fst r) (snd r)). rewrite ord_lt_unfold. exists (c,d). simpl.
  apply naddOrd_monotone; apply gbound_monotone;
    first [ apply glb_le2 | reflexivity ].
Qed.

(** The key estimate: cutting at a point of rectangle [r] is dominated by
    splitting [r] alone into its two pieces, which strictly lowers the
    natural sum of [gbound]s over the rectangles. *)
Lemma grank_le_measure : forall β D, grank β D ≤ gmeasure D.
Proof.
  induction β as [F h IH]; intro D.
  simpl. rewrite ord_le_unfold. simpl. intros [k m]. simpl.
  destruct (cut_split D m) as [D' [HD' Hlt]].
  apply ord_le_lt_trans with (grank (h k) D').
  - apply grank_mono; auto. reflexivity.
  - apply ord_le_lt_trans with (gmeasure D'); auto.
Qed.

Lemma grank_cut_lt_measure β D (m:mv D) :
  grank β (cut (mvpt D m) D) < gmeasure D.
Proof.
  destruct (cut_split D m) as [D' [HD' Hlt]].
  apply ord_le_lt_trans with (grank β D').
  - apply grank_mono; auto. reflexivity.
  - apply ord_le_lt_trans with (gmeasure D'); auto.
    apply grank_le_measure.
Qed.

Lemma nmulOrd_sufficient a b :
  grank (succOrd (gbound a b)) [(a,b)] < succOrd (gbound a b).
Proof.
  apply succ_trans.
  rewrite grank_le_measure. simpl.
  apply naddOrd_zero_r.
Qed.

(** The definition does not depend on the choice of fuel,
    so long as it exceeds the bound. *)
Theorem nmulOrd_fuel a b β :
  gbound a b < β -> nmulOrd a b ≈ grank β [(a,b)].
Proof.
  intro Hβ. unfold nmulOrd. symmetry.
  apply grank_stable_eq.
  - apply nmulOrd_sufficient.
  - apply succ_least; auto.
Qed.

Lemma nmulOrd_le_gbound a b : nmulOrd a b ≤ gbound a b.
Proof.
  unfold nmulOrd. rewrite grank_le_measure. simpl. apply naddOrd_zero_r.
Qed.


(** ** Commutativity *)

Definition rswap (r:Ord*Ord) : Ord*Ord := (snd r, fst r).
Definition swapR (D:region) : region := map rswap D.

Lemma cut_swap p D : rsub (cut p (swapR D)) (swapR (cut (rswap p) D)).
Proof.
  intros r Hr. right.
  unfold cut, swapR in Hr. apply in_flat_map in Hr.
  destruct Hr as [r0 [Hr0 Hr]].
  apply in_map_iff in Hr0. destruct Hr0 as [r1 [Hr1 Hin]]. subst r0.
  exists r. split; [|split; reflexivity].
  unfold swapR, cut. apply in_map_iff.
  simpl in Hr. destruct Hr as [Hr|[Hr|[]]]; subst r.
  - exists (fst r1, snd r1 ⊓ fst p). split; [reflexivity|].
    apply in_flat_map. exists r1. simpl; auto.
  - exists (fst r1 ⊓ snd p, snd r1). split; [reflexivity|].
    apply in_flat_map. exists r1. simpl; auto.
Qed.

Lemma grank_swap_le : forall β D, grank β (swapR D) ≤ grank β D.
Proof.
  induction β as [F h IH]; intros D.
  simpl. rewrite ord_le_unfold. simpl. intros [k m]. simpl.
  destruct (mv_elim _ m) as [r [Hr [c [d Hm]]]].
  unfold swapR in Hr. apply in_map_iff in Hr.
  destruct Hr as [r0 [Hr0 Hin]]. subst r.
  destruct (mv_intro D r0 Hin d c) as [m' Hm'].
  apply ord_le_lt_trans with (grank (h k) (cut (mvpt D m') D)).
  - rewrite (grank_mono (h k) (h k) _ (swapR (cut (rswap (mvpt (swapR D) m)) D)));
      [| reflexivity | apply cut_swap ].
    rewrite IH.
    rewrite Hm, Hm'. reflexivity.
  - apply (grank_unfold_lt (ord F h) D k m').
Qed.

Lemma swapR_swapR D : swapR (swapR D) = D.
Proof.
  unfold swapR. rewrite map_map.
  rewrite <- (map_id D) at 2. apply map_ext. intros [x y]; reflexivity.
Qed.

Lemma grank_swap β D : grank β (swapR D) ≈ grank β D.
Proof.
  split.
  - apply grank_swap_le.
  - rewrite <- (swapR_swapR D) at 1. apply grank_swap_le.
Qed.

Theorem nmulOrd_comm a b : nmulOrd a b ≈ nmulOrd b a.
Proof.
  set (β := succOrd (gbound a b ⊔ gbound b a)).
  rewrite (nmulOrd_fuel a b β); [| apply succ_trans; apply lub_le1 ].
  rewrite (nmulOrd_fuel b a β); [| apply succ_trans; apply lub_le2 ].
  symmetry. apply (grank_swap β [(a,b)]).
Qed.


(** ** Monotonicity *)

Theorem nmulOrd_monotone a b a' b' :
  a ≤ a' -> b ≤ b' -> nmulOrd a b ≤ nmulOrd a' b'.
Proof.
  intros Ha Hb.
  rewrite (nmulOrd_fuel a b (succOrd (gbound a' b'))).
  - unfold nmulOrd. apply grank_mono; [reflexivity|].
    intros r [Hr|[]]; subst r. right.
    exists (a',b'). simpl; split; auto. split; auto.
  - apply succ_trans. apply gbound_monotone; auto.
Qed.

Theorem nmulOrd_increasing1 a a' b :
  a < a' -> 0 < b -> nmulOrd a b < nmulOrd a' b.
Proof.
  intros Ha Hb.
  generalize Ha. rewrite ord_lt_unfold. intros [c' Hc'].
  rewrite ord_lt_unfold in Hb. destruct Hb as [d _].
  unfold nmulOrd at 2.
  apply ord_le_lt_trans with
      (grank (gbound a' b) (cut (mvpt [(a',b)] (inl (c',d))) [(a',b)])).
  - apply ord_le_trans with (grank (gbound a' b) [(a,b)]).
    + apply grank_value_fuel.
      apply ord_le_trans with (gbound a b); [apply nmulOrd_le_gbound|].
      apply gbound_monotone; auto with ord.
    + apply grank_mono; [reflexivity|].
      intros r [Hr|[]]; subst r. right. simpl.
      exists (a' ⊓ ordSize a' c', b). split; auto.
      split; simpl; [|reflexivity].
      apply glb_greatest; auto with ord.
  - apply (grank_unfold_lt (succOrd (gbound a' b)) [(a',b)] tt (inl (c',d))).
Qed.

Theorem nmulOrd_increasing2 a b b' :
  b < b' -> 0 < a -> nmulOrd a b < nmulOrd a b'.
Proof.
  intros. rewrite (nmulOrd_comm a b), (nmulOrd_comm a b').
  apply nmulOrd_increasing1; auto.
Qed.


(** ** Zero and one *)

Theorem nmulOrd_zero a : nmulOrd a 0 ≈ 0.
Proof.
  apply grank_nomoves. simpl. intros [[_ []]|[]].
Qed.

(** One rectangle of height one behaves exactly like its width,
    as long as the fuel is large enough. *)
Lemma grank_one_upper : forall β x, grank β [(x,1)] ≤ x.
Proof.
  induction β as [F h IH]; intros x.
  simpl. rewrite ord_le_unfold. simpl.
  intros [k [[c []]|[]]]. simpl.
  apply ord_le_lt_trans with (grank (h k) [(ordSize x c, 1)]).
  - apply grank_mono; [reflexivity|].
    intros r Hr. simpl in Hr.
    destruct Hr as [Hr|[Hr|[]]]; subst r; simpl.
    + right. exists (ordSize x c, 1). simpl; split; auto.
      split; simpl; [apply glb_le2 | reflexivity].
    + left. right.
      rewrite glb_le2. rewrite ord_le_unfold. intros [].
  - apply ord_le_lt_trans with (ordSize x c); auto with ord.
Qed.

Lemma grank_one_lower : forall β x, x ≤ β -> x ≤ grank β [(x,1)].
Proof.
  induction β as [F h IH]; intros x Hx.
  rewrite ord_le_unfold. intro c.
  rewrite ord_le_unfold in Hx. generalize (Hx c).
  rewrite ord_lt_unfold. simpl. intros [k Hk].
  apply ord_le_lt_trans with (grank (h k) [(ordSize x c, 1)]).
  - apply IH; auto.
  - apply ord_le_lt_trans with (grank (h k) (cut (mvpt [(x,1)] (inl (c,tt))) [(x,1)])).
    + apply grank_mono; [reflexivity|].
      intros r [Hr|[]]; subst r. right.
      exists (x ⊓ ordSize x c, 1). simpl. split; auto.
      split; simpl; [|reflexivity].
      apply glb_greatest; auto with ord.
    + apply (grank_unfold_lt (ord F h) [(x,1)] k (inl (c,tt))).
Qed.

Lemma gbound_one : forall a, a ≤ gbound a 1.
Proof.
  induction a as [A f IH].
  rewrite ord_le_unfold. intro c.
  rewrite gbound_unfold. rewrite ord_lt_unfold. exists (c,tt). simpl.
  rewrite <- naddOrd_le1. apply IH.
Qed.

Theorem nmulOrd_one a : nmulOrd a 1 ≈ a.
Proof.
  unfold nmulOrd. split.
  - apply grank_one_upper.
  - apply grank_one_lower.
    apply ord_lt_le. apply succ_trans. apply gbound_one.
Qed.


(** ** The successor law, upper half

  Consider a rectangle [w × (b+1)] laid over a region [D] that covers
  [w × b] and has height at most [b].  Moves in the top row are moves in
  [w]; moves in [D] only shrink the top row.  Hence the rank is at most
  [rank D ⊕ w]. *)

Lemma rsub_nil E : rsub [] E.
Proof. intros r []. Qed.

Lemma rsub_cons r D E : rsub [r] E -> rsub D E -> rsub (r::D) E.
Proof.
  intros H1 H2 r0 [Hr0|Hr0].
  - subst r0. apply H1. simpl; auto.
  - apply H2; auto.
Qed.

Lemma rsub_in r s E : In s E -> rle r s -> rsub [r] E.
Proof.
  intros Hs Hrs r0 [Hr0|[]]. subst r0. right. eauto.
Qed.

Lemma rsub_cons_r s D E : rsub D E -> rsub D (s::E).
Proof.
  intros H r Hr. destruct (H r Hr) as [Hz|[s' [Hs' Hrs]]]; auto.
  right. exists s'. simpl; auto.
Qed.

Lemma rsub_single_trans r s E : rle r s -> rsub [s] E -> rsub [r] E.
Proof.
  intros [H1 H2] Hs. apply rsub_trans with [s]; auto.
  apply rsub_in with s; simpl; auto. split; auto.
Qed.

Lemma cut_sub p D : rsub (cut p D) D.
Proof.
  intros r Hr. right.
  unfold cut in Hr. apply in_flat_map in Hr.
  destruct Hr as [r1 [Hr1 Hin]].
  exists r1. split; auto. eapply cut_piece_le; eauto.
Qed.

Lemma grank_row_upper : forall β D w b,
  rsub [(w,b)] D ->
  (forall r, In r D -> snd r ≤ b) ->
  grank β ((w, succOrd b) :: D) ≤ grank β D ⊕ w.
Proof.
  induction β as [F h IH]; intros D w b Hw Hh.
  rewrite ord_le_unfold. simpl. intros [k [[c d]|m]]; simpl.
  - (* a move in the top row *)
    apply ord_le_lt_trans with (grank (h k) ((ordSize w c, succOrd b) :: D)).
    { apply grank_mono; [reflexivity|].
      apply rsub_cons.
      { apply rsub_in with (ordSize w c, succOrd b); simpl; auto.
        split; simpl; [apply glb_le2 | reflexivity]. }
      apply rsub_cons.
      { apply rsub_cons_r. apply rsub_single_trans with (w,b); auto.
        split; simpl; [reflexivity | apply glb_le2]. }
      apply rsub_cons_r. apply cut_sub. }
    apply ord_le_lt_trans with (grank (h k) D ⊕ ordSize w c).
    { apply IH; auto.
      apply rsub_single_trans with (w,b); auto.
      split; simpl; auto with ord. }
    apply ord_le_lt_trans with (grank (ord F h) D ⊕ ordSize w c).
    { apply naddOrd_monotone; [|reflexivity].
      apply grank_mono; [|apply rsub_refl].
      apply (index_le (ord F h) k). }
    apply naddOrd_increasing2. apply index_lt.
  - (* a move in D *)
    set (p := mvpt D m).
    assert (Hpy : snd p ≤ b).
    { destruct (mv_elim D m) as [r [Hr [c [d Hm]]]].
      unfold p. rewrite Hm. simpl.
      rewrite <- (Hh r Hr). auto with ord. }
    assert (Hcut : rsub (cut p [(w,b)]) (cut p D)).
    { apply cut_mono; auto. split; reflexivity. }
    apply ord_le_lt_trans with (grank (h k) ((w ⊓ fst p, succOrd b) :: cut p D)).
    { apply grank_mono; [reflexivity|].
      apply rsub_cons.
      { apply rsub_in with (w ⊓ fst p, succOrd b); simpl; auto.
        split; reflexivity. }
      apply rsub_cons; [|apply rsub_cons_r; apply rsub_refl].
      apply rsub_cons_r.
      apply rsub_single_trans with (w, b ⊓ snd p).
      { split; simpl; [reflexivity|].
        apply glb_greatest; [rewrite glb_le2; auto | apply glb_le2]. }
      apply rsub_trans with (cut p [(w,b)]); auto.
      apply rsub_in with (w, b ⊓ snd p); simpl; auto.
      split; reflexivity. }
    apply ord_le_lt_trans with (grank (h k) (cut p D) ⊕ (w ⊓ fst p)).
    { apply IH.
      - apply rsub_trans with (cut p [(w,b)]); auto.
        apply rsub_in with (w ⊓ fst p, b); simpl; auto.
        split; reflexivity.
      - intros r Hr. unfold cut in Hr. apply in_flat_map in Hr.
        destruct Hr as [r1 [Hr1 Hin]].
        destruct (cut_piece_le p r1 r Hin) as [_ H2].
        rewrite H2. auto. }
    apply ord_le_lt_trans with (grank (h k) (cut p D) ⊕ w).
    { apply naddOrd_monotone; [reflexivity | apply glb_le1]. }
    apply naddOrd_increasing1.
    apply (grank_unfold_lt (ord F h) D k m).
Qed.

Theorem nmulOrd_succ_upper a b : nmulOrd a (succOrd b) ≤ nmulOrd a b ⊕ a.
Proof.
  set (β := succOrd (gbound a (succOrd b) ⊔ gbound a b)).
  rewrite (nmulOrd_fuel a (succOrd b) β); [| apply succ_trans; apply lub_le1 ].
  rewrite (nmulOrd_fuel a b β); [| apply succ_trans; apply lub_le2 ].
  apply ord_le_trans with (grank β [(a, succOrd b); (a,b)]).
  - apply grank_mono; [reflexivity|].
    apply rsub_cons; [|apply rsub_nil].
    apply rsub_in with (a, succOrd b); simpl; auto. split; reflexivity.
  - apply grank_row_upper.
    + apply rsub_refl.
    + intros r [Hr|[]]; subst r. reflexivity.
Qed.


(** ** Fuel-free rank

  With the fuel fixed just above [gmeasure D], [grank] no longer
  depends on fuel, and behaves like the true rank of the game. *)

Definition rk (D:region) : Ord := grank (succOrd (gmeasure D)) D.

Lemma rk_sufficient D : rk D < succOrd (gmeasure D).
Proof. apply succ_trans. apply grank_le_measure. Qed.

Lemma grank_le_rk β D : grank β D ≤ rk D.
Proof. apply grank_stable. apply rk_sufficient. Qed.

Lemma rk_le_grank β D : rk D ≤ β -> rk D ≤ grank β D.
Proof. apply grank_value_fuel. Qed.

Lemma rk_mono D E : rsub D E -> rk D ≤ rk E.
Proof.
  intro H. apply ord_le_trans with (grank (succOrd (gmeasure D)) E).
  - apply grank_mono; auto. reflexivity.
  - apply grank_le_rk.
Qed.

Lemma rk_move_lt D (m:mv D) : rk (cut (mvpt D m) D) < rk D.
Proof.
  apply ord_le_lt_trans with (grank (gmeasure D) (cut (mvpt D m) D)).
  - apply rk_le_grank. apply ord_lt_le.
    apply ord_le_lt_trans with (grank (succOrd (gmeasure (cut (mvpt D m) D))) (cut (mvpt D m) D)).
    + reflexivity.
    + apply grank_cut_lt_measure.
  - unfold rk. apply (grank_unfold_lt (succOrd (gmeasure D)) D tt m).
Qed.

Lemma rk_lt_elim D i : i < rk D -> exists m:mv D, i ≤ rk (cut (mvpt D m) D).
Proof.
  unfold rk at 1, succOrd. rewrite ord_lt_unfold. simpl.
  intros [[[] m] H]. simpl in H.
  exists m. rewrite H. apply grank_le_rk.
Qed.

Lemma nmul_rk a b : nmulOrd a b ≈ rk [(a,b)].
Proof.
  unfold rk. apply nmulOrd_fuel. simpl.
  apply succ_trans. apply naddOrd_le1.
Qed.


(** ** More region lemmas *)

Lemma cut_cons p r D :
  cut p (r :: D) = (fst r ⊓ fst p, snd r) :: (fst r, snd r ⊓ snd p) :: cut p D.
Proof. reflexivity. Qed.

Lemma cut_cut_sub u v t q D :
  u ≤ t -> u ≤ fst q -> v ≤ snd q ->
  rsub (cut (u,v) D) (cut q (cut (t,v) D)).
Proof.
  intros Hut Huq Hvq r Hr. right.
  unfold cut in Hr. apply in_flat_map in Hr.
  destruct Hr as [r1 [Hr1 Hin]]. simpl in Hin.
  destruct Hin as [Hin|[Hin|[]]]; subst r.
  - exists ((fst r1 ⊓ t) ⊓ fst q, snd r1). split.
    + unfold cut. apply in_flat_map. exists (fst r1 ⊓ t, snd r1). split.
      * apply in_flat_map. exists r1. simpl; auto.
      * simpl; auto.
    + split; simpl; [|reflexivity].
      apply glb_greatest.
      * apply glb_greatest; [apply glb_le1 | rewrite glb_le2; auto].
      * rewrite glb_le2; auto.
  - exists (fst r1, (snd r1 ⊓ v) ⊓ snd q). split.
    + unfold cut. apply in_flat_map. exists (fst r1, snd r1 ⊓ v). split.
      * apply in_flat_map. exists r1. simpl; auto.
      * simpl; auto.
    + split; simpl; [reflexivity|].
      apply glb_greatest; [reflexivity | rewrite glb_le2; auto].
Qed.

Lemma rsub_row_cut w b q D :
  w ≤ fst q -> rsub [(w,b)] D -> rsub [(w,b)] (cut q D).
Proof.
  intros Hwq Hw.
  apply rsub_trans with (cut q [(w,b)]).
  - apply rsub_in with (w ⊓ fst q, b); simpl; auto.
    split; simpl; [apply glb_greatest; [reflexivity|auto] | reflexivity].
  - apply cut_mono; auto. split; reflexivity.
Qed.

Lemma cut_heights b q D :
  (forall r, In r D -> snd r ≤ b) -> forall r, In r (cut q D) -> snd r ≤ b.
Proof.
  intros Hh r Hr. unfold cut in Hr. apply in_flat_map in Hr.
  destruct Hr as [r1 [Hr1 Hin]].
  destruct (cut_piece_le q r1 r Hin) as [_ H2].
  rewrite H2. auto.
Qed.

Lemma cut_high q D :
  (forall r, In r D -> snd r ≤ snd q) -> rsub D (cut q D).
Proof.
  intros H r Hr. right. exists (fst r, snd r ⊓ snd q). split.
  - unfold cut. apply in_flat_map. exists r. simpl; auto.
  - split; simpl; [reflexivity | apply glb_greatest; [reflexivity | auto]].
Qed.

Lemma move_height D b (m:mv D) :
  (forall r, In r D -> snd r ≤ b) -> snd (mvpt D m) < b.
Proof.
  intros Hh. destruct (mv_elim D m) as [r [Hr [c [d Hm]]]].
  rewrite Hm. simpl.
  apply ord_lt_le_trans with (snd r); auto with ord.
Qed.

Lemma row_move_lower w b D (c:ordCarrier w) :
  (forall r, In r D -> snd r ≤ b) ->
  rk ((ordSize w c, succOrd b) :: D) < rk ((w, succOrd b) :: D).
Proof.
  intros Hh.
  apply ord_le_lt_trans with
      (rk (cut (mvpt ((w,succOrd b)::D) (inl (c,tt))) ((w,succOrd b)::D))).
  - apply rk_mono. rewrite cut_cons.
    apply rsub_cons.
    + apply rsub_in with (w ⊓ ordSize w c, succOrd b); simpl; auto.
      split; simpl; [apply glb_greatest; auto with ord | reflexivity].
    + apply rsub_cons_r. apply rsub_cons_r.
      apply cut_high. intros r Hr. simpl. auto.
  - apply rk_move_lt.
Qed.


(** ** The chain lemma

  Inside the cone above [(px,py)], play the points [(u,py)] for
  decreasing [u] first: this shows that removing that cone costs at
  least the (ordinal-sum) length of the chain from [px] to [w]. *)

Lemma rk_chain : forall w b D px py,
  rsub [(w,b)] D -> py < b ->
  forall e t, px + e ≤ t -> t ≤ w ->
    rk (cut (px,py) D) + e ≤ rk (cut (t,py) D).
Proof.
  intros w b D px py Hw Hpy.
  induction e as [E f IH]; intros t Ht Htw.
  rewrite addOrd_unfold. apply lub_least.
  - apply rk_mono. apply cut_mono; [|apply rsub_refl].
    split; simpl; [|reflexivity].
    rewrite <- Ht. apply addOrd_le1.
  - apply sup_least. intro i. apply succ_least.
    set (u := px + f i).
    assert (Hut : u < t).
    { apply ord_lt_le_trans with (px + ord E f); auto.
      apply addOrd_increasing. apply (index_lt (ord E f) i). }
    destruct (Hw (w,b) (or_introl eq_refl)) as [[Hz|Hz]|[s [Hs [Hs1 Hs2]]]].
    + simpl in Hz. elim (zero_lt u). rewrite <- Hz. rewrite <- Htw. auto.
    + simpl in Hz. elim (zero_lt py). rewrite <- Hz. auto.
    + simpl in Hs1, Hs2. assert (Hux : u < fst s ⊓ t).
      { apply ord_lt_le_trans with (succOrd u); [apply succ_lt|].
        apply glb_greatest; apply succ_least; auto.
        rewrite <- Hs1. rewrite <- Htw. auto. }
      rewrite ord_lt_unfold in Hux. destruct Hux as [c Hc].
      assert (Hpy' : py < snd s) by (rewrite <- Hs2; auto).
      rewrite ord_lt_unfold in Hpy'. destruct Hpy' as [d Hd].
      assert (Hin : In (fst s ⊓ t, snd s) (cut (t,py) D)).
      { unfold cut. apply in_flat_map. exists s. simpl; auto. }
      destruct (mv_intro _ _ Hin c d) as [m Hm].
      apply ord_le_lt_trans with (rk (cut (u,py) D)).
      * apply (IH i u); [reflexivity|].
        apply ord_lt_le. rewrite <- Htw. auto.
      * apply ord_le_lt_trans with (rk (cut (mvpt _ m) (cut (t,py) D))).
        { apply rk_mono. rewrite Hm.
          apply cut_cut_sub; simpl; auto with ord. }
        apply rk_move_lt.
Qed.


(** ** The successor law, lower half (classical)

  The one arithmetic fact needed is stated separately: if [x] exceeds
  [x''] by at least the chain [y ↦ w] (in the sense of ordinal sum),
  then [x'' ⊕ w] is already reached by [x ⊕ w'] for some [w' < w].
  For successor [w] this is trivial; for limit [w] it is an absorption
  property of Cantor normal forms. *)

Definition absorb_prop := forall w y x x'', y < w -> x'' < x ->
  (forall e, y + e ≤ w -> x'' + e ≤ x) ->
  exists w', w' < w /\ x'' ⊕ w ≤ x ⊕ w'.

Lemma rk_row_lower (EM:excluded_middle) (ABS:absorb_prop) :
  forall w D b, rsub [(w,b)] D -> (forall r, In r D -> snd r ≤ b) ->
  rk D ⊕ w ≤ rk ((w, succOrd b) :: D).
Proof.
  induction w as [w IHw] using (well_founded_ind ord_lt_wf).
  intros D b.
  generalize (ord_le_refl (rk D)). generalize (rk D) at 2 as o. intro o. revert D b.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros D b Ho Hw Hh.
  apply naddOrd_least3.
  - intros i Hi.
    destruct (rk_lt_elim D i Hi) as [m Hm].
    assert (Hcut : cut (mvpt D m) D = cut (fst (mvpt D m), snd (mvpt D m)) D).
    { destruct (mvpt D m); reflexivity. }
    set (q := mvpt D m) in *.
    assert (Hqy : snd q < b) by (apply move_height; auto).
    destruct (classical.order_total EM w (fst q)) as [Hwq|Hqw].
    + (* a move at q does not disturb the top row *)
      apply ord_le_lt_trans with (rk (cut q D) ⊕ w).
      { apply naddOrd_monotone; auto. reflexivity. }
      apply ord_le_lt_trans with (rk ((w, succOrd b) :: cut q D)).
      { apply (IHo (rk (cut q D))).
        - apply ord_lt_le_trans with (rk D); auto. apply rk_move_lt.
        - reflexivity.
        - apply rsub_row_cut; auto.
        - apply cut_heights; auto. }
      apply ord_le_lt_trans with
          (rk (cut (mvpt ((w,succOrd b)::D) (inr m)) ((w,succOrd b)::D))).
      { apply rk_mono.
        change (mvpt ((w,succOrd b)::D) (inr m)) with q.
        rewrite cut_cons.
        apply rsub_cons.
        - apply rsub_in with (w ⊓ fst q, succOrd b); simpl; auto.
          split; simpl; [apply glb_greatest; [reflexivity|auto] | reflexivity].
        - apply rsub_cons_r. apply rsub_cons_r. apply rsub_refl. }
      apply rk_move_lt.
    + (* q lies under the top row: answer with a top-row move *)
      assert (Hchain : forall e, fst q + e ≤ w -> rk (cut q D) + e ≤ rk D).
      { intros e He.
        apply ord_le_trans with (rk (cut (w, snd q) D)).
        - rewrite Hcut. exact (rk_chain w b D (fst q) (snd q) Hw Hqy e w He (ord_le_refl w)).
        - apply rk_mono. apply cut_sub. }
      destruct (ABS w (fst q) (rk D) (rk (cut q D)) Hqw (rk_move_lt D m) Hchain)
        as [w' [Hw' Habs]].
      rewrite ord_lt_unfold in Hw'. destruct Hw' as [c Hc].
      apply ord_le_lt_trans with (rk (cut q D) ⊕ w).
      { apply naddOrd_monotone; auto. reflexivity. }
      rewrite Habs.
      apply ord_le_lt_trans with (rk D ⊕ ordSize w c).
      { apply naddOrd_monotone; auto. reflexivity. }
      apply ord_le_lt_trans with (rk ((ordSize w c, succOrd b) :: D)).
      { apply IHw; auto with ord.
        apply rsub_single_trans with (w,b); auto.
        split; simpl; auto with ord. }
      apply row_move_lower; auto.
  - intros j Hj. rewrite ord_lt_unfold in Hj. destruct Hj as [c Hc].
    apply ord_le_lt_trans with (rk D ⊕ ordSize w c).
    { apply naddOrd_monotone; auto. reflexivity. }
    apply ord_le_lt_trans with (rk ((ordSize w c, succOrd b) :: D)).
    { apply IHw; auto with ord.
      apply rsub_single_trans with (w,b); auto.
      split; simpl; auto with ord. }
    apply row_move_lower; auto.
Qed.

Theorem nmulOrd_succ_lower (EM:excluded_middle) (ABS:absorb_prop) a b :
  nmulOrd a b ⊕ a ≤ nmulOrd a (succOrd b).
Proof.
  rewrite (nmul_rk a b), (nmul_rk a (succOrd b)).
  apply ord_le_trans with (rk ((a, succOrd b) :: [(a,b)])).
  - apply rk_row_lower; auto.
    + apply rsub_refl.
    + intros r [Hr|[]]; subst r. reflexivity.
  - apply rk_mono. apply rsub_cons.
    + apply rsub_in with (a, succOrd b); simpl; auto. split; reflexivity.
    + apply rsub_in with (a, succOrd b); simpl; auto.
      split; simpl; [reflexivity | apply ord_lt_le; apply succ_lt].
Qed.

Theorem nmulOrd_succ (EM:excluded_middle) (ABS:absorb_prop) a b :
  nmulOrd a (succOrd b) ≈ nmulOrd a b ⊕ a.
Proof.
  split.
  - apply nmulOrd_succ_upper.
  - apply nmulOrd_succ_lower; auto.
Qed.


(** ** The absorption fact (classical, via Cantor normal forms)

  Let ω^δ be the last Cantor term of [w], so [w = w0 + ω^δ] with every
  exponent of [w0] at least δ.  Split [x'' = H + L] with every exponent
  of [H] at least δ and [L < ω^δ].  Then [w' := w0 + L] works. *)

Section absorb.
Variable EM : excluded_middle.

Let cpl x : complete x := classical.ord_complete EM x.

Lemma each_complete xs : each complete xs.
Proof. induction xs; simpl; auto. Qed.

Lemma omega_exp_closed δ : additively_closed (expOrd ω δ).
Proof. apply expOmega_additively_closed. apply cpl. Qed.

(** Anything below [w0 + ω^δ] is absorbed by adding ω^δ. *)
Lemma below_add_last δ : forall pre,
  (forall a, In a pre -> δ ≤ a) ->
  forall z, z < cantor_denote pre + expOrd ω δ ->
  z + expOrd ω δ ≤ cantor_denote pre + expOrd ω δ.
Proof.
  induction pre as [|a pre IH]; simpl; intros Hpre z Hz.
  - rewrite addOrd_zero_l in *.
    apply additively_closed_collapse; auto. apply omega_exp_closed.
  - rewrite <- addOrd_assoc in *.
    destruct (add_lt _ _ _ Hz) as [Hza|[i Hi]].
    + apply ord_le_trans with (expOrd ω a); [|apply addOrd_le1].
      destruct (classical.order_total EM a δ) as [Had|Hda].
      * apply ord_le_trans with (expOrd ω δ).
        { apply additively_closed_collapse; [apply omega_exp_closed|].
          apply ord_lt_le_trans with (expOrd ω a); auto.
          apply expOrd_monotone; auto. }
        apply expOrd_monotone. apply Hpre; simpl; auto.
      * apply ord_lt_le. apply omega_exp_closed; auto.
        apply expOrd_increasing; auto. apply omega_gt1.
    + rewrite Hi. rewrite <- addOrd_assoc.
      apply addOrd_monotone; [reflexivity|].
      apply IH; [intros; apply Hpre; simpl; auto | auto with ord].
Qed.

Lemma cantor_split δ : forall ls x, cantor_sequence x ls ->
  exists pre suf, ls = pre ++ suf /\
    (forall a, In a pre -> δ ≤ a) /\ (forall a, In a suf -> a < δ).
Proof.
  induction ls as [|a ls IH]; simpl; intros x Hls.
  - exists [], []. simpl; intuition.
  - destruct Hls as [Hxa Hls].
    destruct (classical.order_total EM δ a) as [Hda|Had].
    + destruct (IH a Hls) as [pre [suf [Heq [Hpre Hsuf]]]].
      exists (a::pre), suf. subst ls. simpl. intuition. subst; auto.
    + exists [], (a::ls). simpl. intuition. subst; auto.
      apply ord_le_lt_trans with a; auto.
      apply (cantor_sequence_le1 ls a); auto.
Qed.

Lemma cantor_below δ : forall suf,
  (forall a, In a suf -> a < δ) -> cantor_denote suf < expOrd ω δ.
Proof.
  induction suf as [|a suf IH]; simpl; intros H.
  - apply expOrd_nonzero.
  - apply omega_exp_closed.
    + apply expOrd_increasing; auto. apply omega_gt1.
    + apply IH. intros; apply H; auto.
Qed.

Lemma decompose_at δ x : exists H L,
  x ≈ H + L /\ L < expOrd ω δ /\
  (forall q, q ≤ expOrd ω δ -> H ⊕ q ≤ H + q).
Proof.
  destruct (cantor_decomposition EM x) as [ls [Hls Hx]].
  destruct (cantor_split δ ls x Hls) as [pre [suf [Heq [Hpre Hsuf]]]].
  exists (cantor_denote pre), (cantor_denote suf). split; [|split].
  - rewrite <- Hx. subst ls. apply cantor_denote_app.
  - apply cantor_below; auto.
  - apply cantor_denote_nadd_add; auto. apply each_complete.
Qed.

Lemma last_term w : 0 < w -> exists pre δ,
  w ≈ cantor_denote pre + expOrd ω δ /\ (forall a, In a pre -> δ ≤ a).
Proof.
  intro Hw.
  destruct (cantor_decomposition EM w) as [ls [Hls Hx]].
  destruct ls as [|a ls].
  { simpl in Hx. rewrite <- Hx in Hw. elim (ord_lt_irreflexive 0 Hw). }
  assert (Hne : a :: ls <> []) by discriminate.
  destruct (exists_last Hne) as [pre [δ Heq]].
  rewrite Heq in Hx, Hls.
  exists pre, δ. split.
  - rewrite <- Hx. rewrite cantor_denote_app. simpl.
    rewrite addOrd_zero_r. reflexivity.
  - intros b Hb. apply (cantor_sequence_le pre w [δ] Hls); simpl; auto.
Qed.

Lemma nadd_swap4 a b c d : (a ⊕ b) ⊕ (c ⊕ d) ≈ (a ⊕ d) ⊕ (c ⊕ b).
Proof.
  rewrite <- !naddOrd_assoc.
  rewrite (naddOrd_assoc b c d), (naddOrd_comm (b ⊕ c) d), (naddOrd_comm b c).
  reflexivity.
Qed.

Theorem absorb : absorb_prop.
Proof.
  intros w y x x'' Hyw Hx Hchain.
  assert (Hw0 : 0 < w) by (apply ord_le_lt_trans with y; auto; apply zero_least).
  destruct (last_term w Hw0) as [pre [δ [Hw Hpre]]].
  set (w0 := cantor_denote pre).
  destruct (decompose_at δ x'') as [H [L [Hx'' [HL HD]]]].
  assert (HDw0 : forall q, q ≤ expOrd ω δ -> w0 ⊕ q ≤ w0 + q).
  { apply cantor_denote_nadd_add; auto. apply each_complete. }
  assert (HA1 : y + expOrd ω δ ≤ w).
  { rewrite Hw. apply below_add_last; auto. rewrite <- Hw. auto. }
  assert (Hxx : H + expOrd ω δ ≤ x).
  { apply ord_le_trans with (x'' + expOrd ω δ); auto.
    rewrite Hx''. apply addOrd_monotone; [apply addOrd_le1 | reflexivity]. }
  exists (w0 + L). split.
  - rewrite Hw. apply addOrd_increasing; auto.
  - apply ord_le_trans with ((H ⊕ L) ⊕ (w0 ⊕ expOrd ω δ)).
    { rewrite Hx'', Hw. apply naddOrd_monotone; apply add_nadd_le. }
    rewrite nadd_swap4.
    apply naddOrd_monotone.
    + rewrite HD; auto. reflexivity.
    + apply HDw0. apply ord_lt_le; auto.
Qed.

End absorb.

Theorem nmulOrd_succ_classical (EM:excluded_middle) a b :
  nmulOrd a (succOrd b) ≈ nmulOrd a b ⊕ a.
Proof.
  apply nmulOrd_succ; auto. apply absorb; auto.
Qed.


(** * Distributivity *)

(** ** Region sums

  [rsum R1 R2] stacks the height profiles of [R1] and [R2] column by
  column, using natural sum.  The game on [a × (b ⊕ c)] is the game on
  [rsum [(a,b)] [(a,c)]], and a move at height [b' ⊕ c] corresponds to
  a move at height [b'] in the first component.

  Only the lower bound [rk R1 ⊕ rk R2 ≤ rk (rsum R1 R2)] holds in
  general.  For [R1 = 1 × ω] and [R2 = ω × 1] (each padded with a
  zero-height rectangle of width ω), [rsum] is a column of height ω+1
  over a row of length ω, of rank ω·2+1 > ω ⊕ ω.  This region does arise
  in the [ω × (ω+1)] game, after the move (1,1). *)

Definition rsum (R1 R2:region) : region :=
  flat_map (fun r1 => map (fun r2 => (fst r1 ⊓ fst r2, snd r1 ⊕ snd r2)) R2) R1.

Lemma in_rsum r R1 R2 : In r (rsum R1 R2) <->
  exists r1 r2, In r1 R1 /\ In r2 R2 /\ r = (fst r1 ⊓ fst r2, snd r1 ⊕ snd r2).
Proof.
  unfold rsum. rewrite in_flat_map. split.
  - intros [r1 [H1 H2]]. apply in_map_iff in H2.
    destruct H2 as [r2 [Heq H2]]. exists r1, r2. auto.
  - intros [r1 [r2 [H1 [H2 Heq]]]]. exists r1. split; auto.
    apply in_map_iff. exists r2. auto.
Qed.

Lemma rsum_comm R1 R2 : rsub (rsum R1 R2) (rsum R2 R1).
Proof.
  intros r Hr. right. apply in_rsum in Hr.
  destruct Hr as [r1 [r2 [H1 [H2 Heq]]]]. subst r.
  exists (fst r2 ⊓ fst r1, snd r2 ⊕ snd r1). split.
  - apply in_rsum. exists r2, r1. auto.
  - split; simpl.
    + apply glb_greatest; [apply glb_le2 | apply glb_le1].
    + apply naddOrd_comm.
Qed.

(** Every column below [W] is covered, and nothing is wider than [W]. *)
Definition wide (W:Ord) (R:region) :=
  (exists s, In s R /\ W ≤ fst s) /\ (forall r, In r R -> fst r ≤ W).

Lemma wide_cut W q R : wide W R -> wide W (cut q R).
Proof.
  intros [[s [Hs HWs]] Hle]. split.
  - exists (fst s, snd s ⊓ snd q). split; auto.
    unfold cut. apply in_flat_map. exists s. simpl; auto.
  - intros r Hr. unfold cut in Hr. apply in_flat_map in Hr.
    destruct Hr as [r1 [Hr1 Hin]].
    destruct (cut_piece_le q r1 r Hin) as [H1 _].
    rewrite H1. auto.
Qed.

Lemma list_max (EM:excluded_middle) (P:Ord*Ord -> Prop) : forall l,
  (exists s, In s l /\ P s) ->
  exists s, In s l /\ P s /\ forall s', In s' l -> P s' -> snd s' ≤ snd s.
Proof.
  induction l as [|a l IH]; intros Hex.
  - destruct Hex as [s [[] _]].
  - destruct (EM (exists s, In s l /\ P s)) as [Hl|Hl].
    + destruct (IH Hl) as [s [Hs [HPs Hmax]]].
      destruct (EM (P a)) as [HPa|HPa].
      * destruct (classical.order_total EM (snd a) (snd s)) as [Has|Hsa].
        { exists s. split; [simpl; auto|]. split; auto.
          intros s' [Hs'|Hs'] HPs'; [subst s'; auto | auto]. }
        { exists a. split; [simpl; auto|]. split; auto.
          intros s' [Hs'|Hs'] HPs'; [subst s'; reflexivity|].
          apply ord_lt_le. apply ord_le_lt_trans with (snd s); auto. }
      * exists s. split; [simpl; auto|]. split; auto.
        intros s' [Hs'|Hs'] HPs'; [subst s'; contradiction | auto].
    + destruct Hex as [s [[Hs|Hs] HPs]].
      * subst s. exists a. split; [simpl; auto|]. split; auto.
        intros s' [Hs'|Hs'] HPs'; [subst s'; reflexivity|].
        elim Hl. eauto.
      * elim Hl. eauto.
Qed.

(** ** Superdistributivity (classical) *)

(** Answer a move [q] in the first component by the point
    [(qx, qy ⊕ Y2)], where [Y2] is the tallest rectangle of the second
    component covering column [qx]. *)
Lemma rsum_step (EM:excluded_middle) W R1 R2 (m:mv R1) :
  wide W R1 -> wide W R2 ->
  rk (cut (mvpt R1 m) R1) ⊕ rk R2 ≤ rk (rsum (cut (mvpt R1 m) R1) R2) ->
  rk (cut (mvpt R1 m) R1) ⊕ rk R2 < rk (rsum R1 R2).
Proof.
  intros HW1 HW2 IH.
  destruct (mv_elim R1 m) as [r1 [Hr1 [c [d Hm]]]].
  set (q := mvpt R1 m) in *.
  assert (Hq1 : fst q < fst r1) by (rewrite Hm; simpl; auto with ord).
  assert (Hcov : exists s, In s R2 /\ fst q < fst s).
  { destruct HW2 as [[s [Hs HWs]] _]. exists s. split; auto.
    apply ord_lt_le_trans with (fst r1); auto.
    rewrite <- HWs. apply (proj2 HW1); auto. }
  destruct (list_max EM (fun s => fst q < fst s) R2 Hcov) as [s2 [Hs2 [Hqs2 Hmax]]].
  (* the answering point *)
  assert (Hpx : fst q < fst r1 ⊓ fst s2).
  { apply ord_lt_le_trans with (succOrd (fst q)); [apply succ_lt|].
    apply glb_greatest; apply succ_least; auto. }
  rewrite ord_lt_unfold in Hpx. destruct Hpx as [cg Hcg].
  assert (Hpy : snd q ⊕ snd s2 < snd r1 ⊕ snd s2).
  { apply naddOrd_increasing1. rewrite Hm; simpl; auto with ord. }
  rewrite ord_lt_unfold in Hpy. destruct Hpy as [dg Hdg].
  assert (Hin : In (fst r1 ⊓ fst s2, snd r1 ⊕ snd s2) (rsum R1 R2)).
  { apply in_rsum. exists r1, s2. auto. }
  destruct (mv_intro _ _ Hin cg dg) as [m' Hm'].
  set (p := mvpt (rsum R1 R2) m') in *.
  simpl in Hm'.
  assert (Hqp : fst q ≤ fst p) by (rewrite Hm'; auto).
  assert (Hqp2 : snd q ⊕ snd s2 ≤ snd p) by (rewrite Hm'; auto).
  apply ord_le_lt_trans with (rk (rsum (cut q R1) R2)); auto.
  apply ord_le_lt_trans with (rk (cut p (rsum R1 R2))); [|apply rk_move_lt].
  apply rk_mono.
  intros r Hr. right. apply in_rsum in Hr.
  destruct Hr as [r1' [r2 [H1 [H2 Heq]]]]. subst r.
  unfold cut in H1. apply in_flat_map in H1.
  destruct H1 as [r0 [Hr0 Hpiece]].
  assert (Hsrc : In (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2) (rsum R1 R2)).
  { apply in_rsum. exists r0, r2. auto. }
  simpl in Hpiece. destruct Hpiece as [Hpiece|[Hpiece|[]]]; subst r1'.
  - (* left piece *)
    exists ((fst r0 ⊓ fst r2) ⊓ fst p, snd r0 ⊕ snd r2). split.
    + unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
      simpl; auto.
    + split; simpl; [|reflexivity].
      apply glb_greatest; [apply glb_greatest|].
      * rewrite glb_le1. apply glb_le1.
      * apply glb_le2.
      * rewrite glb_le1. rewrite glb_le2. auto.
  - (* lower piece *)
    destruct (classical.order_total EM (fst r2) (fst q)) as [Hr2q|Hqr2].
    + exists ((fst r0 ⊓ fst r2) ⊓ fst p, snd r0 ⊕ snd r2). split.
      * unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
        simpl; auto.
      * split; simpl.
        { apply glb_greatest; [reflexivity|].
          rewrite glb_le2. rewrite Hr2q. auto. }
        { apply naddOrd_monotone; [apply glb_le1 | reflexivity]. }
    + assert (Hh : snd r2 ≤ snd s2) by (apply Hmax; auto).
      exists (fst r0 ⊓ fst r2, (snd r0 ⊕ snd r2) ⊓ snd p). split.
      * unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
        simpl; auto.
      * split; simpl; [reflexivity|].
        apply glb_greatest.
        { apply naddOrd_monotone; [apply glb_le1 | reflexivity]. }
        { rewrite <- Hqp2. apply naddOrd_monotone; [apply glb_le2 | auto]. }
Qed.

Lemma rsum_lower (EM:excluded_middle) W : forall R1 R2,
  wide W R1 -> wide W R2 -> rk R1 ⊕ rk R2 ≤ rk (rsum R1 R2).
Proof.
  intros R1 R2.
  generalize (ord_le_refl (rk R1 ⊕ rk R2)).
  generalize (rk R1 ⊕ rk R2) at 2 as o. intro o. revert R1 R2.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros R1 R2 Ho HW1 HW2.
  apply naddOrd_least3.
  - intros i Hi.
    destruct (rk_lt_elim R1 i Hi) as [m Hm].
    apply ord_le_lt_trans with (rk (cut (mvpt R1 m) R1) ⊕ rk R2).
    { apply naddOrd_monotone; auto. reflexivity. }
    apply rsum_step with W; auto.
    apply (IHo (rk (cut (mvpt R1 m) R1) ⊕ rk R2)); auto using wide_cut.
    + apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
      apply naddOrd_increasing1. apply rk_move_lt.
    + reflexivity.
  - intros j Hj.
    destruct (rk_lt_elim R2 j Hj) as [m Hm].
    apply ord_le_lt_trans with (rk (cut (mvpt R2 m) R2) ⊕ rk R1).
    { rewrite naddOrd_comm. apply naddOrd_monotone; auto. reflexivity. }
    apply ord_lt_le_trans with (rk (rsum R2 R1)); [|apply rk_mono; apply rsum_comm].
    apply rsum_step with W; auto.
    rewrite naddOrd_comm.
    apply ord_le_trans with (rk (rsum R1 (cut (mvpt R2 m) R2)));
      [| apply rk_mono; apply rsum_comm].
    apply (IHo (rk R1 ⊕ rk (cut (mvpt R2 m) R2))); auto using wide_cut.
    + apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
      apply naddOrd_increasing2. apply rk_move_lt.
    + reflexivity.
Qed.

Theorem nmulOrd_distrib_lower (EM:excluded_middle) a b c :
  nmulOrd a b ⊕ nmulOrd a c ≤ nmulOrd a (b ⊕ c).
Proof.
  set (R1 := [(a,b); (a,0)]). set (R2 := [(a,c); (a,0)]).
  assert (HW : forall y, wide a [(a,y); (a,0)]).
  { intro y. split.
    - exists (a,y). simpl; split; auto. reflexivity.
    - intros r [Hr|[Hr|[]]]; subst r; reflexivity. }
  rewrite (nmul_rk a b), (nmul_rk a c), (nmul_rk a (b ⊕ c)).
  apply ord_le_trans with (rk R1 ⊕ rk R2).
  { apply naddOrd_monotone; apply rk_mono.
    - apply rsub_in with (a,b); simpl; auto. split; reflexivity.
    - apply rsub_in with (a,c); simpl; auto. split; reflexivity. }
  apply ord_le_trans with (rk (rsum R1 R2)).
  { exact (rsum_lower EM a R1 R2 (HW b) (HW c)). }
  apply rk_mono. intros r Hr. right. apply in_rsum in Hr.
  destruct Hr as [r1 [r2 [H1 [H2 Heq]]]]. subst r.
  exists (a, b ⊕ c). split; [simpl; auto|].
  split; simpl.
  - rewrite glb_le1. destruct H1 as [H1|[H1|[]]]; subst r1; reflexivity.
  - apply naddOrd_monotone.
    + destruct H1 as [H1|[H1|[]]]; subst r1; simpl; [reflexivity | apply zero_least].
    + destruct H2 as [H2|[H2|[]]]; subst r2; simpl; [reflexivity | apply zero_least].
Qed.


(** ** Splitting the chain [b ⊕ c] (classical)

  Interleaving the Cantor normal forms of [b] and [c] writes [b ⊕ c] as
  an ordinal sum of blocks ω^z, each tagged with the side it came from.
  Every [v < b ⊕ c] then gets a side and a position on that side;
  positions are strictly increasing within each side and bounded by [b]
  (resp. [c]).  This is the order-preserving bijection [b ⊔ c → b ⊕ c],
  presented as a relation. *)

Section split.
Variable EM : excluded_middle.

Lemma left_subtract x v : x ≤ v -> exists e, v ≈ x + e.
Proof.
  intro Hxv.
  destruct (classical.ord_well_ordered EM (fun e => v ≤ x + e) v (addOrd_le2 x v))
    as [e [He Hleast]].
  exists e. split; auto.
  destruct (classical.order_total EM (x + e) v) as [H|H]; auto.
  destruct (add_lt _ _ _ H) as [H1|[i Hi]].
  - elim (ord_lt_irreflexive x). apply ord_le_lt_trans with v; auto.
  - elim (ord_lt_irreflexive (ordSize e i)).
    apply ord_lt_le_trans with e; auto with ord.
Qed.

Definition tden (tl:list (bool*Ord)) : Ord := cantor_denote (map snd tl).
Definition sden (s:bool) (tl:list (bool*Ord)) : Ord :=
  cantor_denote (map snd (filter (fun e => Bool.eqb (fst e) s) tl)).

Fixpoint splitR (tl:list (bool*Ord)) (v:Ord) (s:bool) (p:Ord) : Prop :=
  match tl with
  | [] => False
  | (t,z) :: tl' =>
      (v < expOrd ω z /\ s = t /\ p ≈ v) \/
      (expOrd ω z ≤ v /\ exists v' p', v ≈ expOrd ω z + v' /\ splitR tl' v' s p' /\
                         p ≈ (if Bool.eqb s t then expOrd ω z + p' else p'))
  end.

Lemma splitR_total : forall tl v, v < tden tl -> exists s p, splitR tl v s p.
Proof.
  induction tl as [|[t z] tl IH]; unfold tden; simpl; intros v Hv.
  - elim (zero_lt v Hv).
  - destruct (classical.order_total EM (expOrd ω z) v) as [Hzv|Hvz].
    + destruct (left_subtract _ _ Hzv) as [v' Hv'].
      assert (Hv'' : v' < tden tl).
      { apply addOrd_cancel_lt with (expOrd ω z). rewrite <- Hv'. auto. }
      destruct (IH v' Hv'') as [s [p' Hsp]].
      exists s, (if Bool.eqb s t then expOrd ω z + p' else p').
      right. split; auto. exists v', p'. split; auto. split; auto. reflexivity.
    + exists t, v. left. split; auto. split; auto. reflexivity.
Qed.

Lemma splitR_bound : forall tl v s p, splitR tl v s p -> p < sden s tl.
Proof.
  induction tl as [|[t z] tl IH]; unfold sden; simpl; intros v s p H.
  - elim H.
  - destruct H as [[Hv [Hs Hp]]|[Hzv [v' [p' [Hv' [Hsp Hp]]]]]].
    + subst s. rewrite Bool.eqb_reflx. simpl.
      rewrite Hp. apply ord_lt_le_trans with (expOrd ω z); auto.
      apply addOrd_le1.
    + generalize (IH v' s p' Hsp). unfold sden. intro Hb.
      rewrite Hp. destruct t, s; simpl in *; auto;
        apply addOrd_increasing; auto.
Qed.

Lemma splitR_mono : forall tl v w s p q,
  splitR tl v s p -> splitR tl w s q -> v < w -> p < q.
Proof.
  induction tl as [|[t z] tl IH]; simpl; intros v w s p q Hv Hw Hvw.
  - elim Hv.
  - destruct Hv as [[Hvz [Hs Hp]]|[Hzv [v' [p' [Hv' [Hsp Hp]]]]]];
    destruct Hw as [[Hwz [Hs' Hq]]|[Hzw [w' [q' [Hw' [Hsq Hq]]]]]].
    + rewrite Hp, Hq; auto.
    + subst s. rewrite Bool.eqb_reflx in Hq.
      rewrite Hp, Hq. apply ord_lt_le_trans with (expOrd ω z); auto.
      apply addOrd_le1.
    + elim (ord_lt_irreflexive v).
      apply ord_lt_le_trans with (expOrd ω z); auto.
      apply ord_lt_trans with w; auto.
    + assert (Hvw' : v' < w').
      { apply addOrd_cancel_lt with (expOrd ω z). rewrite <- Hv', <- Hw'. auto. }
      generalize (IH v' w' s p' q' Hsp Hsq Hvw'). intro Hpq.
      rewrite Hp, Hq. destruct (Bool.eqb s t); auto.
      apply addOrd_increasing; auto.
Qed.

Lemma merge_tags : forall (xs ys zs:list Ord), merge_lists xs ys zs ->
  exists tl : list (bool*Ord), map snd tl = zs /\
    map snd (filter (fun e => Bool.eqb (fst e) true) tl) = xs /\
    map snd (filter (fun e => Bool.eqb (fst e) false) tl) = ys.
Proof.
  intros xs ys zs H. induction H.
  - exists (@nil (bool*Ord)). simpl; auto.
  - destruct IHmerge_lists as [tl [H1 [H2 H3]]].
    exists ((true,x)::tl). simpl. rewrite H1, H2, H3. auto.
  - destruct IHmerge_lists as [tl [H1 [H2 H3]]].
    exists ((false,y)::tl). simpl. rewrite H1, H2, H3. auto.
Qed.

Lemma cantor_sequence_weaken : forall l x x',
  x ≤ x' -> cantor_sequence x l -> cantor_sequence x' l.
Proof.
  destruct l as [|a l]; simpl; intuition.
  rewrite H1. auto.
Qed.

Lemma merge_nil_l : forall (ys:list Ord), merge_lists [] ys ys.
Proof. induction ys; constructor; auto. Qed.

Lemma merge_nil_r : forall (xs:list Ord), merge_lists xs [] xs.
Proof. induction xs; constructor; auto. Qed.

Lemma merge_exists : forall xs ys x y,
  cantor_sequence x xs -> cantor_sequence y ys ->
  exists zs, merge_lists xs ys zs /\ cantor_sequence (x ⊔ y) zs.
Proof.
  induction xs as [|a xs IHx].
  { intros ys x y _ Hys. exists ys. split; [apply merge_nil_l|].
    apply cantor_sequence_weaken with y; auto. apply lub_le2. }
  induction ys as [|b ys IHy].
  { intros x y Hxs _. exists (a::xs). split; [apply merge_nil_r|].
    apply cantor_sequence_weaken with x; auto. apply lub_le1. }
  intros x y [Hxa Hxs] [Hyb Hys].
  destruct (classical.order_total EM b a) as [Hba|Hab].
  - destruct (IHx (b::ys) a b Hxs) as [zs [Hm Hzs]].
    { simpl; split; auto. reflexivity. }
    exists (a::zs). split; [constructor; auto|].
    simpl. split.
    + rewrite <- lub_le1. auto.
    + apply cantor_sequence_weaken with (a ⊔ b); auto.
      apply lub_least; auto. reflexivity.
  - destruct (IHy a b) as [zs [Hm Hzs]]; auto.
    { simpl; split; auto. reflexivity. }
    exists (b::zs). split; [constructor; auto|].
    simpl. split.
    + rewrite <- lub_le2. auto.
    + apply cantor_sequence_weaken with (a ⊔ b); auto.
      apply lub_least; [apply ord_lt_le; auto | reflexivity].
Qed.

(** The split, packaged. *)
Theorem nadd_split b c : exists Sp : Ord -> bool -> Ord -> Prop,
  (forall v, v < b ⊕ c -> exists s p, Sp v s p) /\
  (forall v p, Sp v true p -> p < b) /\
  (forall v p, Sp v false p -> p < c) /\
  (forall v w s p q, Sp v s p -> Sp w s q -> v < w -> p < q).
Proof.
  destruct (cantor_decomposition EM b) as [xs [Hxs Hb]].
  destruct (cantor_decomposition EM c) as [ys [Hys Hc]].
  destruct (merge_exists xs ys b c Hxs Hys) as [zs [Hm Hzs]].
  generalize (nadd_cantor_sequences EM xs ys zs Hm b c (b ⊔ c) Hxs Hys Hzs).
  intro Hbc.
  destruct (merge_tags xs ys zs Hm) as [tl [H1 [H2 H3]]].
  exists (splitR tl). split; [|split; [|split]].
  - intros v Hv. apply splitR_total.
    unfold tden. rewrite H1. rewrite <- Hbc, Hb, Hc. auto.
  - intros v p H. rewrite <- Hb.
    generalize (splitR_bound tl v true p H). unfold sden. rewrite H2. auto.
  - intros v p H. rewrite <- Hc.
    generalize (splitR_bound tl v false p H). unfold sden. rewrite H3. auto.
  - apply splitR_mono.
Qed.

End split.


(** ** Subdistributivity via the split

  Map each point [(u,v)] of the [a × (b ⊕ c)] game to [(u, pos v)] on
  the side of [v].  This map reflects the order, so the game embeds in
  the sum of the [a × b] and [a × c] games.  Coverage is tracked
  semantically: every point of the left region, sent to its side, lies
  in the corresponding right region. *)

Definition sem (R:region) (u v:Ord) := exists r, In r R /\ u < fst r /\ v < snd r.

Lemma glb_lt a x y : a < x -> a < y -> a < x ⊓ y.
Proof.
  intros. apply ord_lt_le_trans with (succOrd a); [apply succ_lt|].
  apply glb_greatest; apply succ_least; auto.
Qed.

Lemma sem_cut_elim p D u v :
  sem (cut p D) u v -> sem D u v /\ (u < fst p \/ v < snd p).
Proof.
  intros [r [Hr [Hu Hv]]].
  unfold cut in Hr. apply in_flat_map in Hr. destruct Hr as [r0 [Hr0 Hin]].
  simpl in Hin. destruct Hin as [Hin|[Hin|[]]]; subst r; simpl in *.
  - split; [exists r0; split; auto; split; auto|].
    + apply ord_lt_le_trans with (fst r0 ⊓ fst p); auto. apply glb_le1.
    + left. apply ord_lt_le_trans with (fst r0 ⊓ fst p); auto. apply glb_le2.
  - split; [exists r0; split; auto; split; auto|].
    + apply ord_lt_le_trans with (snd r0 ⊓ snd p); auto. apply glb_le1.
    + right. apply ord_lt_le_trans with (snd r0 ⊓ snd p); auto. apply glb_le2.
Qed.

Lemma sem_cut_intro q R u y :
  sem R u y -> (u < fst q \/ y < snd q) -> sem (cut q R) u y.
Proof.
  intros [r [Hr [Hu Hy]]] [H|H].
  - exists (fst r ⊓ fst q, snd r). split.
    + unfold cut. apply in_flat_map. exists r. simpl; auto.
    + simpl. split; auto. apply glb_lt; auto.
  - exists (fst r, snd r ⊓ snd q). split.
    + unfold cut. apply in_flat_map. exists r. simpl; auto.
    + simpl. split; auto. apply glb_lt; auto.
Qed.

Lemma sem_move D (m:mv D) : sem D (fst (mvpt D m)) (snd (mvpt D m)).
Proof.
  destruct (mv_elim D m) as [r [Hr [c [d Hm]]]].
  rewrite Hm. exists r. simpl. split; auto. split; auto with ord.
Qed.

Lemma sem_to_move R u y : sem R u y ->
  exists m:mv R, u ≤ fst (mvpt R m) /\ y ≤ snd (mvpt R m).
Proof.
  intros [r [Hr [Hu Hy]]].
  rewrite ord_lt_unfold in Hu, Hy.
  destruct Hu as [c Hc]. destruct Hy as [d Hd].
  destruct (mv_intro R r Hr c d) as [m Hm].
  exists m. rewrite Hm. simpl. auto.
Qed.

Section embed.
Variable T : Ord.
Variable Sp : Ord -> bool -> Ord -> Prop.
Hypothesis Sp_total : forall v, v < T -> exists s p, Sp v s p.
Hypothesis Sp_mono : forall v w s p q, Sp v s p -> Sp w s q -> v < w -> p < q.

Definition side (s:bool) (R1 R2:region) := if s then R1 else R2.

Definition covers (D R1 R2:region) :=
  forall u v, sem D u v ->
    v < T /\ forall s p, Sp v s p -> sem (side s R1 R2) u p.

Lemma covers_rk : forall D R1 R2, covers D R1 R2 -> rk D ≤ rk R1 ⊕ rk R2.
Proof.
  intro D.
  generalize (ord_le_refl (rk D)). generalize (rk D) at 2 as o. intro o. revert D.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros D Ho R1 R2 Hcov.
  apply ord_le_intro. intros i Hi.
  destruct (rk_lt_elim D i Hi) as [m Hm].
  set (p := mvpt D m) in *.
  destruct (Hcov (fst p) (snd p) (sem_move D m)) as [HT Hside].
  destruct (Sp_total (snd p) HT) as [s [π Hπ]].
  generalize (Hside s π Hπ). intro Hsem.
  destruct (sem_to_move _ _ _ Hsem) as [m' [Hq1 Hq2]].
  apply ord_le_lt_trans with (rk (cut p D)); auto.
  assert (Hrk : rk (cut p D) < o).
  { apply ord_lt_le_trans with (rk D); auto. apply rk_move_lt. }
  destruct s; simpl in m', Hq1, Hq2.
  - set (q := mvpt R1 m') in *.
    apply ord_le_lt_trans with (rk (cut q R1) ⊕ rk R2).
    + apply (IHo (rk (cut p D))); auto. reflexivity.
      intros u v Huv.
      destruct (sem_cut_elim p D u v Huv) as [HD Hor].
      destruct (Hcov u v HD) as [HTv Hsidev].
      split; auto. intros s' p' Hs'.
      generalize (Hsidev s' p' Hs'). intro Hsem'.
      destruct s'; simpl in *; auto.
      apply sem_cut_intro; auto.
      destruct Hor as [Hu|Hv].
      * left. apply ord_lt_le_trans with (fst p); auto.
      * right. apply ord_lt_le_trans with π; auto.
        apply (Sp_mono v (snd p) true p' π); auto.
    + apply naddOrd_increasing1. apply rk_move_lt.
  - set (q := mvpt R2 m') in *.
    apply ord_le_lt_trans with (rk R1 ⊕ rk (cut q R2)).
    + apply (IHo (rk (cut p D))); auto. reflexivity.
      intros u v Huv.
      destruct (sem_cut_elim p D u v Huv) as [HD Hor].
      destruct (Hcov u v HD) as [HTv Hsidev].
      split; auto. intros s' p' Hs'.
      generalize (Hsidev s' p' Hs'). intro Hsem'.
      destruct s'; simpl in *; auto.
      apply sem_cut_intro; auto.
      destruct Hor as [Hu|Hv].
      * left. apply ord_lt_le_trans with (fst p); auto.
      * right. apply ord_lt_le_trans with π; auto.
        apply (Sp_mono v (snd p) false p' π); auto.
    + apply naddOrd_increasing2. apply rk_move_lt.
Qed.

End embed.

Theorem nmulOrd_distrib_upper (EM:excluded_middle) a b c :
  nmulOrd a (b ⊕ c) ≤ nmulOrd a b ⊕ nmulOrd a c.
Proof.
  destruct (nadd_split EM b c) as [Sp [Htot [Hb [Hc Hmono]]]].
  rewrite (nmul_rk a b), (nmul_rk a c), (nmul_rk a (b ⊕ c)).
  apply (covers_rk (b ⊕ c) Sp Htot Hmono).
  intros u v [r [[Hr|[]] [Hu Hv]]]. subst r. simpl in Hu, Hv.
  split; auto.
  intros s p Hsp. exists (a, if s then b else c).
  destruct s; simpl; (split; [auto|split; auto]).
  - apply (Hb v p Hsp).
  - apply (Hc v p Hsp).
Qed.

Theorem nmulOrd_distrib (EM:excluded_middle) a b c :
  nmulOrd a (b ⊕ c) ≈ nmulOrd a b ⊕ nmulOrd a c.
Proof.
  split.
  - apply nmulOrd_distrib_upper; auto.
  - apply nmulOrd_distrib_lower; auto.
Qed.


(** * The exponent law: ω^α ⊗ ω^β ≈ ω^(α ⊕ β) *)

Add Parametric Morphism : nmulOrd with signature
    ord_le ++> ord_le ++> ord_le as nmulOrd_le_mor.
Proof. intros. apply nmulOrd_monotone; auto. Qed.

Add Parametric Morphism : nmulOrd with signature
    ord_eq ==> ord_eq ==> ord_eq as nmulOrd_eq_mor.
Proof.
  intros x y [Hxy Hyx] a b [Hab Hba]. split; apply nmulOrd_monotone; auto.
Qed.

(** Subadditivity: a move in a union is a move in one of the parts,
    and only shrinks the other. *)
Lemma rsub_app A A' B B' : rsub A A' -> rsub B B' -> rsub (A ++ B) (A' ++ B').
Proof.
  intros HA HB r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - destruct (HA r Hr) as [Hz|[s [Hs Hrs]]]; auto.
    right. exists s. split; auto. apply in_or_app; auto.
  - destruct (HB r Hr) as [Hz|[s [Hs Hrs]]]; auto.
    right. exists s. split; auto. apply in_or_app; auto.
Qed.

Lemma rk_app_le : forall R1 R2, rk (R1 ++ R2) ≤ rk R1 ⊕ rk R2.
Proof.
  intros R1 R2.
  generalize (ord_le_refl (rk R1 ⊕ rk R2)).
  generalize (rk R1 ⊕ rk R2) at 2 as o. intro o. revert R1 R2.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros R1 R2 Ho.
  apply ord_le_intro. intros i Hi.
  destruct (rk_lt_elim _ i Hi) as [m Hm].
  apply ord_le_lt_trans with (rk (cut (mvpt _ m) (R1 ++ R2))); auto.
  destruct (mv_elim _ m) as [r [Hr [c [d Hp]]]].
  set (p := mvpt (R1 ++ R2) m) in *.
  unfold cut at 1. rewrite flat_map_app. fold (cut p R1). fold (cut p R2).
  apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - destruct (mv_intro R1 r Hr c d) as [m1 Hm1].
    rewrite <- Hp in Hm1.
    apply ord_le_lt_trans with (rk (cut (mvpt R1 m1) R1) ⊕ rk R2).
    + rewrite Hm1.
      apply ord_le_trans with (rk (cut p R1 ++ R2)).
      * apply rk_mono. apply rsub_app; [apply rsub_refl | apply cut_sub].
      * apply (IHo (rk (cut p R1) ⊕ rk R2)); [|reflexivity].
        apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
        apply naddOrd_increasing1. rewrite <- Hm1. apply rk_move_lt.
    + apply naddOrd_increasing1. apply rk_move_lt.
  - destruct (mv_intro R2 r Hr c d) as [m2 Hm2].
    rewrite <- Hp in Hm2.
    apply ord_le_lt_trans with (rk R1 ⊕ rk (cut (mvpt R2 m2) R2)).
    + rewrite Hm2.
      apply ord_le_trans with (rk (R1 ++ cut p R2)).
      * apply rk_mono. apply rsub_app; [apply cut_sub | apply rsub_refl].
      * apply (IHo (rk R1 ⊕ rk (cut p R2))); [|reflexivity].
        apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
        apply naddOrd_increasing2. rewrite <- Hm2. apply rk_move_lt.
    + apply naddOrd_increasing2. apply rk_move_lt.
Qed.

(** Finite natural multiples. *)
Fixpoint nrep (k:nat) (x:Ord) : Ord :=
  match k with
  | O => 0
  | S k => nrep k x ⊕ x
  end.

Lemma nrep_mono k x y : x ≤ y -> nrep k x ≤ nrep k y.
Proof.
  intro H. induction k; simpl; [reflexivity|].
  apply naddOrd_monotone; auto.
Qed.

Add Parametric Morphism k : (nrep k) with signature
    ord_le ++> ord_le as nrep_le_mor.
Proof. intros. apply nrep_mono; auto. Qed.

Add Parametric Morphism k : (nrep k) with signature
    ord_eq ==> ord_eq as nrep_eq_mor.
Proof. intros x y [H1 H2]. split; apply nrep_mono; auto. Qed.

Lemma mul_nat_le_nrep x k : x * natOrdSize k ≤ nrep k x.
Proof.
  induction k; simpl.
  - apply mulOrd_zero_r.
  - rewrite mulOrd_succ. rewrite add_nadd_le.
    apply naddOrd_monotone; auto. reflexivity.
Qed.

Section exponent.
Variable EM : excluded_middle.

Lemma nrep_below k γ δ : γ < δ -> nrep k (expOrd ω γ) < expOrd ω δ.
Proof.
  intro H. induction k; simpl.
  - apply expOrd_nonzero.
  - apply nadd_closed; auto.
    + apply classical.ord_complete; auto.
    + apply expOrd_increasing; auto. apply omega_gt1.
Qed.

Lemma nmul_nrep_l k x y : nmulOrd (nrep k x) y ≈ nrep k (nmulOrd x y).
Proof.
  induction k; simpl.
  - rewrite nmulOrd_comm. apply nmulOrd_zero.
  - rewrite nmulOrd_comm. rewrite nmulOrd_distrib; auto.
    rewrite (nmulOrd_comm y), (nmulOrd_comm y x), IHk. reflexivity.
Qed.

Lemma exp_below u α : u < expOrd ω α ->
  u < 1 \/ exists (i:ordCarrier α) k, u ≤ nrep k (expOrd ω (α i)).
Proof.
  rewrite expOrd_unfold. intro H.
  apply lub_lt in H. destruct H as [H|H]; auto.
  right. apply sup_lt in H. destruct H as [i H].
  rewrite mulOrd_unfold in H. apply sup_lt in H. destruct H as [n H].
  exists i, (S n). apply ord_lt_le.
  rewrite <- mul_nat_le_nrep. simpl.
  rewrite mulOrd_succ. auto.
Qed.

Lemma below_one u : u < 1 -> u ≤ 0.
Proof.
  intro H. rewrite ord_lt_unfold in H. destruct H as [t Ht]. exact Ht.
Qed.

(** One side of the upper bound, shared by both coordinates. *)
Lemma exp_upper_part α β u :
  (forall (i:ordCarrier α), nmulOrd (expOrd ω (α i)) (expOrd ω β) ≤ expOrd ω (α i ⊕ β)) ->
  u < expOrd ω α -> nmulOrd u (expOrd ω β) < expOrd ω (α ⊕ β).
Proof.
  intros IH Hu.
  destruct (exp_below u α Hu) as [H1|[i [k Hk]]].
  - apply ord_le_lt_trans with (nmulOrd 0 (expOrd ω β)).
    + apply nmulOrd_monotone; [apply below_one; auto | reflexivity].
    + rewrite nmulOrd_comm, nmulOrd_zero. apply expOrd_nonzero.
  - rewrite Hk. rewrite nmul_nrep_l.
    rewrite (nrep_mono k _ _ (IH i)).
    apply nrep_below. apply naddOrd_increasing1. apply index_lt.
Qed.

Theorem nmulOrd_exp_upper : forall α β,
  nmulOrd (expOrd ω α) (expOrd ω β) ≤ expOrd ω (α ⊕ β).
Proof.
  induction α as [A f IHa]. intro β.
  induction β as [B g IHb].
  set (α := ord A f) in *. set (β := ord B g) in *.
  rewrite nmul_rk. apply ord_le_intro. intros i Hi.
  destruct (rk_lt_elim _ i Hi) as [m Hm].
  set (p := mvpt [(expOrd ω α, expOrd ω β)] m) in *.
  destruct (mv_elim _ m) as [r [[Hr|[]] [c [d Hp]]]]. subst r.
  change (mvpt _ m) with p in Hp.
  apply ord_le_lt_trans with (rk (cut p [(expOrd ω α, expOrd ω β)])); auto.
  apply ord_le_lt_trans with (rk ([(fst p, expOrd ω β)] ++ [(expOrd ω α, snd p)])).
  { apply rk_mono. intros r Hr. right. simpl in Hr.
    destruct Hr as [Hr|[Hr|[]]]; subst r; simpl.
    - exists (fst p, expOrd ω β). simpl; split; auto. split; [apply glb_le2 | reflexivity].
    - exists (expOrd ω α, snd p). simpl; split; auto. split; [reflexivity | apply glb_le2]. }
  rewrite rk_app_le. rewrite <- !nmul_rk.
  assert (Hpx : fst p < expOrd ω α) by (rewrite Hp; simpl; auto with ord).
  assert (Hpy : snd p < expOrd ω β) by (rewrite Hp; simpl; auto with ord).
  apply nadd_closed; auto.
  - apply classical.ord_complete; auto.
  - apply exp_upper_part; auto.
  - rewrite nmulOrd_comm. rewrite naddOrd_comm.
    apply exp_upper_part; auto.
    intro j. rewrite nmulOrd_comm, naddOrd_comm. apply IHb.
Qed.

Theorem nmulOrd_exp_lower : forall α β,
  expOrd ω (α ⊕ β) ≤ nmulOrd (expOrd ω α) (expOrd ω β).
Proof.
  induction α as [A f IHa]. intro β.
  induction β as [B g IHb].
  set (α := ord A f) in *. set (β := ord B g) in *.
  rewrite expOrd_unfold. apply lub_least.
  - rewrite <- (nmulOrd_one 1) at 1.
    apply nmulOrd_monotone; apply succ_least; apply expOrd_nonzero.
  - apply sup_least. intros [a|b]; simpl;
      rewrite mulOrd_unfold; apply sup_least; intro n;
      rewrite <- mulOrd_succ; rewrite (mul_nat_le_nrep _ (S n)).
    + change ((α ⊕ β) (inl a)) with (f a ⊕ β).
      rewrite (nrep_mono _ _ _ (IHa a β)).
      rewrite <- nmul_nrep_l.
      apply nmulOrd_monotone; [|reflexivity].
      apply ord_lt_le. apply nrep_below. apply (index_lt α a).
    + change ((α ⊕ β) (inr b)) with (α ⊕ g b).
      rewrite (nrep_mono _ _ _ (IHb b)).
      rewrite (nmulOrd_comm (expOrd ω α)).
      rewrite <- nmul_nrep_l. rewrite nmulOrd_comm.
      apply nmulOrd_monotone; [reflexivity|].
      apply ord_lt_le. apply nrep_below. apply (index_lt β b).
Qed.

Theorem nmulOrd_exp α β :
  nmulOrd (expOrd ω α) (expOrd ω β) ≈ expOrd ω (α ⊕ β).
Proof.
  split; [apply nmulOrd_exp_upper | apply nmulOrd_exp_lower].
Qed.

End exponent.


(** * Identification with Hessenberg's natural product

  Classically, writing [a = ω^α1 + ... + ω^αm] and [b = ω^β1 + ... + ω^βn]
  in Cantor normal form, Hessenberg's product is the natural sum of the
  terms [ω^(αi ⊕ βj)] over all pairs [i, j].  We show [nmulOrd] satisfies
  exactly this formula.  It follows from distributivity and the exponent
  law alone; the general form below needs no ordering on the lists. *)

(** All pairwise natural sums of exponents. *)
Definition cnf_prod (xs ys:list Ord) : list Ord :=
  flat_map (fun a => map (fun b => a ⊕ b) ys) xs.

Section hessenberg.
Variable EM : excluded_middle.

Lemma nmul_exp_nadd a ys :
  nmulOrd (expOrd ω a) (cantor_denote_nadd ys) ≈
  cantor_denote_nadd (map (fun b => a ⊕ b) ys).
Proof.
  induction ys as [|b ys IH]; simpl.
  - apply nmulOrd_zero.
  - rewrite nmulOrd_distrib; auto.
    rewrite nmulOrd_exp; auto. rewrite IH. reflexivity.
Qed.

(** Natural sums of ω-powers multiply term by term. *)
Theorem nmulOrd_nadd_powers xs ys :
  nmulOrd (cantor_denote_nadd xs) (cantor_denote_nadd ys) ≈
  cantor_denote_nadd (cnf_prod xs ys).
Proof.
  induction xs as [|a xs IH]; unfold cnf_prod; simpl.
  - rewrite nmulOrd_comm. apply nmulOrd_zero.
  - rewrite cantor_denote_nadd_app.
    rewrite nmulOrd_comm, nmulOrd_distrib; auto.
    rewrite (nmulOrd_comm _ (expOrd ω a)), (nmulOrd_comm _ (cantor_denote_nadd xs)).
    rewrite nmul_exp_nadd, IH. reflexivity.
Qed.

(** The formula on Cantor normal forms. *)
Theorem nmulOrd_cantor xs ys x y :
  cantor_sequence x xs -> cantor_sequence y ys ->
  nmulOrd (cantor_denote xs) (cantor_denote ys) ≈
  cantor_denote_nadd (cnf_prod xs ys).
Proof.
  intros Hxs Hys.
  rewrite (cantor_denote_nadd_eq EM xs x (each_complete EM xs) Hxs).
  rewrite (cantor_denote_nadd_eq EM ys y (each_complete EM ys) Hys).
  apply nmulOrd_nadd_powers.
Qed.

(** [nmulOrd] is Hessenberg's natural product. *)
Theorem nmulOrd_is_hessenberg a b :
  exists xs ys,
    cantor_sequence a xs /\ cantor_denote xs ≈ a /\
    cantor_sequence b ys /\ cantor_denote ys ≈ b /\
    nmulOrd a b ≈ cantor_denote_nadd (cnf_prod xs ys).
Proof.
  destruct (cantor_decomposition EM a) as [xs [Hxs Ha]].
  destruct (cantor_decomposition EM b) as [ys [Hys Hb]].
  exists xs, ys. do 4 (split; auto).
  rewrite <- Ha at 1. rewrite <- Hb at 1.
  apply nmulOrd_cantor with a b; auto.
Qed.

End hessenberg.


(** * Superdistributivity on a decidable universe

  Superdistributivity, [a ⊗ b ⊕ a ⊗ c ≤ a ⊗ (b ⊕ c)], implies weak
  excluded middle in general ([distrib_lower_WEM]), but its proof
  ([rsum_step]) uses excluded middle only to compare corners of
  rectangles with coordinates of moves.  Those comparisons are
  decidable when every ordinal in sight lies in a universe [Q] with a
  decidable order, closed under the operations that build positions:
  [Q] is closed under [≈], [⊕] and [0], and the trees are hereditarily
  in [Q] ([QH]).  For a notation system with interpolants, the
  notations provide such a universe (Notation/CantorProduct.v). *)

Section decidable_universe.
Variable Q : Ord -> Prop.
Hypothesis Q_eq : forall x y, x ≈ y -> Q x -> Q y.
Hypothesis Q_dec : forall x y, Q x -> Q y -> x < y \/ y ≤ x.
Hypothesis Q_zero : Q 0.
Hypothesis Q_nadd : forall x y, Q x -> Q y -> Q (x ⊕ y).

(** Hereditary membership: [x] and all its descendants lie in [Q]. *)
Fixpoint HQ (x:Ord) : Prop :=
  match x with ord A g => forall a, Q (g a) /\ HQ (g a) end.

Definition QH (x:Ord) := Q x /\ HQ x.

Lemma QH_child x i : QH x -> QH (ordSize x i).
Proof. destruct x as [A g]. intros [_ H]. apply H. Qed.

Lemma QH_zero : QH 0.
Proof. split; auto. intros []. Qed.

Lemma Q_glb x y : Q x -> Q y -> Q (x ⊓ y).
Proof.
  intros Hx Hy. destruct (Q_dec x y Hx Hy) as [H|H].
  - apply Q_eq with x; auto. split.
    + apply glb_greatest; [reflexivity | apply ord_lt_le; auto].
    + apply glb_le1.
  - apply Q_eq with y; auto. split.
    + apply glb_greatest; [auto | reflexivity].
    + apply glb_le2.
Qed.

Lemma QH_glb : forall x y, QH x -> QH y -> QH (x ⊓ y).
Proof.
  induction x as [A f IH]. intros [B g] Hx Hy.
  split; [apply Q_glb; [apply Hx | apply Hy]|].
  rewrite glb_unfold. hnf. intros [a b]. simpl.
  apply IH; [apply (proj2 Hx a) | apply (proj2 Hy b)].
Qed.

Lemma HQ_lub x y : HQ x -> HQ y -> HQ (x ⊔ y).
Proof. destruct x as [A f], y as [B g]. intros Hx Hy. rewrite lub_unfold. hnf. intros [a|b]; [apply Hx | apply Hy]. Qed.

Lemma QH_nadd : forall x y, QH x -> QH y -> QH (x ⊕ y).
Proof.
  induction x as [A f IHx]. induction y as [B g IHy]. intros Hx Hy.
  split; [apply Q_nadd; [apply Hx | apply Hy]|].
  rewrite naddOrd_unfold. apply HQ_lub; simpl.
  - intro a. apply IHx; auto. apply (proj2 Hx a).
  - intro b. apply IHy; auto. apply (proj2 Hy b).
Qed.

Lemma QH_nrep k x : QH x -> QH (nrep k x).
Proof. intro Hx. induction k; simpl; [apply QH_zero | apply QH_nadd; auto]. Qed.

(** Regions whose corners are hereditarily in [Q]. *)
Definition QR (R:region) := forall r, In r R -> QH (fst r) /\ QH (snd r).

Lemma QR_move R (m:mv R) : QR R -> QH (fst (mvpt R m)) /\ QH (snd (mvpt R m)).
Proof.
  intro HR. destruct (mv_elim R m) as [r [Hr [c [d Hm]]]]. rewrite Hm. simpl.
  destruct (HR r Hr). split; apply QH_child; auto.
Qed.

Lemma QR_cut p R : QH (fst p) -> QH (snd p) -> QR R -> QR (cut p R).
Proof.
  intros Hp1 Hp2 HR r Hr. unfold cut in Hr. apply in_flat_map in Hr.
  destruct Hr as [r1 [Hr1 Hin]]. destruct (HR r1 Hr1) as [H1 H2].
  destruct Hin as [Hin|[Hin|[]]]; subst r; simpl; split; auto; apply QH_glb; auto.
Qed.

Lemma QR_rsum R1 R2 : QR R1 -> QR R2 -> QR (rsum R1 R2).
Proof.
  intros H1 H2 r Hr. apply in_rsum in Hr.
  destruct Hr as [r1 [r2 [Hr1 [Hr2 Heq]]]]. subst r. simpl.
  destruct (H1 r1 Hr1), (H2 r2 Hr2).
  split; [apply QH_glb | apply QH_nadd]; auto.
Qed.

Lemma exists_dec (Pr:Ord*Ord -> Prop) : forall l,
  (forall s, In s l -> Pr s \/ ~Pr s) ->
  (exists s, In s l /\ Pr s) \/ ~(exists s, In s l /\ Pr s).
Proof.
  induction l as [|a l IH]; intros Hd.
  - right. intros [s [[] _]].
  - destruct (Hd a (or_introl eq_refl)) as [Ha|Ha].
    + left. exists a. simpl; auto.
    + destruct IH as [Hl|Hl]; [intros; apply Hd; simpl; auto | |].
      * left. destruct Hl as [s [Hs HPs]]. exists s. simpl; auto.
      * right. intros [s [[Hs|Hs] HPs]]; [subst; contradiction | eauto].
Qed.

Lemma list_max_Q (Pr:Ord*Ord -> Prop) : forall l,
  (forall s, In s l -> (Pr s \/ ~Pr s) /\ Q (snd s)) ->
  (exists s, In s l /\ Pr s) ->
  exists s, In s l /\ Pr s /\ forall s', In s' l -> Pr s' -> snd s' ≤ snd s.
Proof.
  induction l as [|a l IH]; intros Hd Hex.
  - destruct Hex as [s [[] _]].
  - destruct (exists_dec Pr l) as [Hl|Hl]; [intros; apply Hd; simpl; auto | |].
    + destruct (IH (fun s Hs => Hd s (or_intror Hs)) Hl) as [s [Hs [HPs Hmax]]].
      destruct (Hd a (or_introl eq_refl)) as [[HPa|HPa] HQa].
      * destruct (Q_dec (snd s) (snd a) (proj2 (Hd s (or_intror Hs))) HQa) as [Hsa|Has].
        { exists a. split; [simpl; auto|]. split; auto.
          intros s' [Hs'|Hs'] HPs'; [subst s'; reflexivity|].
          apply ord_lt_le. apply ord_le_lt_trans with (snd s); auto. }
        { exists s. split; [simpl; auto|]. split; auto.
          intros s' [Hs'|Hs'] HPs'; [subst s'; auto | auto]. }
      * exists s. split; [simpl; auto|]. split; auto.
        intros s' [Hs'|Hs'] HPs'; [subst s'; contradiction | auto].
    + destruct Hex as [s [[Hs|Hs] HPs]].
      * subst s. exists a. split; [simpl; auto|]. split; auto.
        intros s' [Hs'|Hs'] HPs'; [subst s'; reflexivity|].
        elim Hl. eauto.
      * elim Hl. eauto.
Qed.

Lemma rsum_step_Q W R1 R2 (m:mv R1) :
  QR R1 -> QR R2 ->
  wide W R1 -> wide W R2 ->
  rk (cut (mvpt R1 m) R1) ⊕ rk R2 ≤ rk (rsum (cut (mvpt R1 m) R1) R2) ->
  rk (cut (mvpt R1 m) R1) ⊕ rk R2 < rk (rsum R1 R2).
Proof.
  intros HQ1 HQ2 HW1 HW2 IH.
  destruct (QR_move R1 m HQ1) as [[Hqx _] _].
  destruct (mv_elim R1 m) as [r1 [Hr1 [c [d Hm]]]].
  set (q := mvpt R1 m) in *.
  assert (Hq1 : fst q < fst r1) by (rewrite Hm; simpl; auto with ord).
  assert (Hcov : exists s, In s R2 /\ fst q < fst s).
  { destruct HW2 as [[s [Hs HWs]] _]. exists s. split; auto.
    apply ord_lt_le_trans with (fst r1); auto.
    rewrite <- HWs. apply (proj2 HW1); auto. }
  assert (Hdec : forall s, In s R2 -> ((fst q < fst s) \/ ~(fst q < fst s)) /\ Q (snd s)).
  { intros s Hs. destruct (HQ2 s Hs) as [[Hs1 _] [Hs2 _]]. split; auto.
    destruct (Q_dec (fst q) (fst s) Hqx Hs1) as [H|H]; [left; auto | right].
    intro H'. apply (ord_lt_irreflexive (fst q)). apply ord_lt_le_trans with (fst s); auto. }
  destruct (list_max_Q (fun s => fst q < fst s) R2 Hdec Hcov) as [s2 [Hs2 [Hqs2 Hmax]]].
  assert (Hpx : fst q < fst r1 ⊓ fst s2).
  { apply ord_lt_le_trans with (succOrd (fst q)); [apply succ_lt|].
    apply glb_greatest; apply succ_least; auto. }
  rewrite ord_lt_unfold in Hpx. destruct Hpx as [cg Hcg].
  assert (Hpy : snd q ⊕ snd s2 < snd r1 ⊕ snd s2).
  { apply naddOrd_increasing1. rewrite Hm; simpl; auto with ord. }
  rewrite ord_lt_unfold in Hpy. destruct Hpy as [dg Hdg].
  assert (Hin : In (fst r1 ⊓ fst s2, snd r1 ⊕ snd s2) (rsum R1 R2)).
  { apply in_rsum. exists r1, s2. auto. }
  destruct (mv_intro _ _ Hin cg dg) as [m' Hm'].
  set (p := mvpt (rsum R1 R2) m') in *.
  simpl in Hm'.
  assert (Hqp : fst q ≤ fst p) by (rewrite Hm'; auto).
  assert (Hqp2 : snd q ⊕ snd s2 ≤ snd p) by (rewrite Hm'; auto).
  apply ord_le_lt_trans with (rk (rsum (cut q R1) R2)); auto.
  apply ord_le_lt_trans with (rk (cut p (rsum R1 R2))); [|apply rk_move_lt].
  apply rk_mono.
  intros r Hr. right. apply in_rsum in Hr.
  destruct Hr as [r1' [r2 [H1 [H2 Heq]]]]. subst r.
  unfold cut in H1. apply in_flat_map in H1.
  destruct H1 as [r0 [Hr0 Hpiece]].
  simpl in Hpiece. destruct Hpiece as [Hpiece|[Hpiece|[]]]; subst r1'.
  - exists ((fst r0 ⊓ fst r2) ⊓ fst p, snd r0 ⊕ snd r2). split.
    + unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
      split; [apply in_rsum; exists r0, r2; auto | simpl; auto].
    + split; simpl; [|reflexivity].
      apply glb_greatest; [apply glb_greatest|].
      * rewrite glb_le1. apply glb_le1.
      * apply glb_le2.
      * rewrite glb_le1. rewrite glb_le2. auto.
  - destruct (HQ2 r2 H2) as [[Hr2x _] _].
    destruct (Q_dec (fst q) (fst r2) Hqx Hr2x) as [Hqr2|Hr2q].
    + assert (Hh : snd r2 ≤ snd s2) by (apply Hmax; auto).
      exists (fst r0 ⊓ fst r2, (snd r0 ⊕ snd r2) ⊓ snd p). split.
      * unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
        split; [apply in_rsum; exists r0, r2; auto | simpl; auto].
      * split; simpl; [reflexivity|].
        apply glb_greatest.
        { apply naddOrd_monotone; [apply glb_le1 | reflexivity]. }
        { rewrite <- Hqp2. apply naddOrd_monotone; [apply glb_le2 | auto]. }
    + exists ((fst r0 ⊓ fst r2) ⊓ fst p, snd r0 ⊕ snd r2). split.
      * unfold cut. apply in_flat_map. exists (fst r0 ⊓ fst r2, snd r0 ⊕ snd r2).
        split; [apply in_rsum; exists r0, r2; auto | simpl; auto].
      * split; simpl.
        { apply glb_greatest; [reflexivity|].
          rewrite glb_le2. rewrite Hr2q. auto. }
        { apply naddOrd_monotone; [apply glb_le1 | reflexivity]. }
Qed.

Lemma rsum_lower_Q W : forall R1 R2,
  QR R1 -> QR R2 -> wide W R1 -> wide W R2 -> rk R1 ⊕ rk R2 ≤ rk (rsum R1 R2).
Proof.
  intros R1 R2.
  generalize (ord_le_refl (rk R1 ⊕ rk R2)).
  generalize (rk R1 ⊕ rk R2) at 2 as o. intro o. revert R1 R2.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros R1 R2 Ho HQ1 HQ2 HW1 HW2.
  apply naddOrd_least3.
  - intros i Hi.
    destruct (rk_lt_elim R1 i Hi) as [m Hm].
    destruct (QR_move R1 m HQ1) as [Hm1 Hm2].
    apply ord_le_lt_trans with (rk (cut (mvpt R1 m) R1) ⊕ rk R2).
    { apply naddOrd_monotone; auto. reflexivity. }
    apply rsum_step_Q with W; auto.
    apply (IHo (rk (cut (mvpt R1 m) R1) ⊕ rk R2)); auto using wide_cut, QR_cut.
    + apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
      apply naddOrd_increasing1. apply rk_move_lt.
    + reflexivity.
  - intros j Hj.
    destruct (rk_lt_elim R2 j Hj) as [m Hm].
    destruct (QR_move R2 m HQ2) as [Hm1 Hm2].
    apply ord_le_lt_trans with (rk (cut (mvpt R2 m) R2) ⊕ rk R1).
    { rewrite naddOrd_comm. apply naddOrd_monotone; auto. reflexivity. }
    apply ord_lt_le_trans with (rk (rsum R2 R1)); [|apply rk_mono; apply rsum_comm].
    apply rsum_step_Q with W; auto.
    rewrite naddOrd_comm.
    apply ord_le_trans with (rk (rsum R1 (cut (mvpt R2 m) R2)));
      [| apply rk_mono; apply rsum_comm].
    apply (IHo (rk R1 ⊕ rk (cut (mvpt R2 m) R2))); auto using wide_cut, QR_cut.
    + apply ord_lt_le_trans with (rk R1 ⊕ rk R2); auto.
      apply naddOrd_increasing2. apply rk_move_lt.
    + reflexivity.
Qed.

Theorem nmulOrd_distrib_lower_Q a b c :
  QH a -> QH b -> QH c ->
  nmulOrd a b ⊕ nmulOrd a c ≤ nmulOrd a (b ⊕ c).
Proof.
  intros Ha Hb Hc.
  set (R1 := [(a,b); (a,0)]). set (R2 := [(a,c); (a,0)]).
  assert (HW : forall y, wide a [(a,y); (a,0)]).
  { intro y. split.
    - exists (a,y). simpl; split; auto. reflexivity.
    - intros r [Hr|[Hr|[]]]; subst r; reflexivity. }
  assert (HQR : forall y, QH y -> QR [(a,y); (a,0)]).
  { intros y Hy r [Hr|[Hr|[]]]; subst r; simpl; auto using QH_zero. }
  rewrite (nmul_rk a b), (nmul_rk a c), (nmul_rk a (b ⊕ c)).
  apply ord_le_trans with (rk R1 ⊕ rk R2).
  { apply naddOrd_monotone; apply rk_mono.
    - apply rsub_in with (a,b); simpl; auto. split; reflexivity.
    - apply rsub_in with (a,c); simpl; auto. split; reflexivity. }
  apply ord_le_trans with (rk (rsum R1 R2)).
  { exact (rsum_lower_Q a R1 R2 (HQR b Hb) (HQR c Hc) (HW b) (HW c)). }
  apply rk_mono. intros r Hr. right. apply in_rsum in Hr.
  destruct Hr as [r1 [r2 [H1 [H2 Heq]]]]. subst r.
  exists (a, b ⊕ c). split; [simpl; auto|].
  split; simpl.
  - rewrite glb_le1. destruct H1 as [H1|[H1|[]]]; subst r1; reflexivity.
  - apply naddOrd_monotone.
    + destruct H1 as [H1|[H1|[]]]; subst r1; simpl; [reflexivity | apply zero_least].
    + destruct H2 as [H2|[H2|[]]]; subst r2; simpl; [reflexivity | apply zero_least].
Qed.

Lemma nmul_nrep_lower_Q k x y : QH x -> QH y ->
  nrep k (nmulOrd x y) ≤ nmulOrd (nrep k x) y.
Proof.
  intros Hx Hy. induction k; simpl.
  - apply zero_least.
  - rewrite IHk.
    rewrite (nmulOrd_comm (nrep k x)), (nmulOrd_comm x), (nmulOrd_comm _ y).
    apply nmulOrd_distrib_lower_Q; auto. apply QH_nrep; auto.
Qed.

(** Subdistributivity on the universe: [covers_rk], with the split
    needed only at points of the universe. *)
Section embed_Q.
Variable T : Ord.
Variable Sp : Ord -> bool -> Ord -> Prop.
Hypothesis Sp_total : forall v, Q v -> v < T -> exists s p, Sp v s p.
Hypothesis Sp_mono : forall v w s p q,
  Q v -> Q w -> Sp v s p -> Sp w s q -> v < w -> p < q.

Definition covers_Q (D R1 R2:region) :=
  forall u v, sem D u v -> Q v ->
    v < T /\ forall s p, Sp v s p -> sem (side s R1 R2) u p.

Lemma covers_rk_Q : forall D R1 R2, QR D -> covers_Q D R1 R2 -> rk D ≤ rk R1 ⊕ rk R2.
Proof.
  intro D.
  generalize (ord_le_refl (rk D)). generalize (rk D) at 2 as o. intro o. revert D.
  induction o as [o IHo] using (well_founded_ind ord_lt_wf).
  intros D Ho R1 R2 HQD Hcov.
  apply ord_le_intro. intros i Hi.
  destruct (rk_lt_elim D i Hi) as [m Hm].
  destruct (QR_move D m HQD) as [Hp1 Hp2].
  set (p := mvpt D m) in *.
  destruct (Hcov (fst p) (snd p) (sem_move D m) (proj1 Hp2)) as [HT Hside].
  destruct (Sp_total (snd p) (proj1 Hp2) HT) as [s [π Hπ]].
  generalize (Hside s π Hπ). intro Hsem.
  destruct (sem_to_move _ _ _ Hsem) as [m' [Hq1 Hq2]].
  apply ord_le_lt_trans with (rk (cut p D)); auto.
  assert (Hrk : rk (cut p D) < o).
  { apply ord_lt_le_trans with (rk D); auto. apply rk_move_lt. }
  assert (HQc : QR (cut p D)) by (apply QR_cut; auto).
  destruct s; simpl in m', Hq1, Hq2.
  - set (q := mvpt R1 m') in *.
    apply ord_le_lt_trans with (rk (cut q R1) ⊕ rk R2).
    + apply (IHo (rk (cut p D))); auto. reflexivity.
      intros u v Huv HQv.
      destruct (sem_cut_elim p D u v Huv) as [HD Hor].
      destruct (Hcov u v HD HQv) as [HTv Hsidev].
      split; auto. intros s' p' Hs'.
      generalize (Hsidev s' p' Hs'). intro Hsem'.
      destruct s'; simpl in *; auto.
      apply sem_cut_intro; auto.
      destruct Hor as [Hu|Hv].
      * left. apply ord_lt_le_trans with (fst p); auto.
      * right. apply ord_lt_le_trans with π; auto.
        apply (Sp_mono v (snd p) true p' π); auto. apply Hp2.
    + apply naddOrd_increasing1. apply rk_move_lt.
  - set (q := mvpt R2 m') in *.
    apply ord_le_lt_trans with (rk R1 ⊕ rk (cut q R2)).
    + apply (IHo (rk (cut p D))); auto. reflexivity.
      intros u v Huv HQv.
      destruct (sem_cut_elim p D u v Huv) as [HD Hor].
      destruct (Hcov u v HD HQv) as [HTv Hsidev].
      split; auto. intros s' p' Hs'.
      generalize (Hsidev s' p' Hs'). intro Hsem'.
      destruct s'; simpl in *; auto.
      apply sem_cut_intro; auto.
      destruct Hor as [Hu|Hv].
      * left. apply ord_lt_le_trans with (fst p); auto.
      * right. apply ord_lt_le_trans with π; auto.
        apply (Sp_mono v (snd p) false p' π); auto. apply Hp2.
    + apply naddOrd_increasing2. apply rk_move_lt.
Qed.
End embed_Q.

End decidable_universe.


(** * Toward a constructive split

  ** A split on all ordinals is not constructive

  [covers_rk] needs only a split of [b ⊕ c]; EM enters only through
  [nadd_split].  But a split in exactly the form of [nadd_split],
  total on every ordinal below [b ⊕ c] with a boolean side, already
  implies weak excluded middle.  Take [b = c = 1]: all positions are
  below 1, so two comparable heights never share a side, and the side
  of the height [ord P (fun _ => 0)] (which is 0 or 1 according to [P])
  decides [~P \/ ~~P].  So any constructive version must weaken
  the interface, e.g. require totality only on heights that actually
  occur as moves. *)

Definition split_spec (b c:Ord) (Sp:Ord -> bool -> Ord -> Prop) :=
  (forall v, v < b ⊕ c -> exists s p, Sp v s p) /\
  (forall v p, Sp v true p -> p < b) /\
  (forall v p, Sp v false p -> p < c) /\
  (forall v w s p q, Sp v s p -> Sp w s q -> v < w -> p < q).

Theorem split_WEM :
  (forall b c, exists Sp, split_spec b c Sp) -> weak_excluded_middle.
Proof.
  intros H P.
  destruct (H 1 1) as [Sp [Htot [Hb [Hc Hm]]]].
  assert (H12 : 1 < 1 ⊕ 1).
  { apply ord_le_lt_trans with (1 ⊕ 0); [apply naddOrd_zero_r|].
    apply naddOrd_increasing2. apply succ_lt. }
  assert (Hpos : forall v s p, Sp v s p -> p ≤ 0).
  { intros v s p Hsp. apply below_one.
    destruct s; [apply (Hb v) | apply (Hc v)]; auto. }
  assert (Hsame : forall v w s p q, Sp v s p -> Sp w s q -> v < w -> False).
  { intros v w s p q Hv Hw Hvw.
    apply (zero_lt p). rewrite <- (Hpos w s q Hw). apply (Hm v w s p q); auto. }
  set (e := ord P (fun _ => 0)).
  assert (He : e ≤ 1).
  { unfold e. rewrite ord_le_unfold. simpl. intros _. apply succ_lt. }
  destruct (Htot 0) as [s0 [p0 H0]].
  { apply ord_le_lt_trans with 1; auto. apply zero_least. }
  destruct (Htot 1 H12) as [s1 [p1 H1]].
  destruct (Htot e) as [se [pe He']].
  { apply ord_le_lt_trans with 1; auto. }
  assert (H01 : s0 <> s1).
  { intro Heq. subst s1. apply (Hsame 0 1 s0 p0 p1); auto. apply succ_lt. }
  destruct (Bool.bool_dec se s0) as [Heq|Hne].
  - (* same side as 0: P is refuted *)
    right. intro HP. subst se.
    apply (Hsame 0 e s0 p0 pe); auto.
    unfold e. rewrite ord_lt_unfold. simpl. exists HP. reflexivity.
  - (* different side from 0: ~P is refuted *)
    left. intro HnP.
    assert (He0 : e < 1).
    { apply ord_le_lt_trans with 0; [|apply succ_lt].
      unfold e. rewrite ord_le_unfold. simpl. intro HP. elim (HnP HP). }
    destruct se, s0, s1; try congruence;
      exact (Hsame e 1 _ pe p1 He' H1 He0).
Qed.


(** ** The general row lemma implies excluded middle

  [rk_row_lower] places a row of width [w] over an arbitrary region [D]
  covering [w × b].  In that generality its statement already implies
  excluded middle.  Take [w = 1 ⊔ sup_{P} ω] (ω if [P], 1 otherwise),
  [d = 1 + w], and [D = d × 1].  The natural-sum child [1 ⊕ w] of
  [rk D ⊕ w] must be reached by some move:
  - a top-row move into a [P]-indexed child of [w] proves [P];
  - the top-row move into the child 0 of [w], or any move inside [D],
    reaches only [d] or a finite rank, which refutes [P].
  So a constructive proof of the successor law cannot go through the row
  lemma for arbitrary [D]; at most it can use it for full rectangles. *)

Lemma rk_row_upper w b D :
  rsub [(w,b)] D -> (forall r, In r D -> snd r ≤ b) ->
  rk ((w, succOrd b) :: D) ≤ rk D ⊕ w.
Proof.
  intros Hw Hh. unfold rk at 1.
  rewrite grank_row_upper; eauto.
  apply naddOrd_monotone; [apply grank_le_rk | reflexivity].
Qed.

Lemma nat_nadd n m : natOrdSize n ⊕ natOrdSize m ≈ natOrdSize (n + m)%nat.
Proof.
  induction m; simpl.
  - rewrite PeanoNat.Nat.add_0_r. apply naddOrd_zero_r.
  - rewrite PeanoNat.Nat.add_succ_r. simpl.
    rewrite naddOrd_succ2. rewrite IHm. reflexivity.
Qed.

Lemma below_omega_double x : x < ω -> x ⊕ x < ω.
Proof.
  intro H. rewrite ord_lt_unfold in H. destruct H as [n Hn]. simpl in Hn.
  rewrite Hn. rewrite nat_nadd. apply (index_lt ω (n+n)%nat).
Qed.

Theorem row_lower_EM :
  (forall w D b, rsub [(w,b)] D -> (forall r, In r D -> snd r ≤ b) ->
     rk D ⊕ w ≤ rk ((w, succOrd b) :: D)) ->
  excluded_middle.
Proof.
  intros RL P.
  set (s := supOrd (fun _:P => ω)).
  set (w := 1 ⊔ s).
  set (d := 1 + w).
  assert (Hs : s ≤ ω) by (apply sup_least; intros; reflexivity).
  assert (Hw1 : 1 ≤ w) by apply lub_le1.
  assert (Hwω : w ≤ ω) by (apply lub_least; auto; apply ord_lt_le; apply omega_gt1).
  assert (Hdω : d ≤ ω).
  { unfold d. rewrite Hwω. apply additively_closed_collapse.
    - apply additively_closed_omega.
    - apply omega_gt1. }
  assert (Hd1 : 1 < d).
  { unfold d. apply ord_le_lt_trans with (1 + 0); [apply addOrd_zero_r|].
    apply addOrd_increasing. apply ord_lt_le_trans with 1; auto. apply succ_lt. }
  assert (Hwd : w ≤ d) by apply addOrd_le2.
  (* under P, [1 ⊕ w] exceeds ω *)
  assert (Hbig : P -> ω < 1 ⊕ w).
  { intro p. apply ord_lt_le_trans with (ω ⊕ 1).
    - apply ord_le_lt_trans with (ω ⊕ 0); [apply naddOrd_zero_r|].
      apply naddOrd_increasing2. apply succ_lt.
    - rewrite naddOrd_comm. apply naddOrd_monotone; [reflexivity|].
      apply ord_le_trans with s; [|apply lub_le2].
      unfold s. apply (sup_le _ (fun _:P => ω) p). }
  set (D := [(d, 1)]).
  assert (HrkD : rk D ≈ d).
  { unfold D. rewrite <- nmul_rk. apply nmulOrd_one. }
  assert (Hz : 1 ⊕ w < rk ((w, succOrd 1) :: D)).
  { apply ord_lt_le_trans with (rk D ⊕ w).
    - rewrite HrkD. apply naddOrd_increasing1; auto.
    - apply RL.
      + apply rsub_in with (d,1); simpl; auto. split; simpl; auto. reflexivity.
      + intros r [Hr|[]]; subst r. reflexivity. }
  destruct (rk_lt_elim _ _ Hz) as [m Hm].
  destruct m as [[c t]|[[k t]|[]]].
  - (* a top-row move to width [w c] *)
    assert (Hup : 1 ⊕ w ≤ d ⊕ ordSize w c).
    { rewrite Hm. rewrite <- HrkD.
      apply ord_le_trans with (rk ((ordSize w c, succOrd 1) :: D)).
      - apply rk_mono. simpl mvpt. rewrite cut_cons.
        apply rsub_cons.
        { apply rsub_in with (ordSize w c, succOrd 1); simpl; auto.
          split; simpl; [apply glb_le2 | reflexivity]. }
        apply rsub_cons.
        { apply rsub_in with (d, 1); simpl; auto.
          split; simpl; auto. apply glb_le2. }
        apply rsub_cons_r. apply cut_sub.
      - apply rk_row_upper.
        + apply rsub_in with (d,1); simpl; auto.
          split; simpl; [rewrite <- Hwd; apply index_le | reflexivity].
        + intros r [Hr|[]]; subst r. reflexivity. }
    destruct c as [u|[p n]].
    + (* the child 0 of [w]: refutes P *)
      right. intro p.
      apply (ord_lt_irreflexive ω).
      apply ord_lt_le_trans with (1 ⊕ w); auto.
      rewrite Hup. change (ordSize w (inl u)) with zeroOrd.
      rewrite naddOrd_zero_r. auto.
    + (* a P-indexed child *)
      left. exact p.
  - (* a move inside D: everything left is finite *)
    right. intro p.
    set (dk := ordSize d k).
    assert (Hup : 1 ⊕ w ≤ dk ⊕ dk).
    { rewrite Hm.
      apply ord_le_trans with (rk [(dk, succOrd 1)]).
      - apply rk_mono. simpl mvpt. unfold D. rewrite !cut_cons.
        unfold cut; simpl.
        apply rsub_cons.
        { apply rsub_in with (dk, succOrd 1); simpl; auto.
          split; simpl; [apply glb_le2 | reflexivity]. }
        apply rsub_cons.
        { intros r [Hr|[]]; subst r. left. right. simpl. apply glb_le2. }
        apply rsub_cons.
        { apply rsub_in with (dk, succOrd 1); simpl; auto.
          split; simpl; [apply glb_le2 | apply ord_lt_le; apply succ_lt]. }
        apply rsub_cons; [|apply rsub_nil].
        { intros r [Hr|[]]; subst r. left. right. simpl. apply glb_le2. }
      - rewrite <- nmul_rk. rewrite nmulOrd_succ_upper.
        rewrite nmulOrd_one. reflexivity. }
    assert (Hdk : dk < ω) by (apply ord_lt_le_trans with d; auto; apply index_lt).
    apply (ord_lt_irreflexive ω).
    apply ord_lt_le_trans with (1 ⊕ w); auto.
    rewrite Hup. apply ord_lt_le. apply below_omega_double; auto.
Qed.


(** ** The successor law implies weak excluded middle

  Found by a search in a two-world Kripke model (P undecided, then true).
  Let [c1 = ord P (fun _ => ω)] (0, or ω+1 if [P]), [c2 = succ (ord P
  (fun _ => 0))] (1, or 2 if [P]), and let [a] have exactly the two
  children [c1] and [c2].  These children are not directed: which of them
  is larger depends on [P].  In [a ⊕ a ≤ a ⊗ 2], the natural-sum child
  [c1 ⊕ a] must be matched by a top-row move into [c1] or [c2]:
  - into [c2] reaches at most [a ⊕ c2], which refutes [P];
  - into [c1]: then [c1 ⊕ c2] must be matched by a move inside [c1 × 2]
    (which needs a proof of [P]), at [(c1, 0)] (reaching [c1 ⊕ c1], which
    refutes [~P]), or at [(c2, 0)] (reaching [c2 ⊕ (c1 ⊓ c2)], which
    refutes [P]).
  So the lower half of the successor law, for all ordinals, is not
  constructive.  Completeness does not rescue it either; see
  [succ_lower_complete_WEM] below. *)

Lemma rk_one x : rk [(x, 1)] ≈ x.
Proof. rewrite <- nmul_rk. apply nmulOrd_one. Qed.

Lemma rk_two x : rk [(x, succOrd 1)] ≤ x ⊕ x.
Proof.
  rewrite <- nmul_rk. rewrite nmulOrd_succ_upper.
  apply naddOrd_monotone; [apply nmulOrd_one | reflexivity].
Qed.

Lemma succ_one_glb_child (y : ordCarrier (succOrd 1 ⊓ 1)) :
  ordSize (succOrd 1 ⊓ 1) y ≤ 0.
Proof.
  rewrite ord_le_unfold. simpl in *. destruct y as [[] []]. simpl. intros [_ []].
Qed.

Theorem succ_lower_WEM :
  (forall a b, nmulOrd a b ⊕ a ≤ nmulOrd a (succOrd b)) ->
  weak_excluded_middle.
Proof.
  intros SL P.
  pose (c1 := ord P (fun _ => ω)).
  pose (e := ord P (fun _ => zeroOrd)).
  pose (c2 := succOrd e).
  pose (a := ord bool (fun x:bool => if x then c1 else c2)).
  assert (Hc1P : P -> ω < c1).
  { intro p. unfold c1. rewrite ord_lt_unfold. exists p. reflexivity. }
  assert (Hc1nP : ~P -> c1 ≤ 0).
  { intro np. unfold c1. rewrite ord_le_unfold. intro p. elim (np p). }
  assert (Hc2small : c2 < ω).
  { apply ord_le_lt_trans with (natOrdSize 2); [|apply (index_lt ω 2%nat)].
    unfold c2. simpl. apply succ_monotone.
    unfold e. rewrite ord_le_unfold. intro q. simpl. apply succ_lt. }
  assert (Hc2pos : 0 < c2).
  { unfold c2. apply succ_trans. apply zero_least. }
  assert (Hc1a : c1 < a) by apply (index_lt a true).
  assert (Hc2a : c2 < a) by apply (index_lt a false).
  (* c1 ≤ c2 refutes P;  c2 ≤ c1 refutes ~P *)
  assert (HnotP : c1 ≤ c2 -> ~P).
  { intros H p. apply (ord_lt_irreflexive ω).
    apply ord_lt_le_trans with c1; auto. rewrite H. apply ord_lt_le; auto. }
  assert (HnotnotP : c2 ≤ c1 -> ~~P).
  { intros H np. apply (ord_lt_irreflexive 0).
    apply ord_lt_le_trans with c2; auto. rewrite H. auto. }
  assert (HA : a ⊕ a ≤ rk [(a, succOrd 1)]).
  { rewrite <- nmul_rk.
    apply ord_le_trans with (nmulOrd a 1 ⊕ a); [|apply SL].
    apply naddOrd_monotone; [apply nmulOrd_one | reflexivity]. }
  assert (Hz1 : c1 ⊕ a < rk [(a, succOrd 1)]).
  { apply ord_lt_le_trans with (a ⊕ a); auto. apply naddOrd_increasing1; auto. }
  destruct (rk_lt_elim _ _ Hz1) as [m Hm].
  destruct m as [[x t]|[]].
  destruct x.
  - (* top-row answer into c1 *)
    change (mvpt [(a, succOrd 1)] (inl (true, t))) with (c1, natOrdSize 1) in Hm.
    set (R1 := cut (c1, natOrdSize 1) [(a, succOrd 1)]) in *.
    assert (Hz2 : c1 ⊕ c2 < rk R1).
    { apply ord_lt_le_trans with (c1 ⊕ a); auto. apply naddOrd_increasing2; auto. }
    destruct (rk_lt_elim _ _ Hz2) as [m2 Hm2].
    destruct m2 as [[[xb p] y]|[[x2 y2]|[]]].
    + (* a move inside c1 × 2 carries a proof of P *)
      left. intro np. exact (np p).
    + set (v := ordSize (succOrd 1 ⊓ 1) y2).
      assert (Hv : v ≤ 0) by apply succ_one_glb_child.
      destruct x2.
      * (* at (c1, 0): reaches only c1 ⊕ c1 *)
        left. apply HnotnotP.
        apply (naddOrd_cancel_le _ _ c1).
        rewrite (naddOrd_comm c2 c1).
        rewrite Hm2.
        rewrite <- rk_two.
        apply rk_mono.
        change (mvpt R1 (inr (inl (true, y2)))) with (c1, v).
        unfold R1. rewrite !cut_cons.
        intros r Hr. simpl in Hr.
        destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r.
        { right. exists (c1, succOrd 1). simpl; split; auto. split; simpl; [apply glb_le2 | reflexivity]. }
        { left. right. simpl. rewrite glb_le2. auto. }
        { right. exists (c1, succOrd 1). simpl; split; auto.
          split; simpl; [apply glb_le2 | apply glb_le1]. }
        { left. right. simpl. rewrite glb_le2. auto. }
      * (* at (c2, 0): reaches only c2 ⊕ (c1 ⊓ c2) *)
        right. apply HnotP.
        apply ord_le_trans with (c1 ⊓ c2); [|apply glb_le2].
        apply (naddOrd_cancel_le _ _ c2).
        rewrite Hm2.
        apply ord_le_trans with (rk ((c1 ⊓ c2, succOrd 1) :: [(c2, 1)])).
        -- apply rk_mono.
           change (mvpt R1 (inr (inl (false, y2)))) with (c2, v).
           unfold R1. rewrite !cut_cons.
           intros r Hr. simpl in Hr.
           destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r.
           { right. exists (c1 ⊓ c2, succOrd 1). simpl; split; auto.
             split; simpl; [|reflexivity].
             apply glb_greatest; [rewrite glb_le1; apply glb_le2 | apply glb_le2]. }
           { left. right. simpl. rewrite glb_le2. auto. }
           { right. exists (c2, 1). simpl; split; auto.
             split; simpl; apply glb_le2. }
           { left. right. simpl. rewrite glb_le2. auto. }
        -- rewrite (rk_row_upper (c1 ⊓ c2) 1 [(c2, 1)]).
           ++ rewrite rk_one. rewrite naddOrd_comm. reflexivity.
           ++ apply rsub_in with (c2, 1); simpl; auto.
              split; simpl; [apply glb_le2 | reflexivity].
           ++ intros r [Hr|[]]; subst r. reflexivity.
  - (* top-row answer into c2: reaches only a ⊕ c2 *)
    change (mvpt [(a, succOrd 1)] (inl (false, t))) with (c2, natOrdSize 1) in Hm.
    right. apply HnotP.
    apply (naddOrd_cancel_le _ _ a).
    rewrite Hm.
    apply ord_le_trans with (rk ((c2, succOrd 1) :: [(a, 1)])).
    + apply rk_mono. rewrite cut_cons.
      apply rsub_cons.
      { apply rsub_in with (c2, succOrd 1); simpl; auto.
        split; simpl; [apply glb_le2 | reflexivity]. }
      apply rsub_cons_r. apply rsub_cons.
      { apply rsub_in with (a, 1); simpl; auto.
        split; simpl; [reflexivity | apply glb_le2]. }
      apply rsub_nil.
    + rewrite (rk_row_upper c2 1 [(a, 1)]).
      * rewrite rk_one. rewrite naddOrd_comm. reflexivity.
      * apply rsub_in with (a, 1); simpl; auto.
        split; simpl; [apply ord_lt_le; auto | reflexivity].
      * intros r [Hr|[]]; subst r. reflexivity.
Qed.

(** ** Completeness does not help

  The witness above has non-directed children.  This one is complete:
  let [c n] have the children [n] and, if [P], [ω] (so [c n] is [n+1],
  or [ω+1] if [P]), and let [a] be the limit of the increasing sequence
  [c 0, c 1, ...].  The [c n] are directed, and so is [a].  In
  [a ⊕ a ≤ a ⊗ 2], the opponent plays three moves:
  - [c 0 ⊕ a], answered by a top-row move into some [c n];
  - [c 0 ⊕ c (n+1)], from the column just beyond that answer.  The answer
    either shrinks the top row to [n] (reaching only [a ⊕ n], which
    refutes [P]) or plays at [(c j, 0)] in the bottom row, which also
    cuts the top row, leaving [c n × 2 ∪ c j × 1];
  - [c 0 ⊕ (n+1)].  The answer must now shrink the top row to [n]
    (reaching [c 0 ⊕ n] under [P], one move short) or the bottom row to
    [j] (reaching a finite rank, which refutes [P]).
  Each answer is either a move into a [P]-indexed child, proving [P], or
  refutes [P].  The opponent wins because the answer's column must be
  chosen before the opponent's: a strategy for the successor law has to
  commit to one column of the top row, while the matching natural-sum
  move can use any column.

  The Kripke search initially missed this witness.  Its opponent sampled
  too few sequence indices, and a bug in its comparison of limits
  produced spurious glbs.  Both are fixed in tools/kripke. *)

Theorem succ_lower_complete_WEM :
  (forall a b, complete a -> complete b ->
     nmulOrd a b ⊕ a ≤ nmulOrd a (succOrd b)) ->
  weak_excluded_middle.
Proof.
  intros SL P.
  pose (c := fun n:nat => ord (option P)
         (fun o => match o with None => natOrdSize n | Some _ => ω end)).
  pose (a := ord nat c).
  assert (Hca : forall n, c n < a) by (intro n; apply (index_lt a n)).
  assert (Hnc : forall n, natOrdSize n < c n) by (intro n; apply (index_lt (c n) None)).
  assert (HcP : P -> forall i j, c i ≤ c j).
  { intros p i j. rewrite ord_le_unfold. intros [q|]; simpl.
    - apply (index_lt (c j) (Some p)).
    - apply ord_lt_trans with ω; [apply (index_lt ω i) | apply (index_lt (c j) (Some p))]. }
  assert (HwP : P -> forall i, ω < c i) by (intros p i; apply (index_lt (c i) (Some p))).
  assert (Hmono : forall i j, (i <= j)%nat -> c i ≤ c j).
  { intros i j Hij. rewrite ord_le_unfold. intros [q|]; simpl.
    - apply (index_lt (c j) (Some q)).
    - apply ord_le_lt_trans with (natOrdSize j); auto. apply natOrdSize_monotone; auto. }
  assert (Hcomp : complete a).
  { simpl. split; [|split].
    - intros i j. exists (Nat.max i j). split; apply Hmono.
      + apply PeanoNat.Nat.le_max_l.
      + apply PeanoNat.Nat.le_max_r.
    - left. exact (inhabits 0%nat).
    - intro n. simpl. split; [|split].
      + intros [p|] [q|].
        * exists (Some p). split; reflexivity.
        * exists (Some p). split; [reflexivity | apply ord_lt_le, (index_lt ω n)].
        * exists (Some q). split; [apply ord_lt_le, (index_lt ω n) | reflexivity].
        * exists None. split; reflexivity.
      + left. exact (inhabits None).
      + intros [p|]; [apply omega_complete | apply natOrdSize_complete]. }
  assert (HA : a ⊕ a ≤ rk [(a, succOrd 1)]).
  { rewrite <- nmul_rk.
    apply ord_le_trans with (nmulOrd a 1 ⊕ a); [|apply SL; auto with ord].
    apply naddOrd_monotone; [apply nmulOrd_one | reflexivity]. }
  (* finite ranks refute P *)
  assert (HfinP : forall x, x < ω -> c 0%nat ≤ x -> ~P).
  { intros x Hx H p. apply (ord_lt_irreflexive ω).
    apply ord_lt_le_trans with (c 0%nat); auto. rewrite H. apply ord_lt_le; auto. }
  (* the opponent plays c 0 in the first copy of a *)
  assert (Hz1 : c 0%nat ⊕ a < rk [(a, succOrd 1)]).
  { apply ord_lt_le_trans with (a ⊕ a); auto. apply naddOrd_increasing1; auto. }
  destruct (rk_lt_elim _ _ Hz1) as [m Hm].
  destruct m as [[n t]|[]].
  change (mvpt [(a, succOrd 1)] (inl (n, t))) with (c n, natOrdSize 1) in Hm.
  set (R1 := [(c n, succOrd 1); (a, 1)]).
  assert (HR1 : rk (cut (c n, natOrdSize 1) [(a, succOrd 1)]) ≤ rk R1).
  { apply rk_mono. rewrite cut_cons.
    apply rsub_cons.
    { apply rsub_in with (c n, succOrd 1); simpl; auto.
      split; simpl; [apply glb_le2 | reflexivity]. }
    apply rsub_cons; [|apply rsub_nil].
    apply rsub_in with (a, 1); simpl; auto.
    split; simpl; [reflexivity | apply glb_le2]. }
  (* then c (S n) in the second copy, beyond the answer's column *)
  assert (Hz2 : c 0%nat ⊕ c (S n) < rk R1).
  { rewrite <- HR1. apply ord_lt_le_trans with (c 0%nat ⊕ a); auto.
    apply naddOrd_increasing2; auto. }
  destruct (rk_lt_elim _ _ Hz2) as [m2 Hm2].
  destruct m2 as [[o y]|[[j y]|[]]].
  - destruct o as [p|].
    + (* a move into a P-indexed child proves P *)
      left. intro np. exact (np p).
    + (* the top row shrinks to n: reaches only a ⊕ n *)
      change (mvpt R1 (inl (None, y))) with (natOrdSize n, natOrdSize 1) in Hm2.
      right. intro p.
      assert (H : c 0%nat ⊕ c (S n) ≤ a ⊕ natOrdSize n).
      { rewrite Hm2.
        apply ord_le_trans with (rk ((natOrdSize n, succOrd 1) :: [(a, 1)])).
        - apply rk_mono. unfold R1. rewrite !cut_cons.
          intros r Hr. simpl in Hr.
          destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r; right.
          + exists (natOrdSize n, succOrd 1). simpl; split; auto.
            split; simpl; [apply glb_le2 | reflexivity].
          + exists (a, 1). simpl; split; auto.
            split; simpl; [apply ord_lt_le; auto | apply glb_le2].
          + exists (a, 1). simpl; split; auto.
            split; simpl; [apply glb_le1 | reflexivity].
          + exists (a, 1). simpl; split; auto.
            split; simpl; [reflexivity | apply glb_le1].
        - rewrite (rk_row_upper (natOrdSize n) 1 [(a, 1)]).
          + rewrite rk_one. reflexivity.
          + apply rsub_in with (a, 1); simpl; auto.
            split; simpl; [|reflexivity].
            apply ord_lt_le, ord_lt_trans with (c n); auto.
          + intros r [Hr|[]]; subst r. reflexivity. }
      (* under P, a ≤ c (S n) + 1, so c 0 ≤ n + 1 < ω *)
      assert (Ha : a ≤ succOrd (c (S n))).
      { rewrite ord_le_unfold. intro i. simpl.
        apply ord_le_lt_trans with (c (S n)); [apply HcP; auto | apply succ_lt]. }
      apply (HfinP (natOrdSize (S n))); auto; [apply (index_lt ω (S n))|].
      apply (naddOrd_cancel_le _ _ (c (S n))).
      apply ord_le_trans with (a ⊕ natOrdSize n); auto.
      apply ord_le_trans with (succOrd (c (S n)) ⊕ natOrdSize n).
      { apply naddOrd_monotone; auto. reflexivity. }
      change (natOrdSize (S n)) with (succOrd (natOrdSize n)).
      rewrite !naddOrd_succ. apply succ_monotone.
      rewrite naddOrd_comm. reflexivity.
  - (* an answer at (c j, 0) in the bottom row cuts the top row too *)
    change (mvpt R1 (inr (inl (j, y)))) with (c j, natOrdSize 0) in Hm2.
    set (R2 := [(c n, succOrd 1); (c j, 1)]).
    assert (HR2 : rk (cut (c j, natOrdSize 0) R1) ≤ rk R2).
    { apply rk_mono. unfold R1. rewrite !cut_cons.
      intros r Hr. simpl in Hr.
      destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r.
      - right. exists (c n, succOrd 1). simpl; split; auto.
        split; simpl; [apply glb_le1 | reflexivity].
      - left. right. simpl. rewrite glb_le2. reflexivity.
      - right. exists (c j, 1). simpl; split; auto.
        split; simpl; [apply glb_le2 | reflexivity].
      - left. right. simpl. rewrite glb_le2. reflexivity. }
    (* the opponent descends to n+1 inside c (S n) *)
    assert (Hz3 : c 0%nat ⊕ natOrdSize (S n) < rk R2).
    { rewrite <- HR2, <- Hm2. apply naddOrd_increasing2; auto. }
    destruct (rk_lt_elim _ _ Hz3) as [m3 Hm3].
    destruct m3 as [[o y']|[[o y']|[]]].
    + destruct o as [p|].
      * left. intro np. exact (np p).
      * (* top row to n: reaches only c 0 ⊕ n, under P *)
        change (mvpt R2 (inl (None, y'))) with (natOrdSize n, natOrdSize 1) in Hm3.
        right. intro p.
        apply (ord_lt_irreflexive (natOrdSize n)).
        apply ord_lt_le_trans with (natOrdSize (S n)); [apply succ_lt|].
        apply (naddOrd_cancel_le _ _ (c 0%nat)).
        rewrite !(naddOrd_comm _ (c 0%nat)).
        rewrite Hm3.
        apply ord_le_trans with (rk ((natOrdSize n, succOrd 1) :: [(c 0%nat, 1)])).
        -- apply rk_mono. unfold R2. rewrite !cut_cons.
           intros r Hr. simpl in Hr.
           destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r; right.
           ++ exists (natOrdSize n, succOrd 1). simpl; split; auto.
              split; simpl; [apply glb_le2 | reflexivity].
           ++ exists (c 0%nat, 1). simpl; split; auto.
              split; simpl; [apply HcP; auto | apply glb_le2].
           ++ exists (c 0%nat, 1). simpl; split; auto.
              split; simpl; [rewrite glb_le1; apply HcP; auto | reflexivity].
           ++ exists (c 0%nat, 1). simpl; split; auto.
              split; simpl; [apply HcP; auto | apply glb_le1].
        -- rewrite (rk_row_upper (natOrdSize n) 1 [(c 0%nat, 1)]).
           ++ rewrite rk_one. reflexivity.
           ++ apply rsub_in with (c 0%nat, 1); simpl; auto.
              split; simpl; [|reflexivity].
              apply ord_lt_le, ord_lt_le_trans with (c n); auto.
           ++ intros r [Hr|[]]; subst r. reflexivity.
    + destruct o as [p|].
      * left. intro np. exact (np p).
      * (* bottom row to j: everything left is finite *)
        change (mvpt R2 (inr (inl (None, y')))) with (natOrdSize j, natOrdSize 0) in Hm3.
        right.
        apply (HfinP (natOrdSize j ⊕ natOrdSize j));
          [apply below_omega_double, (index_lt ω j)|].
        rewrite (naddOrd_le1 (c 0%nat) (natOrdSize (S n))), Hm3.
        rewrite <- rk_two.
        apply rk_mono. unfold R2. rewrite !cut_cons.
        intros r Hr. simpl in Hr.
        destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r.
        -- right. exists (natOrdSize j, succOrd 1). simpl; split; auto.
           split; simpl; [apply glb_le2 | reflexivity].
        -- left. right. simpl. rewrite glb_le2. reflexivity.
        -- right. exists (natOrdSize j, succOrd 1). simpl; split; auto.
           split; simpl; [apply glb_le2 | apply ord_lt_le, succ_lt].
        -- left. right. simpl. rewrite glb_le2. reflexivity.
Qed.

(** Superdistributivity contains the successor law (take [c = 1]). *)
Corollary distrib_lower_WEM :
  (forall a b c, nmulOrd a b ⊕ nmulOrd a c ≤ nmulOrd a (b ⊕ c)) ->
  weak_excluded_middle.
Proof.
  intro H. apply succ_lower_WEM. intros a b.
  apply ord_le_trans with (nmulOrd a b ⊕ nmulOrd a 1).
  - apply naddOrd_monotone; [reflexivity | apply nmulOrd_one].
  - rewrite H. apply nmulOrd_monotone; [reflexivity|].
    rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
Qed.

Corollary distrib_lower_complete_WEM :
  (forall a b c, complete a -> complete b -> complete c ->
     nmulOrd a b ⊕ nmulOrd a c ≤ nmulOrd a (b ⊕ c)) ->
  weak_excluded_middle.
Proof.
  intro H. apply succ_lower_complete_WEM. intros a b Ha Hb.
  apply ord_le_trans with (nmulOrd a b ⊕ nmulOrd a 1).
  - apply naddOrd_monotone; [reflexivity | apply nmulOrd_one].
  - rewrite H; auto with ord. apply nmulOrd_monotone; [reflexivity|].
    rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
Qed.
