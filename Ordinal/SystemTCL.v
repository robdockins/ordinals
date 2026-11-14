From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Wellfounded.
Import ListNotations.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import Notation.VNotation.
From Ordinal Require Notation.CantorProduct.

(** * Strong normalization of combinatory System T below ε₀

    Gödel's T in combinatory form, with the ordinal assignment of Howard
    and Schütte: each term gets a vector of ordinals below ε₀, indexed by
    type levels, and every reduction step decreases it. *)

Open Scope ord_scope.

(** ** Ordinals: normal V forms

    The vectors hold normal V forms ([VNotation]), with the natural sum
    [⊕], the natural product [⊗] and [ω^x], computed on normal forms.  On
    notations these satisfy the usual laws constructively
    ([CantorProduct]). *)

Record ON : Set := mkON { onv : VForm ; onn : VF_normal onv }.

Definition ON_denote (x:ON) : Ord := VF_denote (onv x).

Canonical Structure ONo := ord ON ON_denote.

Lemma ON_complete (x:ON) : complete (sz x).
Proof. apply VF_complete. Qed.

Local Hint Resolve ON_complete : core.

Lemma ON_below_ε0 (x:ON) : sz x < ε 0.
Proof. apply VNotation_below_ε₀. Qed.

Lemma nadd_ok a b : VF_normal a -> VF_normal b ->
  VF_denote (VF_nadd a b) ≈ VF_denote a ⊕ VF_denote b /\ VF_normal (VF_nadd a b).
Proof.
  intros Ha Hb. destruct (VF_reflects_nadd (VF_denote a) a (conj (ord_eq_refl _) Ha)
                                         (VF_denote b) b (conj (ord_eq_refl _) Hb)) as [H1 H2].
  split; [symmetry; exact H1 | exact H2].
Qed.

Lemma nmul_ok a b : VF_normal a -> VF_normal b ->
  VF_denote (VF_nmul a b) ≈ NaturalProduct.nmulOrd (VF_denote a) (VF_denote b) /\ VF_normal (VF_nmul a b).
Proof.
  intros Ha Hb. destruct (VF_reflects_nmul (VF_denote a) a (conj (ord_eq_refl _) Ha)
                                         (VF_denote b) b (conj (ord_eq_refl _) Hb)) as [H1 H2].
  split; [symmetry; exact H1 | exact H2].
Qed.

Definition oadd (x y:ON) : ON :=
  mkON (VF_nadd (onv x) (onv y)) (proj2 (nadd_ok _ _ (onn x) (onn y))).
Definition omul (x y:ON) : ON :=
  mkON (VF_nmul (onv x) (onv y)) (proj2 (nmul_ok _ _ (onn x) (onn y))).
Definition oexp (x:ON) : ON := mkON (V (onv x) Z) (conj (onn x) (conj I I)).
Definition ozero : ON := mkON Z I.
Definition oone : ON := oexp ozero.
Fixpoint onat (n:nat) : ON := match n with O => ozero | S n => oadd (onat n) oone end.
Definition oomega : ON := oexp oone.

Infix "⊕'" := oadd (at level 45, right associativity).
Infix "⊗'" := omul (at level 35, right associativity).

Local Abbreviation nmul := NaturalProduct.nmulOrd.

#[local] Instance nmul_le_mor : Proper (ord_le ==> ord_le ==> ord_le) NaturalProduct.nmulOrd.
Proof. intros x y H a b H'. apply NaturalProduct.nmulOrd_monotone; auto. Qed.

#[local] Instance nmul_eq_mor : Proper (ord_eq ==> ord_eq ==> ord_eq) NaturalProduct.nmulOrd.
Proof. intros x y [] a b []. split; apply NaturalProduct.nmulOrd_monotone; auto. Qed.

Lemma oadd_eq x y : sz (x ⊕' y) ≈ sz x ⊕ sz y.
Proof. apply (nadd_ok _ _ (onn x) (onn y)). Qed.

Lemma omul_eq x y : sz (x ⊗' y) ≈ nmul (sz x) (sz y).
Proof. apply (nmul_ok _ _ (onn x) (onn y)). Qed.

Lemma oexp_eq x : sz (oexp x) ≈ expOrd ω (sz x).
Proof. unfold sz; simpl. unfold ON_denote; simpl. rewrite veblen_onePlus; [apply addOrd_zero_r | apply VF_complete | apply zero_complete]. Qed.

Lemma ozero_eq : sz ozero ≈ 0.
Proof. reflexivity. Qed.

Lemma oone_eq : sz oone ≈ 1.
Proof. unfold oone. rewrite oexp_eq, ozero_eq. apply expOrd_zero. Qed.

Lemma onat_eq n : sz (onat n) ≈ natOrdSize n.
Proof.
  induction n as [|n IH]; simpl onat; [reflexivity|].
  rewrite oadd_eq, IH, oone_eq. simpl natOrdSize.
  rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
Qed.

Lemma oomega_eq : sz oomega ≈ ω.
Proof.
  unfold oomega. rewrite oexp_eq, oone_eq. apply expOrd_one'. apply omega_gt0.
Qed.

(** The laws of the natural product, on notations. *)

Lemma omul_comm x y : sz (x ⊗' y) ≈ sz (y ⊗' x).
Proof. apply CantorProduct.cantor_nmul_comm; apply onn. Qed.

Lemma omul_assoc x y z : sz ((x ⊗' y) ⊗' z) ≈ sz (x ⊗' (y ⊗' z)).
Proof. apply CantorProduct.cantor_nmul_assoc; apply onn. Qed.

Lemma omul_distr x y z : sz (x ⊗' (y ⊕' z)) ≈ sz (x ⊗' y) ⊕ sz (x ⊗' z).
Proof.
  unfold sz; simpl; unfold ON_denote; simpl.
  rewrite (CantorProduct.cantor_nmul_nadd_r _ _ _ VF_has_cantor_decomposition); try apply onn.
  apply (nadd_ok _ _ (onn (x ⊗' y)) (onn (x ⊗' z))).
Qed.

Lemma oexp_mul a b : sz (oexp a ⊗' oexp b) ≈ sz (oexp (a ⊕' b)).
Proof. apply (CantorProduct.cantor_nmul_exp _ _ _ VF_has_cantor_decomposition); apply onn. Qed.

(** ** Powers of ω times an ordinal

    [wm w y] is [ω^w ⊗ y].  These are the only products the assignment
    uses. *)

Definition wm (w y:ON) : ON := oexp w ⊗' y.

Lemma wm_eq w y : sz (wm w y) ≈ nmul (expOrd ω (sz w)) (sz y).
Proof. unfold wm. rewrite omul_eq, oexp_eq. reflexivity. Qed.

Lemma oadd_mono (x x' y y':ON) : x ⊴ x' -> y ⊴ y' -> x ⊕' y ⊴ x' ⊕' y'.
Proof. intros. rewrite !oadd_eq. apply naddOrd_monotone; auto. Qed.

Lemma oadd_le1 (x y:ON) : x ⊴ x ⊕' y.
Proof. rewrite oadd_eq. apply naddOrd_le1. Qed.

Lemma oadd_le2 (x y:ON) : y ⊴ x ⊕' y.
Proof. rewrite oadd_eq. apply naddOrd_le2. Qed.

Lemma oadd_lt1 (x y:ON) : 0 < sz y -> x ◃ x ⊕' y.
Proof.
  intro H. rewrite oadd_eq. rewrite <- (naddOrd_zero_r (sz x)) at 1.
  apply naddOrd_increasing2. exact H.
Qed.

Lemma oadd_lt2 (x y:ON) : 0 < sz x -> y ◃ x ⊕' y.
Proof.
  intro H. rewrite oadd_eq. rewrite <- (naddOrd_zero_l (sz y)) at 1.
  apply naddOrd_increasing1. exact H.
Qed.

Lemma oadd_pos1 (x y:ON) : 0 < sz x -> 0 < sz (x ⊕' y).
Proof. intro H. eapply ord_lt_le_trans; [exact H | apply oadd_le1]. Qed.

Lemma oexp_mono (x y:ON) : x ⊴ y -> oexp x ⊴ oexp y.
Proof. intro H. rewrite !oexp_eq. apply expOrd_monotone. exact H. Qed.

Lemma oexp_increasing (x y:ON) : x ◃ y -> oexp x ◃ oexp y.
Proof. intro H. rewrite !oexp_eq. apply expOrd_increasing; [apply omega_gt1 | exact H]. Qed.

Lemma oexp_pos (x:ON) : 0 < sz (oexp x).
Proof. rewrite oexp_eq. apply expOrd_nonzero. Qed.

Lemma oexp_ge (x:ON) : x ⊴ oexp x.
Proof. rewrite oexp_eq. apply CantorProduct.le_expOmega. Qed.

(** [ω^c] is closed under the natural sum. *)
Lemma below_oexp (c:ON) (x y:Ord) :
  x < sz (oexp c) -> y < sz (oexp c) -> x ⊕ y < sz (oexp c).
Proof. rewrite !oexp_eq. apply nadd_closed_con. apply ON_complete. Qed.

Lemma wm_mono (w w' y y':ON) : w ⊴ w' -> y ⊴ y' -> wm w y ⊴ wm w' y'.
Proof.
  intros Hw Hy. rewrite !wm_eq. apply NaturalProduct.nmulOrd_monotone; auto.
  apply expOrd_monotone. exact Hw.
Qed.

Lemma wm_increasing (w y y':ON) : y ◃ y' -> wm w y ◃ wm w y'.
Proof.
  intros Hy. rewrite !wm_eq. apply NaturalProduct.nmulOrd_increasing2; auto.
  apply expOrd_nonzero.
Qed.

Lemma wm_ge (w y:ON) : y ⊴ wm w y.
Proof.
  rewrite wm_eq. rewrite <- (NaturalProduct.nmulOrd_one (sz y)) at 1.
  rewrite NaturalProduct.nmulOrd_comm. apply NaturalProduct.nmulOrd_monotone; [|reflexivity].
  apply succ_least. apply expOrd_nonzero.
Qed.

Lemma wm_pos (w y:ON) : 0 < sz y -> 0 < sz (wm w y).
Proof. intro H. eapply ord_lt_le_trans; [exact H | apply wm_ge]. Qed.

Lemma wm_ge_exp (w y:ON) : 0 < sz y -> oexp w ⊴ wm w y.
Proof.
  intro H. rewrite wm_eq, oexp_eq. rewrite <- (NaturalProduct.nmulOrd_one (expOrd ω (sz w))) at 1.
  apply NaturalProduct.nmulOrd_monotone; [reflexivity|]. apply succ_least. exact H.
Qed.

Lemma wm_add (w y z:ON) : sz (wm w (y ⊕' z)) ≈ sz (wm w y) ⊕ sz (wm w z).
Proof. apply omul_distr. Qed.

Lemma wm_wm (a b y:ON) : sz (wm a (wm b y)) ≈ sz (wm (a ⊕' b) y).
Proof.
  unfold wm. rewrite <- omul_assoc. rewrite !omul_eq.
  rewrite <- (omul_eq (oexp a) (oexp b)). rewrite oexp_mul. reflexivity.
Qed.

Lemma wm_oexp (a b:ON) : sz (wm a (oexp b)) ≈ sz (oexp (a ⊕' b)).
Proof. apply oexp_mul. Qed.

Lemma wm_zero (y:ON) : sz (wm ozero y) ≈ sz y.
Proof.
  rewrite wm_eq, ozero_eq, expOrd_zero, NaturalProduct.nmulOrd_comm.
  apply NaturalProduct.nmulOrd_one.
Qed.

(** *** Absorption

    A finite natural sum of ordinals below [ω^E ⊗ y] is below
    [ω^L ⊗ y], when [E < L] and [y > 0]: [ω^L ⊗ y ≥ ω^E ⊗ (ω ⊗ y)]. *)

Fixpoint sumO (us:list Ord) : Ord :=
  match us with [] => 0 | u :: us => u ⊕ sumO us end.

Fixpoint orep (k:nat) (y:ON) : ON :=
  match k with O => ozero | S k => orep k y ⊕' y end.

Lemma wm_orep k w y : sz (wm w (orep k y)) ≈ NaturalProduct.nrep k (sz (wm w y)).
Proof.
  induction k as [|k IH]; simpl orep; simpl NaturalProduct.nrep.
  - rewrite wm_eq, ozero_eq. apply NaturalProduct.nmulOrd_zero.
  - rewrite wm_add, IH. reflexivity.
Qed.

Lemma orep_eq k (y:ON) : sz (orep k y) ≈ nmul (natOrdSize k) (sz y).
Proof.
  induction k as [|k IH]; simpl orep.
  - rewrite ozero_eq, NaturalProduct.nmulOrd_comm. symmetry. apply NaturalProduct.nmulOrd_zero.
  - rewrite oadd_eq, IH. rewrite <- (onat_eq (S k)), <- (onat_eq k).
    rewrite !(NaturalProduct.nmulOrd_comm _ (sz y)). rewrite <- !omul_eq.
    change (onat (S k)) with (onat k ⊕' oone).
    rewrite omul_distr, (omul_eq y oone), oone_eq, NaturalProduct.nmulOrd_one. reflexivity.
Qed.

Lemma orep_below_omega k (y:ON) : 0 < sz y -> orep k y ◃ oomega ⊗' y.
Proof.
  intro Hy. rewrite orep_eq, omul_eq, oomega_eq.
  apply NaturalProduct.nmulOrd_increasing1; auto. apply index_lt.
Qed.

Lemma absorb (E L y:ON) (us:list Ord) :
  0 < sz y -> E ◃ L -> Forall (fun u => u ≤ sz (wm E y)) us -> sumO us < sz (wm L y).
Proof.
  intros Hy HEL Hus.
  apply ord_le_lt_trans with (NaturalProduct.nrep (length us) (sz (wm E y))).
  { clear -Hus. induction Hus as [|u us Hu _ IH]; simpl; [reflexivity|].
    rewrite (naddOrd_comm (NaturalProduct.nrep _ _)). apply naddOrd_monotone; auto. }
  rewrite <- wm_orep.
  eapply ord_lt_le_trans; [apply wm_increasing, orep_below_omega, Hy|].
  unfold oomega. fold (wm oone y). rewrite wm_wm.
  apply wm_mono; [|reflexivity].
  rewrite oadd_eq, oone_eq. rewrite naddOrd_succ2, naddOrd_zero_r. apply succ_least. exact HEL.
Qed.

(** From here on the operations are used only through their laws; keeping
    them opaque stops unification from computing with V forms. *)
#[local] Opaque ON_denote oadd omul oexp wm onat ozero oone oomega.

Lemma oadd_lt_mono (x x' y y':ON) : x' ◃ x -> y' ⊴ y -> x' ⊕' y' ◃ x ⊕' y.
Proof. intros. rewrite !oadd_eq. apply (proj1 (naddOrd_increasing_both _ _ _ _)); auto. Qed.

Lemma oadd_lt_mono2 (x x' y y':ON) : x' ⊴ x -> y' ◃ y -> x' ⊕' y' ◃ x ⊕' y.
Proof. intros. rewrite !oadd_eq. apply (proj2 (naddOrd_increasing_both _ _ _ _)); auto. Qed.

(** ** Vectors and Howard's operation

    A vector assigns an ordinal to each type level.  Applying a function
    with vector [f] to an argument of level [n] with vector [g] gives
    [box n f g]: above [n] the vector of the function, and at level
    [i ≤ n] the value [ω^(box n f g (i+1)) ⊗ (f i ⊕ g i)].  Each level
    exponentiates the one above it, as cut elimination does. *)

Definition vec := nat -> ON.

Fixpoint boxd (f g:vec) (i d:nat) : ON :=
  match d with
  | O => wm (f (S i)) (f i ⊕' g i)
  | S d => wm (boxd f g (S i) d) (f i ⊕' g i)
  end.

Definition box (n:nat) (f g:vec) : vec :=
  fun i => if i <=? n then boxd f g i (n - i) else f i.

Lemma box_hi n f g i : (n < i)%nat -> box n f g i = f i.
Proof. intro H. unfold box. destruct (Nat.leb_spec i n); [lia | reflexivity]. Qed.

Lemma box_lo n f g i : (i <= n)%nat -> box n f g i = wm (box n f g (S i)) (f i ⊕' g i).
Proof.
  intro H. unfold box. rewrite (proj2 (Nat.leb_le i n) H).
  remember (n - i)%nat as d. destruct d as [|d]; cbn [boxd].
  - rewrite (proj2 (Nat.leb_gt (S i) n)) by lia. reflexivity.
  - rewrite (proj2 (Nat.leb_le (S i) n)) by lia. replace (n - S i)%nat with d by lia. reflexivity.
Qed.

(** Downward induction on levels. *)
Lemma down_ind (P:nat -> Prop) (m:nat) :
  (forall i, (i <= m)%nat -> (forall j, (i < j)%nat -> (j <= m)%nat -> P j) -> P i) ->
  forall i, (i <= m)%nat -> P i.
Proof.
  intros H i Hi. remember (m - i)%nat as d. revert i Hi Heqd.
  induction d as [d IH] using lt_wf_ind. intros i Hi Hd.
  apply H; auto. intros j Hij Hjm. apply (IH (m - j)%nat); auto; lia.
Qed.

Lemma box_ge_f n f g i : f i ⊴ box n f g i.
Proof.
  destruct (le_lt_dec i n).
  - rewrite box_lo by auto. eapply ord_le_trans; [apply oadd_le1 | apply wm_ge].
  - rewrite box_hi by auto. reflexivity.
Qed.

Lemma box_ge_sum n f g i : (i <= n)%nat -> f i ⊕' g i ⊴ box n f g i.
Proof. intro H. rewrite box_lo by auto. apply wm_ge. Qed.

Lemma box_pos n f g : (forall j, 0 < sz (f j)) -> forall i, 0 < sz (box n f g i).
Proof. intros Hf i. eapply ord_lt_le_trans; [apply Hf | apply box_ge_f]. Qed.

Lemma box_mono m n f f' g g' : (n < m)%nat ->
  (forall j, (j <= m)%nat -> f' j ⊴ f j) -> (forall j, (j <= n)%nat -> g' j ⊴ g j) ->
  forall i, (i <= m)%nat -> box n f' g' i ⊴ box n f g i.
Proof.
  intros Hnm Hf Hg. apply down_ind. intros i Hi IH.
  destruct (le_lt_dec i n).
  - rewrite (box_lo n f' g' i), (box_lo n f g i) by auto. apply wm_mono; [apply IH; lia|].
    apply oadd_mono; auto.
  - rewrite (box_hi n f' g' i), (box_hi n f g i) by auto. auto.
Qed.

Lemma box_mono_all n f f' g g' :
  (forall j, f' j ⊴ f j) -> (forall j, g' j ⊴ g j) -> forall i, box n f' g' i ⊴ box n f g i.
Proof.
  intros Hf Hg i. apply box_mono with (m := Nat.max i (S n)); auto; lia.
Qed.

Lemma box_lt0 m n (f f' g g':vec) : (n < m)%nat ->
  (forall j, (j <= m)%nat -> f' j ⊴ f j) -> (forall j, (j <= n)%nat -> g' j ⊴ g j) ->
  (f' 0%nat ◃ f 0%nat \/ g' 0%nat ◃ g 0%nat) -> box n f' g' 0%nat ◃ box n f g 0%nat.
Proof.
  intros Hnm Hf Hg H0. rewrite (box_lo n f' g' 0%nat), (box_lo n f g 0%nat) by lia.
  eapply ord_le_lt_trans; [apply wm_mono; [apply (box_mono m n f f' g g'); auto; lia | reflexivity]|].
  apply wm_increasing. destruct H0 as [H0|H0].
  - apply oadd_lt_mono; auto. apply Hg; lia.
  - apply oadd_lt_mono2; auto. apply Hf; lia.
Qed.

Lemma box_ext n f f' g g' i0 :
  (forall j, (i0 <= j)%nat -> (j <= S n)%nat -> f j = f' j) ->
  (forall j, (i0 <= j)%nat -> (j <= n)%nat -> g j = g' j) ->
  forall i, (i0 <= i)%nat -> (i <= S n)%nat -> box n f g i = box n f' g' i.
Proof.
  intros Hf Hg i Hi0 Hi. revert Hi0.
  apply (down_ind (fun i => (i0 <= i)%nat -> box n f g i = box n f' g' i) (S n)); auto.
  intros k Hk IH Hk0. destruct (le_lt_dec k n).
  - rewrite (box_lo n f g k), (box_lo n f' g' k) by auto. rewrite IH by lia. rewrite Hf, Hg by lia. reflexivity.
  - rewrite (box_hi n f g k), (box_hi n f' g' k) by auto. apply Hf; lia.
Qed.

Lemma sumO3 a b c : sumO [a; b; c] ≈ a ⊕ b ⊕ c.
Proof. simpl. rewrite naddOrd_zero_r. reflexivity. Qed.

Lemma le_sumO3 a b c : a ≤ sumO [a; b; c].
Proof. simpl. apply naddOrd_le1. Qed.

(** Regrouping sums, stated once for abstract ordinals: rewriting inside
    the large goals below is very slow. *)
Lemma split_head u a b us : u ≤ a ⊕ b -> sumO (u :: us) ≤ sumO (a :: b :: us).
Proof.
  intro H. cbn [sumO]. rewrite naddOrd_assoc. apply naddOrd_monotone; [exact H | reflexivity].
Qed.

Lemma le_sumO4 a b c d : a ⊕ b ⊕ c ⊕ d ≤ sumO [a; b; c; d].
Proof. cbn [sumO]. rewrite naddOrd_zero_r. reflexivity. Qed.

Lemma split_sum3 u a b c : u ≤ (a ⊕ b) ⊕ c -> u ≤ sumO [a; b; c].
Proof. intro H. cbn [sumO]. rewrite naddOrd_zero_r, naddOrd_assoc. exact H. Qed.

(** ** The key inequalities

    The combinator [S]: [S a b d] at levels [p, q, r] (the levels of the
    types of [a], [b], [d]) has a larger vector than [a d (b d)], whose
    middle application is at level [s], at every level up to [t].  This
    is Howard's lemma: above [r] the vector of [S a b] dominates that of
    [a b] with room to spare, and below [r] the duplicated [d] is paid
    for by one extra power of ω at each level. *)

Lemma S_decrease (p q r s t:nat) (Sv A B D:vec) :
  (forall j, 0 < sz (Sv j)) -> (forall j, 0 < sz (A j)) -> (forall j, 0 < sz (B j)) ->
  (forall j, 0 < sz (D j)) ->
  (r < p)%nat -> (r < q)%nat -> (s <= q)%nat -> (s < p)%nat -> (t <= p)%nat ->
  forall i, (i <= t)%nat ->
    box s (box r A D) (box r B D) i ◃ box r (box q (box p Sv A) B) D i.
Proof.
  intros HS HA HB HD H1 H2 H3 H4 H5.
  set (Sa := box p Sv A). set (c := box q Sa B). set (X := box r A D). set (Y := box r B D).
  set (Rb := box s A B).
  assert (HSa : forall j, 0 < sz (Sa j)) by (apply box_pos; auto).
  assert (Hc : forall j, 0 < sz (c j)) by (apply box_pos; auto).
  assert (HRb : forall i, (r < i)%nat -> box s X Y i = Rb i).
  { intros i Hi. destruct (le_lt_dec i (S s)) as [Hle|Hgt].
    - apply box_ext with (i0 := S r); auto; intros j Hj _; unfold X, Y; apply box_hi; lia.
    - unfold Rb. rewrite (box_hi s X Y i), (box_hi s A B i) by lia. unfold X. apply box_hi; lia. }
  (* Above [r]: [S a b] against [a b]. *)
  assert (Hup : forall i, (i <= p)%nat -> (S r <= i)%nat ->
            ((i <= q)%nat -> sumO [sz (Rb i); sz (A i); sz (B i)] < sz (c i)) /\ Rb i ◃ c i).
  { apply (down_ind (fun i => (S r <= i)%nat ->
             ((i <= q)%nat -> sumO [sz (Rb i); sz (A i); sz (B i)] < sz (c i)) /\ Rb i ◃ c i) p).
    intros i Hip IH Hri.
    destruct (le_lt_dec i q) as [Hiq|Hiq].
    - assert (Hci : c i = wm (c (S i)) (Sa i ⊕' B i)) by (apply box_lo; auto).
      assert (HSai : Sv i ⊕' A i ⊴ Sa i) by (apply box_ge_sum; lia).
      assert (HAy : A i ◃ Sa i ⊕' B i).
      { eapply ord_lt_le_trans; [apply oadd_lt2, HS|].
        eapply ord_le_trans; [exact HSai | apply oadd_le1]. }
      assert (HBy : B i ⊴ Sa i ⊕' B i) by apply oadd_le2.
      assert (Hy : 0 < sz (Sa i ⊕' B i)) by (apply oadd_pos1; auto).
      assert (Hfirst : sumO [sz (Rb i); sz (A i); sz (B i)] < sz (c i)).
      { rewrite Hci. destruct (le_lt_dec i s) as [His|His].
        - assert (HR : Rb i = wm (Rb (S i)) (A i ⊕' B i)) by (apply box_lo; auto).
          assert (IH1 : Rb (S i) ◃ c (S i)) by (apply (IH (S i)); lia).
          apply absorb with (E := Rb (S i)); auto.
          repeat constructor.
          + rewrite HR. apply wm_mono; [reflexivity|]. apply oadd_mono; [|reflexivity].
            apply ord_lt_le. eapply ord_lt_le_trans; [apply oadd_lt2, HS | exact HSai].
          + eapply ord_le_trans; [apply ord_lt_le, HAy | apply wm_ge].
          + eapply ord_le_trans; [exact HBy | apply wm_ge].
        - assert (HR : Rb i = A i) by (apply box_hi; auto). rewrite HR.
          apply absorb with (E := ozero); auto.
          repeat constructor; rewrite wm_zero; auto using ord_lt_le. }
      split; [intros _; exact Hfirst|].
      eapply ord_le_lt_trans; [apply le_sumO3 | exact Hfirst].
    - split; [intro; lia|].
      unfold c. rewrite box_hi by auto. unfold Rb. rewrite box_hi by lia.
      eapply ord_lt_le_trans; [apply oadd_lt2, HS | apply box_ge_sum; auto]. }
  (* Below [r]: the duplicated argument. *)
  assert (Hlow : forall i, (i <= S r)%nat ->
            sumO [sz (box s X Y i); sz (X i); sz (Y i)] < sz (box r c D i)).
  { apply down_ind. intros i Hi IH.
    destruct (Nat.eq_dec i (S r)) as [->|Hne].
    - rewrite HRb by lia. unfold X, Y. rewrite (box_hi r A D (S r)), (box_hi r B D (S r)), (box_hi r c D (S r)) by lia.
      apply Hup; lia.
    - assert (Hir : (i <= r)%nat) by lia.
      set (E := box s X Y (S i) ⊕' (X (S i) ⊕' Y (S i))).
      assert (HE : E ◃ box r c D (S i)).
      { unfold E. rewrite !oadd_eq. rewrite <- (naddOrd_zero_r (sz (Y (S i)))). apply (IH (S i)); lia. }
      assert (HAc : A i ⊴ c i).
      { eapply ord_le_trans; [|apply (box_ge_sum q Sa B i); lia].
        eapply ord_le_trans; [|apply oadd_le1].
        eapply ord_le_trans; [|apply (box_ge_sum p Sv A i); lia]. apply oadd_le2. }
      assert (HBc : B i ⊴ c i).
      { eapply ord_le_trans; [|apply (box_ge_sum q Sa B i); lia]. apply oadd_le2. }
      set (y := c i ⊕' D i).
      assert (Hy : 0 < sz y) by (apply oadd_pos1; auto).
      assert (HXi : X i = wm (X (S i)) (A i ⊕' D i)) by (apply box_lo; auto).
      assert (HYi : Y i = wm (Y (S i)) (B i ⊕' D i)) by (apply box_lo; auto).
      assert (HX : X i ⊴ wm E y).
      { rewrite HXi. apply wm_mono; [|apply oadd_mono; auto; reflexivity].
        unfold E. eapply ord_le_trans; [|apply oadd_le2]. apply oadd_le1. }
      assert (HY : Y i ⊴ wm E y).
      { rewrite HYi. apply wm_mono; [|apply oadd_mono; auto; reflexivity].
        unfold E. eapply ord_le_trans; [|apply oadd_le2]. apply oadd_le2. }
      rewrite (box_lo r c D i) by auto.
      destruct (le_lt_dec i s) as [His|His].
      + rewrite (box_lo s X Y i) by auto.
        set (Rh := box s X Y (S i)).
        apply ord_le_lt_trans with (sumO [sz (wm Rh (X i)); sz (wm Rh (Y i)); sz (X i); sz (Y i)]).
        { apply split_head. rewrite wm_add. reflexivity. }
        apply absorb with (E := E); auto.
        repeat constructor; auto.
        * rewrite HXi, wm_wm. apply wm_mono; [|apply oadd_mono; auto; reflexivity].
          unfold E, Rh. apply oadd_mono; [reflexivity | apply oadd_le1].
        * rewrite HYi, wm_wm. apply wm_mono; [|apply oadd_mono; auto; reflexivity].
          unfold E, Rh. apply oadd_mono; [reflexivity | apply oadd_le2].
      + rewrite (box_hi s X Y i) by auto.
        apply absorb with (E := E); repeat constructor; auto. }
  intros i Hi. destruct (le_lt_dec i r).
  - eapply ord_le_lt_trans; [apply le_sumO3 | apply Hlow; lia].
  - rewrite HRb by lia. rewrite (box_hi r c D i) by lia. apply Hup; lia.
Qed.

(** The recursor.  [R n̄] at a type of level [k] has the vector [vspec k n]:
    [n+1] at level [k+2], the level of the recursor, and [1] elsewhere;
    the unapplied recursor has [ω] there instead ([gen]). *)

Definition vspec (k n:nat) : vec := fun j => if j =? S (S k) then onat (S n) else oone.
Definition gen (k:nat) : vec := fun j => if j =? S (S k) then oomega else oone.

Lemma oone_pos : 0 < sz oone.
Proof. rewrite oone_eq. apply succ_lt. Qed.

Lemma onat_pos n : 0 < sz (onat (S n)).
Proof. rewrite onat_eq. apply (natOrdSize_increasing 0 (S n)). lia. Qed.

Lemma vspec_pos k n j : 0 < sz (vspec k n j).
Proof. unfold vspec. destruct (j =? S (S k)); auto using oone_pos, onat_pos. Qed.

Lemma gen_pos k j : 0 < sz (gen k j).
Proof.
  unfold gen. destruct (j =? S (S k)); auto using oone_pos.
  rewrite oomega_eq. apply omega_gt0.
Qed.

Lemma sumO4 a b c d : sumO [a; b; c; d] ≈ a ⊕ b ⊕ c ⊕ d.
Proof. cbn [sumO]. rewrite naddOrd_zero_r. reflexivity. Qed.

(** The recursion step [R (n+1) a b ↦ b n (R n a b)], at a type of level
    [k]: the vector of the redex is larger at every level up to [k].  The
    extra power of ω at level [k+1], from [n+2] against [n+1], pays for
    the extra application of [b]. *)
Lemma R_decrease (k n:nat) (A B Nv:vec) :
  (forall j, 0 < sz (A j)) -> (forall j, 0 < sz (B j)) ->
  Nv 0%nat ◃ oexp (onat (S n)) ->
  forall i, (i <= k)%nat ->
    box k (box 0 B Nv) (box (S k) (box k (vspec k n) A) B) i
      ◃ box (S k) (box k (vspec k (S n)) A) B i.
Proof.
  intros HA HB HN.
  set (P := box k (vspec k n) A). set (P' := box k (vspec k (S n)) A).
  set (W := box (S k) P B). set (L := box (S k) P' B). set (Bn := box 0 B Nv).
  set (Rh := box k Bn W).
  assert (HPP : forall j, (j <= S k)%nat -> P j = P' j).
  { intros j Hj. apply box_ext with (i0 := 0%nat); [| intros; reflexivity | lia | lia].
    intros j' _ Hj'. unfold vspec. rewrite (proj2 (Nat.eqb_neq j' (S (S k)))) by lia. reflexivity. }
  assert (HP : forall j, 0 < sz (P j)) by (apply box_pos, vspec_pos).
  assert (HW1 : W (S k) = wm (onat (S n)) (oone ⊕' B (S k))).
  { unfold W. rewrite box_lo by auto. unfold P. rewrite !box_hi by lia.
    unfold vspec. rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq (S k) (S (S k)))) by lia. reflexivity. }
  assert (HL1 : L (S k) = wm (onat (S (S n))) (oone ⊕' B (S k))).
  { unfold L. rewrite box_lo by auto. unfold P'. rewrite !box_hi by lia.
    unfold vspec. rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq (S k) (S (S k)))) by lia. reflexivity. }
  assert (Hup : forall i, (i <= S k)%nat -> (1 <= i)%nat ->
            sumO [sz (Rh i); sz (W i); sz (B i); sz (onat (S n))] < sz (L i)).
  { apply (down_ind (fun i => (1 <= i)%nat ->
             sumO [sz (Rh i); sz (W i); sz (B i); sz (onat (S n))] < sz (L i)) (S k)).
    intros i Hi IH H1i.
    destruct (Nat.eq_dec i (S k)) as [->|Hne].
    - assert (HR : Rh (S k) = B (S k)).
      { unfold Rh. rewrite box_hi by lia. unfold Bn. apply box_hi; lia. }
      rewrite HR, HW1, HL1.
      assert (Hy : 0 < sz (oone ⊕' B (S k))) by (apply oadd_pos1, oone_pos).
      apply absorb with (E := onat (S n)); auto.
      + rewrite !onat_eq. apply natOrdSize_increasing. lia.
      + repeat constructor.
        * eapply ord_le_trans; [apply oadd_le2 | apply wm_ge].
        * reflexivity.
        * eapply ord_le_trans; [apply oadd_le2 | apply wm_ge].
        * eapply ord_le_trans; [apply oexp_ge | apply wm_ge_exp; auto].
    - assert (Hik : (i <= k)%nat) by lia.
      set (y := P i ⊕' B i).
      assert (Hy : 0 < sz y) by (apply oadd_pos1; auto).
      set (E := Rh (S i) ⊕' (W (S i) ⊕' (B (S i) ⊕' onat (S n)))).
      assert (HE : E ◃ L (S i)).
      { unfold E. rewrite !oadd_eq. eapply ord_le_lt_trans; [apply le_sumO4 | apply (IH (S i)); lia]. }
      assert (HLi : L i = wm (L (S i)) (P i ⊕' B i)).
      { unfold L. rewrite box_lo by lia. rewrite HPP by lia. reflexivity. }
      assert (HWi : W i = wm (W (S i)) y) by (apply box_lo; lia).
      assert (HRi : Rh i = wm (Rh (S i)) (B i ⊕' W i)).
      { unfold Rh. rewrite box_lo by lia. unfold Bn. rewrite (box_hi 0 B Nv i) by lia. reflexivity. }
      rewrite HLi.
      apply ord_le_lt_trans with
        (sumO [sz (wm (Rh (S i)) (B i)); sz (wm (Rh (S i)) (W i)); sz (W i); sz (B i); sz (onat (S n))]).
      { apply split_head. rewrite HRi, wm_add. reflexivity. }
      apply absorb with (E := E); auto.
      repeat constructor.
      + apply wm_mono; [apply oadd_le1 | apply oadd_le2].
      + rewrite HWi, wm_wm. apply wm_mono; [|reflexivity].
        unfold E. apply oadd_mono; [reflexivity | apply oadd_le1].
      + rewrite HWi. apply wm_mono; [|reflexivity].
        unfold E. eapply ord_le_trans; [|apply oadd_le2]. apply oadd_le1.
      + eapply ord_le_trans; [apply oadd_le2 | apply wm_ge].
      + eapply ord_le_trans; [|apply wm_ge_exp; auto].
        eapply ord_le_trans; [|apply oexp_ge].
        unfold E. eapply ord_le_trans; [|apply oadd_le2].
        eapply ord_le_trans; [|apply oadd_le2]. apply oadd_le2. }
  intros i Hi. destruct i as [|i].
  - assert (HB0 : Bn 0%nat = wm (B 1%nat) (B 0%nat ⊕' Nv 0%nat)).
    { unfold Bn. rewrite box_lo by lia. rewrite box_hi by lia. reflexivity. }
    assert (HW0 : W 0%nat = wm (W 1%nat) (P 0%nat ⊕' B 0%nat)) by (apply box_lo; lia).
    assert (HR0 : Rh 0%nat = wm (Rh 1%nat) (Bn 0%nat ⊕' W 0%nat)) by (apply box_lo; lia).
    assert (HL0 : L 0%nat = wm (L 1%nat) (P 0%nat ⊕' B 0%nat)).
    { unfold L. rewrite box_lo by lia. rewrite HPP by lia. reflexivity. }
    set (y := P 0%nat ⊕' B 0%nat).
    assert (Hy : 0 < sz y) by (apply oadd_pos1; auto).
    set (E := Rh 1%nat ⊕' (W 1%nat ⊕' (B 1%nat ⊕' onat (S n)))).
    assert (HE : E ◃ L 1%nat).
    { unfold E. rewrite !oadd_eq. eapply ord_le_lt_trans; [apply le_sumO4 | apply Hup; lia]. }
    change (Rh 0%nat ◃ L 0%nat). rewrite HL0.
    apply ord_le_lt_trans with
      (sumO [sz (wm (Rh 1%nat ⊕' B 1%nat) (B 0%nat)); sz (wm (Rh 1%nat ⊕' B 1%nat) (Nv 0%nat));
             sz (wm (Rh 1%nat) (W 0%nat))]).
    { apply split_sum3. rewrite HR0, wm_add, HB0, wm_wm, wm_add. reflexivity. }
    apply absorb with (E := E); auto.
    repeat constructor.
    + apply wm_mono; [|apply oadd_le2].
      unfold E. apply oadd_mono; [reflexivity|].
      eapply ord_le_trans; [|apply oadd_le2]. apply oadd_le1.
    + eapply ord_le_trans; [apply wm_mono; [reflexivity | apply ord_lt_le, HN]|].
      rewrite wm_oexp. eapply ord_le_trans; [|apply wm_ge_exp; auto].
      apply oexp_mono. unfold E. rewrite !oadd_eq. rewrite <- !naddOrd_assoc.
      apply naddOrd_monotone; [reflexivity|]. apply naddOrd_le2.
    + rewrite HW0, wm_wm. apply wm_mono; [|reflexivity].
      unfold E. apply oadd_mono; [reflexivity | apply oadd_le1].
  - eapply ord_le_lt_trans; [|apply (Hup (S i)); lia]. cbn [sumO]. apply naddOrd_le1.
Qed.

(** ** Combinatory System T *)

Inductive ty : Set :=
| TN : ty
| TAr : ty -> ty -> ty.

Fixpoint lev (A:ty) : nat :=
  match A with
  | TN => 0
  | TAr A B => Nat.max (S (lev A)) (lev B)
  end.

(** Applications are annotated with the type of the argument. *)
Inductive term : Set :=
| var : nat -> term
| Kc : ty -> ty -> term            (* [K_{A,B} : A → B → A] *)
| Sc : ty -> ty -> ty -> term      (* [S_{A,B,C} : (A → B → C) → (A → B) → A → C] *)
| Zc : term
| Suc : term
| Rc : ty -> term                  (* [R_C : N → C → (N → C → C) → C] *)
| app : ty -> term -> term -> term.

Inductive typing (Γ:list ty) : term -> ty -> Prop :=
| T_var x A : nth_error Γ x = Some A -> typing Γ (var x) A
| T_K A B : typing Γ (Kc A B) (TAr A (TAr B A))
| T_S A B C : typing Γ (Sc A B C) (TAr (TAr A (TAr B C)) (TAr (TAr A B) (TAr A C)))
| T_Z : typing Γ Zc TN
| T_Suc : typing Γ Suc (TAr TN TN)
| T_R C : typing Γ (Rc C) (TAr TN (TAr C (TAr (TAr TN (TAr C C)) C)))
| T_app A B M N : typing Γ M (TAr A B) -> typing Γ N A -> typing Γ (app A M N) B.

Fixpoint num (n:nat) : term :=
  match n with O => Zc | S n => app TN Suc (num n) end.

Fixpoint is_num (t:term) : option nat :=
  match t with
  | Zc => Some O
  | app TN Suc t => option_map S (is_num t)
  | _ => None
  end.

Lemma is_num_num n : is_num (num n) = Some n.
Proof. induction n as [|n IH]; simpl; auto. rewrite IH. reflexivity. Qed.

Lemma is_num_spec t n : is_num t = Some n -> t = num n.
Proof.
  revert n. induction t as [| | | | | |A M _ N IHN]; intros m H; simpl in H; try discriminate.
  - injection H as <-. reflexivity.
  - destruct A; try discriminate. destruct M; try discriminate.
    destruct (is_num N) as [k|] eqn:E; simpl in H; try discriminate.
    injection H as <-. simpl. rewrite (IHN k eq_refl). reflexivity.
Qed.

(** Reduction.  The recursor reduces when its first argument is a
    numeral, as in Howard (1970); every closed term of type [N] still
    reduces to a numeral ([T_value]). *)
Inductive step : term -> term -> Prop :=
| st_K A B X Y a b : step (app Y (app X (Kc A B) a) b) a
| st_S A B C X Y W a b c :
    step (app W (app Y (app X (Sc A B C) a) b) c) (app B (app A a c) (app A b c))
| st_R0 C X Y W t a b : is_num t = Some O -> step (app W (app Y (app X (Rc C) t) a) b) a
| st_RS C X Y W t n a b : is_num t = Some (S n) ->
    step (app W (app Y (app X (Rc C) t) a) b)
         (app C (app TN b (num n)) (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) a) b))
| st_l A M M' N : step M M' -> step (app A M N) (app A M' N)
| st_r A M N N' : step N N' -> step (app A M N) (app A M N').

Lemma num_normal n M : step (num n) M -> False.
Proof.
  revert M. induction n as [|n IH]; intros M H; inversion H; subst.
  - inversion H4.
  - eapply IH; eauto.
Qed.

(** ** Typing facts *)

Lemma typing_app Γ A M N T : typing Γ (app A M N) T -> typing Γ M (TAr A T) /\ typing Γ N A.
Proof. intro H. inversion H; subst; auto. Qed.

Lemma typing_unique Γ M A : typing Γ M A -> forall B, typing Γ M B -> A = B.
Proof.
  intro H. induction H; intros T HT; inversion HT; subst; auto; try congruence.
  match goal with Hm : typing _ M (TAr _ T) |- _ => apply IHtyping1 in Hm; congruence end.
Qed.

Lemma typing_num Γ n : typing Γ (num n) TN.
Proof. induction n; simpl; repeat econstructor; eauto. Qed.

Theorem subject_reduction Γ M M' A : step M M' -> typing Γ M A -> typing Γ M' A.
Proof.
  intro H. revert A. induction H; intros T HT.
  - apply typing_app in HT as [H1 _]. apply typing_app in H1 as [H1 H2].
    inversion H1; subst. congruence.
  - apply typing_app in HT as [H1 Hc]. apply typing_app in H1 as [H1 Hb].
    apply typing_app in H1 as [H1 Ha]. inversion H1; subst.
    repeat econstructor; eauto.
  - apply typing_app in HT as [H1 _]. apply typing_app in H1 as [H1 Ha].
    apply typing_app in H1 as [H1 _]. inversion H1; subst. exact Ha.
  - apply typing_app in HT as [H1 Hb]. apply typing_app in H1 as [H1 Ha].
    apply typing_app in H1 as [H1 Ht]. inversion H1; subst.
    econstructor; [econstructor; [exact Hb | apply typing_num]|].
    econstructor; [econstructor; [econstructor; [constructor | apply typing_num] | exact Ha] | exact Hb].
  - apply typing_app in HT as [H1 H2]. econstructor; eauto.
  - apply typing_app in HT as [H1 H2]. econstructor; eauto.
Qed.

(** ** The ordinal assignment *)

Definition ones : vec := fun _ => oone.

Fixpoint meas (M:term) : vec :=
  match M with
  | Rc C => gen (lev C)
  | app A M N =>
      match M with
      | Rc C =>
          match is_num N with
          | Some n => vspec (lev C) n
          | None => box (lev A) (gen (lev C)) (meas N)
          end
      | _ => box (lev A) (meas M) (meas N)
      end
  | _ => ones
  end.

Lemma meas_app A M N : (forall C, M <> Rc C) -> meas (app A M N) = box (lev A) (meas M) (meas N).
Proof. intro H. destruct M; simpl; auto. elim (H t); auto. Qed.

Lemma meas_app_nonum A M N : is_num N = None -> meas (app A M N) = box (lev A) (meas M) (meas N).
Proof. intro H. destruct M; simpl; auto. rewrite H. reflexivity. Qed.

Lemma vspec_le_gen k n j : vspec k n j ⊴ gen k j.
Proof.
  unfold vspec, gen. destruct (j =? S (S k)); [|reflexivity].
  apply ord_lt_le. rewrite onat_eq, oomega_eq. apply index_lt.
Qed.

(** The vector of a numeral-applied recursor is at most that of the
    unapplied recursor applied to the numeral. *)
Lemma meas_app_le A M N j : meas (app A M N) j ⊴ box (lev A) (meas M) (meas N) j.
Proof.
  destruct M; simpl; try reflexivity.
  destruct (is_num N); [|reflexivity].
  eapply ord_le_trans; [apply vspec_le_gen | apply box_ge_f].
Qed.

Lemma ones_pos j : 0 < sz (ones j).
Proof. apply oone_pos. Qed.

Lemma meas_pos M j : 0 < sz (meas M j).
Proof.
  revert j. induction M as [| | | | | C | A M IHM N IHN]; intro j; try apply ones_pos.
  - apply gen_pos.
  - destruct M; try (rewrite meas_app by discriminate; apply box_pos; auto; fail).
    simpl. destruct (is_num N); [apply vspec_pos | apply box_pos, gen_pos].
Qed.

Lemma one_lt_oexp_onat n : oone ◃ oexp (onat (S n)).
Proof.
  rewrite oone_eq, oexp_eq, onat_eq.
  apply ord_le_lt_trans with (expOrd ω 0); [rewrite expOrd_zero; reflexivity|].
  apply expOrd_increasing; [apply omega_gt1 | apply (natOrdSize_increasing 0 (S n)); lia].
Qed.

Lemma num_meas n : meas (num n) 0%nat ◃ oexp (onat (S n)).
Proof.
  induction n as [|n IH].
  - apply one_lt_oexp_onat.
  - change (num (S n)) with (app TN Suc (num n)).
    rewrite meas_app by (intros ? ?; discriminate). change (meas Suc) with ones. change (lev TN) with 0%nat.
    rewrite (box_lo 0 ones (meas (num n)) 0%nat), (box_hi 0 ones (meas (num n)) 1%nat) by lia.
    eapply ord_lt_le_trans; [apply (wm_increasing _ _ (oexp (onat (S n))))|].
    + rewrite oadd_eq. apply below_oexp; [apply one_lt_oexp_onat | exact IH].
    + unfold ones. rewrite wm_oexp, !oexp_eq. apply expOrd_monotone.
      rewrite oadd_eq, oone_eq, !onat_eq. rewrite naddOrd_comm.
      change (natOrdSize (S n) ⊕ succOrd 0 ≤ succOrd (natOrdSize (S n))).
      rewrite naddOrd_succ2, naddOrd_zero_r. reflexivity.
Qed.

(** ** Every reduction step decreases the assignment

    [decr m f g]: [g] is at most [f] at every level up to [m], and below
    it at level [0]. *)

Definition decr (m:nat) (f g:vec) : Prop :=
  (g 0%nat ◃ f 0%nat) /\ forall i, (i <= m)%nat -> (g i ⊴ f i).

Lemma decr_of_lt m (f g:vec) : (forall i, (i <= m)%nat -> g i ◃ f i) -> decr m f g.
Proof. intro H. split; [apply H; lia | intros; apply ord_lt_le, H; auto]. Qed.

Lemma meas_R_num A C t n : is_num t = Some n -> meas (app A (Rc C) t) = vspec (lev C) n.
Proof. intro H. simpl. rewrite H. reflexivity. Qed.

Lemma lev_rec_step C : lev (TAr TN (TAr C C)) = S (lev C).
Proof. cbn [lev]. lia. Qed.

Lemma step_not_Rc C M : step (Rc C) M -> False.
Proof. intro H. inversion H. Qed.

Ltac not_Rc := intros ? ?; discriminate.

Theorem step_decreases M M' : step M M' ->
  forall Γ A, typing Γ M A -> decr (lev A) (meas M) (meas M').
Proof.
  induction 1 as [A B X Y a b | A B C X Y W a b c | C X Y W t a b Ht | C X Y W t n a b Ht
                 | A0 M M' N Hs IH | A0 M N N' Hs IH]; intros Γ T HT.
  - (* K *)
    apply typing_app in HT as [H1 Hb]. apply typing_app in H1 as [H1 Ha].
    inversion H1; subst.
    do 2 (rewrite meas_app by not_Rc). change (meas (Kc _ _)) with ones.
    apply decr_of_lt. intros i Hi.
    eapply ord_lt_le_trans; [|apply box_ge_f].
    eapply ord_lt_le_trans; [|apply box_ge_sum; auto]. apply oadd_lt2, ones_pos.
  - (* S *)
    apply typing_app in HT as [H1 Hc]. apply typing_app in H1 as [H1 Hb].
    apply typing_app in H1 as [H1 Ha]. inversion H1; subst.
    do 3 (rewrite meas_app by not_Rc). change (meas (Sc _ _ _)) with ones.
    apply decr_of_lt. intros i Hi.
    eapply ord_le_lt_trans.
    { eapply ord_le_trans; [apply meas_app_le|].
      apply box_mono_all; intro j; apply meas_app_le. }
    apply S_decrease with (t := lev T); auto using ones_pos, meas_pos; cbn [lev]; lia.
  - (* R 0 *)
    apply typing_app in HT as [H1 Hb]. apply typing_app in H1 as [H1 Ha].
    apply typing_app in H1 as [H1 _]. inversion H1; subst.
    do 2 (rewrite meas_app by not_Rc). rewrite (meas_R_num _ _ _ _ Ht).
    apply decr_of_lt. intros i Hi.
    eapply ord_lt_le_trans; [|apply box_ge_f].
    eapply ord_lt_le_trans; [|apply box_ge_sum; auto]. apply oadd_lt2, vspec_pos.
  - (* R (n+1) *)
    apply typing_app in HT as [H1 Hb]. apply typing_app in H1 as [H1 Ha].
    apply typing_app in H1 as [H1 _]. inversion H1; subst.
    do 2 (rewrite meas_app by not_Rc). rewrite (meas_R_num _ _ _ _ Ht). rewrite lev_rec_step.
    apply decr_of_lt. intros i Hi.
    eapply ord_le_lt_trans.
    { eapply ord_le_trans; [apply meas_app_le|].
      apply box_mono_all; intro j.
      - apply meas_app_le.
      - do 2 (rewrite meas_app by not_Rc).
        rewrite (meas_R_num _ _ _ _ (is_num_num n)), lev_rec_step. reflexivity. }
    apply R_decrease; auto using meas_pos, num_meas.
  - (* left congruence *)
    apply typing_app in HT as [HM HN].
    destruct (IH _ _ HM) as [IH0 IHle].
    rewrite (meas_app A0 M) by (intros C ->; eapply step_not_Rc; eauto).
    split.
    + eapply ord_le_lt_trans; [apply meas_app_le|].
      apply box_lt0 with (m := lev (TAr A0 T)); auto; [cbn [lev]; lia | intros; reflexivity].
    + intros i Hi. eapply ord_le_trans; [apply meas_app_le|].
      apply box_mono with (m := lev (TAr A0 T)); auto; [cbn [lev]; lia | intros; reflexivity |].
      cbn [lev]. lia.
  - (* right congruence *)
    apply typing_app in HT as [HM HN].
    destruct (IH _ _ HN) as [IH0 IHle].
    assert (Hn : is_num N = None).
    { destruct (is_num N) as [k|] eqn:E; auto. apply is_num_spec in E. subst.
      elim (num_normal _ _ Hs). }
    rewrite (meas_app_nonum A0 M N Hn).
    split.
    + eapply ord_le_lt_trans; [apply meas_app_le|].
      apply box_lt0 with (m := lev (TAr A0 T)); auto; [cbn [lev]; lia | intros; reflexivity].
    + intros i Hi. eapply ord_le_trans; [apply meas_app_le|].
      apply box_mono with (m := lev (TAr A0 T)); auto; [cbn [lev]; lia | intros; reflexivity |].
      cbn [lev]. lia.
Qed.

(** ** Strong normalization *)

Definition SN (M:term) : Prop := Acc (fun N M => step M N) M.

Theorem typed_SN Γ M A : typing Γ M A -> SN M.
Proof.
  revert Γ A.
  induction M as [M IH] using
    (well_founded_induction (wf_inverse_image _ _ ord_lt (fun M => sz (meas M 0%nat)) ord_lt_wf)).
  intros Γ A H. constructor. intros M' Hs.
  apply IH with Γ A.
  - apply (step_decreases _ _ Hs _ _ H).
  - eapply subject_reduction; eauto.
Qed.

(** The ordinal of a term is a notation, so below ε₀. *)
Theorem meas_below_ε0 M : sz (meas M 0%nat) < ε 0.
Proof. apply ON_below_ε0. Qed.

(** ** Confluence

    By Takahashi's method: parallel reduction, and the complete
    development [cd M], which contracts every redex of [M] at once. *)

Inductive star : term -> term -> Prop :=
| star_refl M : star M M
| star_step M N P : step M N -> star N P -> star M P.

Lemma star_trans M N P : star M N -> star N P -> star M P.
Proof. intro H. induction H; eauto using star. Qed.

Lemma star_one M N : step M N -> star M N.
Proof. eauto using star. Qed.

Lemma star_app_l A M M' N : star M M' -> star (app A M N) (app A M' N).
Proof. induction 1; eauto using star, step. Qed.

Lemma star_app_r A M N N' : star N N' -> star (app A M N) (app A M N').
Proof. induction 1; eauto using star, step. Qed.

Lemma star_app A M M' N N' : star M M' -> star N N' -> star (app A M N) (app A M' N').
Proof. intros. eapply star_trans; [apply star_app_l | apply star_app_r]; eauto. Qed.

Inductive par : term -> term -> Prop :=
| p_refl M : par M M
| p_app A M M' N N' : par M M' -> par N N' -> par (app A M N) (app A M' N')
| p_K A B X Y a a' b : par a a' -> par (app Y (app X (Kc A B) a) b) a'
| p_S A B C X Y W a a' b b' c c' : par a a' -> par b b' -> par c c' ->
    par (app W (app Y (app X (Sc A B C) a) b) c) (app B (app A a' c') (app A b' c'))
| p_R0 C X Y W t a a' b : is_num t = Some O -> par a a' ->
    par (app W (app Y (app X (Rc C) t) a) b) a'
| p_RS C X Y W t n a a' b b' : is_num t = Some (S n) -> par a a' -> par b b' ->
    par (app W (app Y (app X (Rc C) t) a) b)
        (app C (app TN b' (num n)) (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) a') b')).

Lemma step_par M N : step M N -> par M N.
Proof. induction 1; eauto using par. Qed.

Lemma par_star M N : par M N -> star M N.
Proof.
  induction 1.
  - apply star_refl.
  - apply star_app; auto.
  - eapply star_step; [apply st_K | auto].
  - eapply star_trans; [apply star_app; [apply star_app; [apply star_app_r|]|]; eauto|].
    apply star_one, st_S.
  - eapply star_step; [apply st_R0; auto | auto].
  - eapply star_trans; [apply star_app; [apply star_app_r|]; eauto|].
    apply star_one, st_RS; auto.
Qed.

Fixpoint cd (M:term) : term :=
  match M with
  | app W F c =>
      match F with
      | app _ (Kc _ _) a => cd a
      | app Y (app X (Sc A B C) a) b => app B (app A (cd a) (cd c)) (app A (cd b) (cd c))
      | app Y (app X (Rc C) t) a =>
          match is_num t with
          | Some O => cd a
          | Some (S n) =>
              app C (app TN (cd c) (num n))
                  (app (TAr TN (TAr C C)) (app C (app TN (Rc C) (num n)) (cd a)) (cd c))
          | None => app W (cd F) (cd c)
          end
      | _ => app W (cd F) (cd c)
      end
  | _ => M
  end.

(** The shapes of an application, as [cd] sees them. *)
Lemma app_view W F c :
  (exists X A B a, F = app X (Kc A B) a) \/
  (exists Y X A B C a b, F = app Y (app X (Sc A B C) a) b) \/
  (exists Y X C t a n, F = app Y (app X (Rc C) t) a /\ is_num t = Some n) \/
  (cd (app W F c) = app W (cd F) (cd c) /\
   (forall X A B a, F <> app X (Kc A B) a) /\
   (forall Y X A B C a b, F <> app Y (app X (Sc A B C) a) b) /\
   (forall Y X C t a, F = app Y (app X (Rc C) t) a -> is_num t = None)).
Proof.
  destruct F as [| | | | | |Y G b];
    try (right; right; right; repeat split; intros; discriminate).
  destruct G as [| | | | | |X H a];
    try (right; right; right; repeat split; intros; try discriminate; reflexivity).
  - left. eauto.
  - destruct H as [| | | | | |];
      try (right; right; right; repeat split; intros; try discriminate; reflexivity).
    + right; left. eauto 10.
    + destruct (is_num a) as [n|] eqn:E.
      * right; right; left. eauto 10.
      * right; right; right. simpl. rewrite E. repeat split; intros; try discriminate.
        congruence.
Qed.

Lemma par_atom M N : par M N -> (forall A F c, M <> app A F c) -> N = M.
Proof. intros H Hm. inversion H; subst; auto; exfalso; eapply Hm; eauto. Qed.

Lemma par_num n N : par (num n) N -> N = num n.
Proof.
  revert N. induction n as [|n IH]; intros N H.
  - apply (par_atom _ _ H). intros; discriminate.
  - inversion H; subst; auto.
    match goal with Hs : par Suc _, Hn : par (num n) _ |- _ =>
      apply par_atom in Hs; [|intros; discriminate]; apply IH in Hn; subst; reflexivity end.
Qed.

Lemma par_K1 X A B a N : par (app X (Kc A B) a) N -> exists a', N = app X (Kc A B) a' /\ par a a'.
Proof.
  intro H. inversion H; subst; eauto using par.
  match goal with Hs : par ?K _ |- _ =>
    apply par_atom in Hs; [|intros; discriminate]; subst; eauto end.
Qed.

Lemma par_S1 X A B C a N : par (app X (Sc A B C) a) N -> exists a', N = app X (Sc A B C) a' /\ par a a'.
Proof.
  intro H. inversion H; subst; eauto using par.
  match goal with Hs : par ?K _ |- _ =>
    apply par_atom in Hs; [|intros; discriminate]; subst; eauto end.
Qed.

Lemma par_S2 Y X A B C a b N : par (app Y (app X (Sc A B C) a) b) N ->
  exists a' b', N = app Y (app X (Sc A B C) a') b' /\ par a a' /\ par b b'.
Proof.
  intro H. inversion H; subst; eauto 6 using par.
  match goal with Hs : par (app _ (Sc _ _ _) _) _ |- _ => apply par_S1 in Hs as [a' [-> Ha]]; eauto end.
Qed.

Lemma par_R1 X C t N : par (app X (Rc C) t) N -> exists t', N = app X (Rc C) t' /\ par t t'.
Proof.
  intro H. inversion H; subst; eauto using par.
  match goal with Hs : par ?K _ |- _ =>
    apply par_atom in Hs; [|intros; discriminate]; subst; eauto end.
Qed.

Lemma par_R2 Y X C t a N : par (app Y (app X (Rc C) t) a) N ->
  exists t' a', N = app Y (app X (Rc C) t') a' /\ par t t' /\ par a a'.
Proof.
  intro H. inversion H; subst; eauto 6 using par.
  match goal with Hs : par (app _ (Rc _) _) _ |- _ => apply par_R1 in Hs as [t' [-> Ht]]; eauto end.
Qed.

Lemma par_self_cd M : par M (cd M).
Proof.
  induction M as [| | | | | |W F IHF c IHc]; try apply p_refl.
  destruct (app_view W F c) as [[X [A [B [a ->]]]] | [[Y [X [A [B [C [a [b ->]]]]]]] |
                                [[Y [X [C [t [a [n [-> Hn]]]]]]] | [Hcd _]]]].
  - simpl in IHF. apply par_K1 in IHF as [a' [E Ha]]. injection E as <-.
    simpl. apply p_K. exact Ha.
  - simpl in IHF. apply par_S2 in IHF as [a' [b' [E [Ha Hb]]]]. injection E as <- <-.
    simpl. apply p_S; auto.
  - simpl in IHF.
    apply par_R2 in IHF as [t' [a' [E [_ Ha]]]]. injection E as <- <-.
    simpl. rewrite Hn. destruct n; [apply p_R0 | apply p_RS]; auto.
  - rewrite Hcd. apply p_app; auto.
Qed.

Theorem par_cd M N : par M N -> par N (cd M).
Proof.
  induction 1 as [M | W F F' c c' HF IHF Hc IHc | A B X Y a a' b Ha IHa
                 | A B C X Y W a a' b b' c c' Ha IHa Hb IHb Hc IHc
                 | C X Y W t a a' b Ht Ha IHa | C X Y W t n a a' b b' Ht Ha IHa Hb IHb].
  - apply par_self_cd.
  - destruct (app_view W F c) as [[X [A [B [a ->]]]] | [[Y [X [A [B [C [a [b ->]]]]]]] |
                                  [[Y [X [C [t [a [n [-> Hn]]]]]]] | [Hcd _]]]].
    + apply par_K1 in HF as [a' [-> Ha]]. simpl in IHF.
      apply par_K1 in IHF as [a'' [E Ha']]. injection E as <-.
      simpl. apply p_K. exact Ha'.
    + apply par_S2 in HF as [a' [b' [-> [Ha Hb]]]]. simpl in IHF.
      apply par_S2 in IHF as [a'' [b'' [E [Ha' Hb']]]]. injection E as <- <-.
      simpl. apply p_S; auto.
    + apply par_R2 in HF as [t' [a' [-> [Ht Ha]]]]. simpl in IHF.
      apply par_R2 in IHF as [t'' [a'' [E [Ht' Ha']]]]. injection E as <- <-.
      apply is_num_spec in Hn as Et. subst t. apply par_num in Ht. subst t'.
      simpl. rewrite is_num_num. destruct n; [apply p_R0 | apply p_RS]; auto using is_num_num.
    + rewrite Hcd. apply p_app; auto.
  - simpl. exact IHa.
  - simpl. repeat apply p_app; auto.
  - simpl. rewrite Ht. exact IHa.
  - simpl. rewrite Ht. repeat apply p_app; auto using p_refl.
Qed.

Lemma strip M N1 N2 : par M N1 -> star M N2 -> exists P, star N1 P /\ par N2 P.
Proof.
  intros H1 H2. revert N1 H1. induction H2 as [M | M M1 N2 Hs _ IH]; intros N1 H1.
  - exists N1. split; [apply star_refl | exact H1].
  - destruct (IH (cd M) (par_cd _ _ (step_par _ _ Hs))) as [P [HP1 HP2]].
    exists P. split; auto. eapply star_trans; [apply par_star, par_cd, H1 | exact HP1].
Qed.

Theorem confluence M N1 N2 : star M N1 -> star M N2 -> exists P, star N1 P /\ star N2 P.
Proof.
  intro H1. revert N2. induction H1 as [M | M M1 N1 Hs _ IH]; intros N2 H2.
  - exists N2. split; [exact H2 | apply star_refl].
  - destruct (strip _ _ _ (step_par _ _ Hs) H2) as [Q [HQ1 HQ2]].
    destruct (IH Q HQ1) as [P [HP1 HP2]].
    exists P. split; auto. eapply star_trans; [apply par_star, HQ2 | exact HP2].
Qed.

(** ** Closed terms of type [N] evaluate to numerals *)

Definition normal (M:term) : Prop := forall N, ~ step M N.

Lemma step_or_normal M : (exists N, step M N) \/ normal M.
Proof.
  induction M as [| | | | | |W F IHF c IHc];
    try (right; intros N H; inversion H; fail).
  destruct IHF as [[F' HF]|HF]; [left; eauto using step|].
  destruct IHc as [[c' Hc]|Hc]; [left; eauto using step|].
  destruct (app_view W F c) as [[X [A [B [a ->]]]] | [[Y [X [A [B [C [a [b ->]]]]]]] |
                                [[Y [X [C [t [a [n [-> Hn]]]]]]] | [_ [HK [HS HR]]]]]].
  - left. eauto using step.
  - left. eauto using step.
  - left. destruct n; eauto using step.
  - right. intros N H. inversion H; subst.
    + eapply HK; eauto.
    + eapply HS; eauto.
    + rewrite (HR _ _ _ _ _ eq_refl) in *. discriminate.
    + rewrite (HR _ _ _ _ _ eq_refl) in *. discriminate.
    + eapply HF; eauto.
    + eapply Hc; eauto.
Qed.

Lemma SN_normal_form M : SN M -> exists N, star M N /\ normal N.
Proof.
  induction 1 as [M _ IH].
  destruct (step_or_normal M) as [[M' Hs]|Hn].
  - destruct (IH M' Hs) as [N [HN1 HN2]]. exists N. split; eauto using star.
  - exists M. split; [apply star_refl | exact Hn].
Qed.

Lemma star_typing Γ M N A : star M N -> typing Γ M A -> typing Γ N A.
Proof. induction 1; eauto using subject_reduction. Qed.

Lemma star_normal M N : normal M -> star M N -> N = M.
Proof. intros Hn H. destruct H; auto. elim (Hn _ H). Qed.

(** Closed normal terms are numerals or partial applications of
    constants. *)
Inductive value : term -> Prop :=
| v_num n : value (num n)
| v_Suc : value Suc
| v_K A B : value (Kc A B)
| v_K1 X A B a : value (app X (Kc A B) a)
| v_S A B C : value (Sc A B C)
| v_S1 X A B C a : value (app X (Sc A B C) a)
| v_S2 Y X A B C a b : value (app Y (app X (Sc A B C) a) b)
| v_R C : value (Rc C)
| v_R1 X C n : value (app X (Rc C) (num n))
| v_R2 Y X C n a : value (app Y (app X (Rc C) (num n)) a).

Lemma value_nat Γ M : value M -> typing Γ M TN -> exists n, M = num n.
Proof.
  intros Hv Ht. destruct Hv; eauto; exfalso;
    repeat match goal with H : typing _ (app _ _ _) _ |- _ => apply typing_app in H as [H _] end;
    inversion Ht; subst; try congruence;
    match goal with H : typing _ _ _ |- _ => inversion H end.
Qed.

Lemma normal_app_l A M N : normal (app A M N) -> normal M.
Proof. intros H M' Hs. eapply H, st_l, Hs. Qed.

Lemma normal_app_r A M N : normal (app A M N) -> normal N.
Proof. intros H N' Hs. eapply H, st_r, Hs. Qed.

Lemma closed_normal_value M A : typing [] M A -> normal M -> value M.
Proof.
  remember [] as Γ. intro H. induction H as [x A Hx | | | | | | A B F N HF IHF HN IHN]; intros Hn; subst.
  - destruct x; discriminate.
  - constructor.
  - constructor.
  - apply (v_num 0).
  - constructor.
  - constructor.
  - specialize (IHF (normal_app_l _ _ _ Hn)).
    specialize (IHN (normal_app_r _ _ _ Hn)).
    destruct IHF.
    + exfalso. pose proof (typing_unique _ _ _ HF _ (typing_num [] n)). discriminate.
    + inversion HF; subst. destruct (value_nat _ _ IHN HN) as [m ->]. apply (v_num (S m)).
    + constructor.
    + elim (Hn _ (st_K _ _ _ _ _ _)).
    + constructor.
    + constructor.
    + elim (Hn _ (st_S _ _ _ _ _ _ _ _ _)).
    + inversion HF; subst. destruct (value_nat _ _ IHN HN) as [m ->]. constructor.
    + constructor.
    + destruct n.
      * elim (Hn _ (st_R0 _ _ _ _ _ _ _ (is_num_num 0))).
      * elim (Hn _ (st_RS _ _ _ _ _ _ _ _ (is_num_num (S n)))).
Qed.

(** Every closed term of type [N] reduces to a unique numeral. *)
Theorem T_value M : typing [] M TN ->
  exists n, star M (num n) /\ forall m, star M (num m) -> m = n.
Proof.
  intro H. destruct (SN_normal_form _ (typed_SN _ _ _ H)) as [N [HMN HN]].
  pose proof (star_typing _ _ _ _ HMN H) as HNt.
  destruct (value_nat _ _ (closed_normal_value _ _ HNt HN) HNt) as [n ->].
  exists n. split; auto. intros m Hm.
  destruct (confluence _ _ _ HMN Hm) as [P [HP1 HP2]].
  apply star_normal in HP1; [|intros ? ?; eapply num_normal; eauto].
  apply star_normal in HP2; [|intros ? ?; eapply num_normal; eauto].
  rewrite HP1 in HP2. apply (f_equal is_num) in HP2. rewrite !is_num_num in HP2. congruence.
Qed.
