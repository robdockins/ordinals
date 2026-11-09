From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Cantor.
From Ordinal Require Import Reflection.
From Ordinal Require Import NaturalArith.
From Ordinal Require Import NaturalProduct.
From Ordinal Require Import NaturalExp.
From Ordinal Require Import Notation.Interpolants.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.CantorProduct.
From Ordinal Require Import Notation.SchutteMatrix.

Open Scope ord_scope.

(** * No natural exponentiation on notation systems, constructively

  [NaturalExp.v] shows, with excluded middle, that no operation on the
  ordinals satisfies the laws of a natural exponentiation, and that the
  excluded middle is needed only for the [e]-free ratio lemma
  [no_log23_ratio].  Here we prove the ratio lemma constructively for
  ordinals denoted by a notation system with a Cantor decomposition and
  interpolants ([no_log23_ratio_notation]).  Hence no operation on such a
  notation system satisfies the laws, restricted to its notations
  ([natural_exp_impossible_notation]), constructively.  This covers the
  notation systems of the development, up to the large Veblen ordinal.

  Each use of excluded middle in the classical proof has a constructive
  substitute on notations:
  - Cantor normal forms come from the decomposition of the notation
    system ([dec_head], [lead_exists_Q]);
  - comparisons of exponents are decided by its comparison ([Qn_dec]);
  - powers of [ω] with complete exponents are closed under natural sums
    constructively ([nadd_closed_con]);
  - the leading exponent of a natural product of notations is read off
    the term-by-term product of their normal forms ([has_deg_mul_Q]),
    which reflects [nmulOrd] given interpolants ([cantor_nmul_reflects]). *)

Local Abbreviation V := NaturalArith.cantor_denote_nadd.

(** ** Leading exponents of natural sums of powers, constructively *)

Lemma V_ge_member z zs : In z zs -> expOrd ω z ≤ V zs.
Proof.
  induction zs as [|a zs IH]; simpl; intro Hz; [contradiction|].
  destruct Hz as [->|Hz].
  - apply ord_le_trans with (expOrd ω z ⊕ 0); [apply (naddOrd_zero_r _)|].
    apply naddOrd_monotone; [reflexivity | apply zero_least].
  - apply ord_le_trans with (V zs); auto.
    apply ord_le_trans with (0 ⊕ V zs); [apply (naddOrd_zero_l _)|].
    apply naddOrd_monotone; [apply zero_least | reflexivity].
Qed.

Lemma V_le_nrep z0 zs :
  (forall z, In z zs -> z ≤ z0) -> V zs ≤ nrep (length zs) (expOrd ω z0).
Proof.
  induction zs as [|a zs IH]; simpl; intro H; [reflexivity|].
  rewrite naddOrd_comm. apply naddOrd_monotone.
  - apply IH. intros z Hz. apply H; auto.
  - apply expOrd_monotone. apply H; auto.
Qed.

Lemma has_deg_V z0 zs : In z0 zs -> (forall z, In z zs -> z ≤ z0) -> has_deg z0 (V zs).
Proof.
  intros Hin Hle. split; [apply V_ge_member; auto|].
  exists (S (length zs)).
  apply ord_le_lt_trans with (nrep (length zs) (expOrd ω z0)); [apply V_le_nrep; auto|].
  apply nrep_lt_succ. apply expOrd_nonzero.
Qed.

Lemma nrep_below_con k d : complete d -> nrep k (expOrd ω d) < expOrd ω (succOrd d).
Proof.
  intro Hd. induction k; simpl.
  - apply expOrd_nonzero.
  - apply nadd_closed_con; auto.
    + apply succ_complete; auto.
    + apply expOrd_increasing; [apply omega_gt1 | apply succ_lt].
Qed.

Lemma nrep_lt_closed_con k g r : complete g -> r < expOrd ω g -> nrep k r < expOrd ω g.
Proof.
  intros Hg Hr. induction k; simpl.
  - apply expOrd_nonzero.
  - apply nadd_closed_con; auto.
Qed.

Lemma lead_nrep_con γ c d k :
  complete γ -> has_lead γ c d -> has_lead γ (S k * c) (nrep (S k) d).
Proof.
  intros Hγ [Hc [r [Hr Hd]]]. split; [lia|].
  exists (nrep (S k) r). split; [apply nrep_lt_closed_con; auto|].
  rewrite Hd. rewrite nrep_nadd. rewrite nrep_nrep. reflexivity.
Qed.

Section notation.
Variable A : Type.
Variable f : A -> Ord.
Variable P : A -> Prop.
Variable X : has_cantor_decomposition f P.
Hypothesis Hinterp : has_all_interpolants f P.

Local Abbreviation Q := (Qn A f P).

Lemma Q_f a : P a -> Q (f a).
Proof. intro Ha. exists a. split; auto. reflexivity. Qed.

Lemma Qn_nmul x y : Q x -> Q y -> Q (nmulOrd x y).
Proof.
  intros [a [Ha Hx]] [b [Hb Hy]].
  pose proof (cantor_nmul_reflects A f P X Hinterp) as R. simpl in R.
  destruct (R x a (conj Hx Ha) y b (conj Hy Hb)) as [H1 H2].
  exists (cantor_nmul A f P X a b). split; auto.
Qed.

Lemma Qn_nat n : Q (natOrdSize n).
Proof.
  destruct (cantor_nat_correct X n) as [H1 H2].
  exists (cantor_nat X n). split; auto. symmetry. exact H1.
Qed.

Lemma Qn_omega : Q ω.
Proof.
  destruct (cantor_nat_correct X 1) as [H1 H2].
  destruct (cantor_recompose_correct X [cantor_nat X 1]) as [H3 H4].
  { simpl; auto. }
  { simpl; auto. }
  exists (cantor_recompose X [cantor_nat X 1]). split; auto.
  rewrite <- H4. simpl. rewrite addOrd_zero_r. rewrite H1.
  symmetry. apply expOrd_one'. apply omega_gt0.
Qed.

Lemma Qn_nrep k x : Q x -> Q (nrep k x).
Proof.
  intro Hx. induction k; simpl; [apply Qn_zero; auto | apply Qn_nadd; auto].
Qed.

(** Leading exponents of notation-denoted ordinals are compared by the
    notation system. *)
Lemma has_deg_le_Q δ δ' x x' :
  Q δ -> Q δ' -> has_deg δ x -> has_deg δ' x' -> x ≤ x' -> δ ≤ δ'.
Proof.
  intros [a [Ha Ea]] [b [Hb Eb]] Hd Hd' Hxx'.
  apply has_deg_eq_exp with (δ' := f a) in Hd; auto.
  apply has_deg_eq_exp with (δ' := f b) in Hd'; auto.
  rewrite Ea, Eb.
  destruct Hd as [Hl _]. destruct Hd' as [_ [n Hu]].
  destruct (Qn_dec A f P X (f b) (f a) (Q_f b Hb) (Q_f a Ha)) as [Hlt|Hle]; auto.
  exfalso. apply (ord_lt_irreflexive (expOrd ω (f a))).
  apply ord_le_lt_trans with x; auto.
  apply ord_le_lt_trans with x'; auto.
  apply ord_lt_le_trans with (nrep n (expOrd ω (f b))); auto.
  apply ord_lt_le. apply ord_lt_le_trans with (expOrd ω (succOrd (f b))).
  - apply nrep_below_con. apply (cantor_decomp_complete X).
  - apply expOrd_monotone. apply succ_least. auto.
Qed.

(** The head of the Cantor decomposition is the leading exponent. *)
Lemma dec_head x : P x -> 0 < f x ->
  exists d ds, cantor_decompose X x = d :: ds /\ P d /\ has_deg (f d) (f x) /\
    (forall z, In z (d :: ds) -> f z ≤ f d).
Proof.
  intros Hx Hpos.
  destruct (cantor_decompose_correct X x Hx) as [Hp [Ho He]].
  pose proof (dec_value A f P X x Hx) as Hv.
  destruct (cantor_decompose X x) as [|d ds] eqn:E.
  - elim (ord_lt_irreflexive 0). apply ord_lt_le_trans with (f x); auto. apply He.
  - exists d, ds. destruct Hp as [Hd Hds].
    pose proof (ordered_head_le A f ds d Ho) as Hb.
    split; [reflexivity|]. split; [auto|]. split; [|auto].
    apply has_deg_eq with (V (map f (d :: ds))); [symmetry; auto|].
    apply has_deg_V; [simpl; auto|].
    intros z Hz. apply in_map_iff in Hz. destruct Hz as [y [<- Hy]]. apply Hb; auto.
Qed.

Lemma pos_of_deg δ z : has_deg δ z -> 0 < z.
Proof. intros [Hl _]. apply ord_lt_le_trans with (expOrd ω δ); auto. apply expOrd_nonzero. Qed.

(** The leading exponent of a natural product of notations, from the
    term-by-term product of their normal forms. *)
Lemma has_deg_mul_Q x y : P x -> P y -> 0 < f x -> 0 < f y ->
  exists dx dy, P dx /\ P dy /\ has_deg (f dx) (f x) /\ has_deg (f dy) (f y) /\
    has_deg (f dx ⊕ f dy) (nmulOrd (f x) (f y)).
Proof.
  intros Hx Hy Px Py.
  destruct (dec_head x Hx Px) as [d [ds [Ex [Hd [Hdx Hbx]]]]].
  destruct (dec_head y Hy Py) as [e [es [Ey [He [Hdy Hby]]]]].
  exists d, e. split; [|split; [|split; [|split]]]; auto.
  destruct (cantor_nmul_correct A f P X x y Hx Hy) as [_ Hc].
  rewrite Ex, Ey in Hc.
  pose proof (cantor_nmul_reflects A f P X Hinterp) as R. simpl in R.
  destruct (R (f x) x (conj (ord_eq_refl _) Hx) (f y) y (conj (ord_eq_refl _) Hy)) as [Hr _].
  apply has_deg_eq with (V (cnf_prod (map f (d :: ds)) (map f (e :: es)))).
  { rewrite Hr, Hc. reflexivity. }
  apply has_deg_V.
  - unfold cnf_prod. simpl. auto.
  - intros z Hz. unfold cnf_prod in Hz. apply in_flat_map in Hz.
    destruct Hz as [a [Ha Hz]]. apply in_map_iff in Hz. destruct Hz as [b [<- Hb]].
    apply in_map_iff in Ha. destruct Ha as [a' [<- Ha']].
    apply in_map_iff in Hb. destruct Hb as [b' [<- Hb']].
    apply naddOrd_monotone; auto.
Qed.

(** The leading exponent of a natural power of a notation. *)
Lemma npow_deg_Q k x δ : P x -> Q δ -> has_deg δ (f x) ->
  exists y, P y /\ npow (S k) (f x) ≈ f y /\ has_deg (nrep (S k) δ) (f y).
Proof.
  intros Hx Qδ Hδ. induction k.
  - exists x. split; [|split]; auto.
    + apply npow_one.
    + apply has_deg_eq_exp with δ; auto. symmetry. apply nrep_one.
  - destruct IHk as [y [Hy [Ey Hdy]]].
    destruct (has_deg_mul_Q y x Hy Hx (pos_of_deg _ _ Hdy) (pos_of_deg _ _ Hδ))
      as [dy [dx [Pdy [Pdx [Hdy' [Hdx' Hm]]]]]].
    pose proof (cantor_nmul_reflects A f P X Hinterp) as R. simpl in R.
    destruct (R (f y) y (conj (ord_eq_refl _) Hy) (f x) x (conj (ord_eq_refl _) Hx))
      as [Hr Hp].
    exists (cantor_nmul A f P X y x). split; [auto|split].
    + change (npow (S (S k)) (f x)) with (nmulOrd (npow (S k) (f x)) (f x)).
      rewrite Ey. exact Hr.
    + apply has_deg_eq with (nmulOrd (f y) (f x)); auto.
      apply has_deg_eq_exp with (f dy ⊕ f dx); auto.
      change (nrep (S (S k)) δ) with (nrep (S k) δ ⊕ δ).
      apply naddOrd_eq_mor.
      * split; apply (has_deg_le_Q _ _ (f y) (f y)); auto using Q_f, Qn_nrep;
          reflexivity.
      * split; apply (has_deg_le_Q _ _ (f x) (f x)); auto using Q_f; reflexivity.
Qed.

(** Splitting off the leading run of equal exponents. *)
Fixpoint take_eq (g:A) (l:list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | z :: l' =>
      match cantor_decomp_compare X g z with
      | EQ => let (p, s) := take_eq g l' in (z :: p, s)
      | _ => ([], l)
      end
  end.

Lemma take_eq_spec g : forall l p s, take_eq g l = (p, s) ->
  l = p ++ s /\ (forall z, In z p -> cantor_decomp_compare X g z = EQ) /\
  match s with [] => True | z :: _ => cantor_decomp_compare X g z <> EQ end.
Proof.
  induction l as [|z l IH]; simpl; intros p s H.
  - injection H as <- <-. split; [reflexivity|]. split; [intros _ []|exact I].
  - destruct (cantor_decomp_compare X g z) eqn:Hc.
    + injection H as <- <-. simpl. split; [auto|]. split; [intros _ []|].
      rewrite Hc. discriminate.
    + destruct (take_eq g l) as [p' s'] eqn:Ht. injection H as <- <-.
      destruct (IH p' s' eq_refl) as [H1 [H2 H3]].
      split; [simpl; rewrite H1; auto|]. split; auto.
      intros w [<-|Hw]; auto.
    + injection H as <- <-. simpl. split; [auto|]. split; [intros _ []|].
      rewrite Hc. discriminate.
Qed.

Lemma ordered_app_r p s : cantor_ordered f (p ++ s) -> cantor_ordered f s.
Proof.
  induction p as [|a p IH]; simpl; auto.
  intro H. apply IH. apply (ordered_tail A f (p ++ s) a). exact H.
Qed.

(** The leading coefficient of a notation-denoted ordinal. *)
Lemma lead_exists_Q d : P d -> 0 < f d -> exists g c, P g /\ has_lead (f g) c (f d).
Proof.
  intros Hd Hpos.
  destruct (cantor_decompose_correct X d Hd) as [Hp [Ho _]].
  pose proof (dec_value A f P X d Hd) as Hv.
  destruct (dec_head d Hd Hpos) as [g [ds [E [Hg [_ Hb]]]]].
  rewrite E in Hp, Ho, Hv.
  destruct (take_eq g (g :: ds)) as [pre suf] eqn:Ht.
  destruct (take_eq_spec g (g :: ds) pre suf Ht) as [Hl [Hpre Hsuf]].
  assert (HP : forall z, In z (g :: ds) -> P z).
  { intros z Hz. destruct Hp as [Hg' Hds]. destruct Hz as [<-|Hz]; auto.
    apply each_in with ds; auto. }
  assert (Hin : forall z, In z pre -> In z (g :: ds)).
  { intros z Hz. rewrite Hl. apply in_or_app. auto. }
  assert (Heq : forall z, In z pre -> f z ≈ f g).
  { intros z Hz. pose proof (cantor_decomp_compare_correct X g z Hg (HP z (Hin z Hz))) as Hc.
    rewrite (Hpre z Hz) in Hc. symmetry. exact Hc. }
  exists g, (length pre). split; auto. split.
  - destruct pre as [|p pre]; simpl; [|lia].
    simpl in Hl. rewrite <- Hl in Hsuf.
    pose proof (cantor_decomp_compare_correct X g g Hg Hg) as Hc.
    destruct (cantor_decomp_compare X g g); try (elim Hsuf; reflexivity);
      elim (ord_lt_irreflexive (f g)); exact Hc.
  - exists (V (map f suf)). split.
    + destruct suf as [|s rest]; simpl; [apply expOrd_nonzero|].
      assert (Hs : In s (g :: ds)) by (rewrite Hl; apply in_or_app; simpl; auto).
      assert (Hord : cantor_ordered f (s :: rest)).
      { apply ordered_app_r with pre. rewrite <- Hl. exact Ho. }
      assert (Hsg : f s < f g).
      { pose proof (cantor_decomp_compare_correct X g s Hg (HP s Hs)) as Hc.
        destruct (cantor_decomp_compare X g s); [| elim Hsuf; reflexivity | exact Hc].
        elim (ord_lt_irreflexive (f g)). apply ord_lt_le_trans with (f s); auto. }
      change (V (f s :: map f rest)) with (V (map f (s :: rest))).
      apply (V_below_power A f (s :: rest) (f s) (f g)); auto.
      * apply ordered_head_le; auto.
      * apply (cantor_decomp_complete X).
    + rewrite Hv. rewrite Hl. rewrite map_app. rewrite V_app.
      apply naddOrd_eq_mor; [|reflexivity].
      rewrite (cantor_nadd_all_eq (f g) (map f pre)).
      * rewrite length_map. reflexivity.
      * intros a Ha. apply in_map_iff in Ha. destruct Ha as [z [<- Hz]]. auto.
Qed.

(** ** The ratio lemma for notations *)

Theorem no_log23_ratio_notation x y : P x -> P y -> ~ log23_ratio (f x) (f y).
Proof.
  intros Hx Hy [HX [Hup Hdown]].
  assert (HXY : f x ≤ f y).
  { rewrite <- (npow_one (f x)), <- (npow_one (f y)). apply (Hup 0%nat 0%nat). simpl; lia. }
  assert (Px : 0 < f x) by (apply ord_lt_le_trans with ω; auto with ord).
  assert (Py : 0 < f y) by (apply ord_lt_le_trans with (f x); auto).
  destruct (dec_head x Hx Px) as [d2 [ds2 [_ [Hd2 [Hδ2 _]]]]].
  destruct (dec_head y Hy Py) as [d3 [ds3 [_ [Hd3 [Hδ3 _]]]]].
  assert (Hmono : forall a k, (2 ^ S a <= 3 ^ S k)%nat ->
            nrep (S a) (f d2) ≤ nrep (S k) (f d3)).
  { intros a k H.
    destruct (npow_deg_Q a x (f d2) Hx (Q_f d2 Hd2) Hδ2) as [z2 [Pz2 [Ez2 Hz2]]].
    destruct (npow_deg_Q k y (f d3) Hy (Q_f d3 Hd3) Hδ3) as [z3 [Pz3 [Ez3 Hz3]]].
    apply (has_deg_le_Q _ _ (f z2) (f z3)); auto using Qn_nrep, Q_f.
    rewrite <- Ez2, <- Ez3. apply Hup; auto. }
  assert (Hmono' : forall a k, (3 ^ S k <= 2 ^ S a)%nat ->
            nrep (S k) (f d3) ≤ nrep (S a) (f d2)).
  { intros a k H.
    destruct (npow_deg_Q a x (f d2) Hx (Q_f d2 Hd2) Hδ2) as [z2 [Pz2 [Ez2 Hz2]]].
    destruct (npow_deg_Q k y (f d3) Hy (Q_f d3 Hd3) Hδ3) as [z3 [Pz3 [Ez3 Hz3]]].
    apply (has_deg_le_Q _ _ (f z3) (f z2)); auto using Qn_nrep, Q_f.
    rewrite <- Ez2, <- Ez3. apply Hdown; auto. }
  (* [D₂ > 0], since [f x ≥ ω]. *)
  assert (Hδ2pos : 0 < f d2).
  { destruct (Qn_dec A f P X 0 (f d2) (Qn_zero A f P X) (Q_f d2 Hd2)) as [H|H]; auto.
    exfalso. destruct Hδ2 as [_ [n Hn]].
    apply (ord_lt_irreflexive ω).
    apply ord_le_lt_trans with (f x); auto.
    apply ord_lt_le_trans with (nrep n (expOrd ω (f d2))); auto.
    rewrite H. rewrite expOrd_zero.
    rewrite (nrep_nat n 1). apply ord_lt_le. apply index_lt. }
  assert (Hδ23 : f d2 ≤ f d3).
  { exact (has_deg_le_Q _ _ _ _ (Q_f d2 Hd2) (Q_f d3 Hd3) Hδ2 Hδ3 HXY). }
  destruct (lead_exists_Q d2 Hd2 Hδ2pos) as [g2 [c2 [Hg2 Hl2]]].
  destruct (lead_exists_Q d3 Hd3) as [g3 [c3 [Hg3 Hl3]]].
  { apply ord_lt_le_trans with (f d2); auto. }
  assert (Cg2 : complete (f g2)) by apply (cantor_decomp_complete X).
  assert (Cg3 : complete (f g3)) by apply (cantor_decomp_complete X).
  (* [D₂] and [D₃] have the same leading exponent. *)
  assert (Hγ23 : f g2 ≤ f g3).
  { exact (has_deg_le_Q _ _ _ _ (Q_f g2 Hg2) (Q_f g3 Hg3) (lead_deg _ _ _ Hl2)
             (lead_deg _ _ _ Hl3) Hδ23). }
  assert (Hγ32 : f g3 ≤ f g2).
  { apply (has_deg_le_Q _ _ _ _ (Q_f g3 Hg3) (Q_f g2 Hg2) (lead_deg _ _ _ Hl3)
             (lead_deg _ _ _ (lead_nrep_con _ _ _ 1 Cg2 Hl2))).
    rewrite <- (nrep_one (f d3)). apply (Hmono' 1%nat 0%nat). simpl; lia. }
  apply (nat_no_ratio c2 c3); [apply Hl2 | apply Hl3 | |].
  - intros a k Ha Hk H.
    destruct a as [|a]; [lia|]. destruct k as [|k]; [lia|].
    exact (lead_le _ _ _ _ _ _ (lead_nrep_con _ _ _ a Cg2 Hl2) (lead_nrep_con _ _ _ k Cg3 Hl3)
             (Hmono a k H) Hγ32).
  - intros a k Ha Hk H.
    destruct a as [|a]; [lia|]. destruct k as [|k]; [lia|].
    exact (lead_le _ _ _ _ _ _ (lead_nrep_con _ _ _ k Cg3 Hl3) (lead_nrep_con _ _ _ a Cg2 Hl2)
             (Hmono' a k H) Hγ23).
Qed.

(** Constructively, there is no power family with values in the
    notations. *)
Theorem no_power_family_notation F : (forall n, Q (F n)) -> ~ power_family F.
Proof.
  intros HQ H.
  destruct (HQ 2%nat) as [x [Hx Ex]]. destruct (HQ 3%nat) as [y [Hy Ey]].
  apply (no_log23_ratio_notation x y Hx Hy).
  exact (log23_ratio_eq _ _ _ _ Ex Ey (power_family_ratio F H)).
Qed.

(** ** No natural exponentiation on notations *)

(** An operation on the notations: it maps notation-denoted ordinals to
    notation-denoted ordinals.  The rest of [exp_domain] holds for any
    such notation system. *)
Lemma exp_domain_notation e :
  (forall a b, Q a -> Q b -> Q (e a b)) -> exp_domain Q e.
Proof.
  intro He.
  exact (conj Qn_nat (conj Qn_omega (conj (Qn_nadd A f P X) (conj Qn_nmul He)))).
Qed.

(** Constructively, no operation on the notations satisfies the laws of a
    natural exponentiation, restricted to the notations. *)
Theorem natural_exp_impossible_notation :
  ~ exists e, (forall a b, Q a -> Q b -> Q (e a b)) /\ natural_exp_laws_on Q e.
Proof.
  intros [e [HQ He]].
  pose proof (laws_log23_ratio_on Q e (exp_domain_notation e HQ) He) as R.
  destruct (HQ _ _ (Qn_nat 2) Qn_omega) as [x [Hx Ex]].
  destruct (HQ _ _ (Qn_nat 3) Qn_omega) as [y [Hy Ey]].
  apply (no_log23_ratio_notation x y Hx Hy).
  exact (log23_ratio_eq _ _ _ _ Ex Ey R).
Qed.

End notation.

(** For example, on the Schütte matrices, whose normal forms reach the
    large Veblen ordinal. *)
Corollary natural_exp_impossible_schutte_matrix :
  let Q := Qn _ SchutteMatrix.VF_denote SchutteMatrix.VF_normal in
  ~ exists e, (forall a b, Q a -> Q b -> Q (e a b)) /\ natural_exp_laws_on Q e.
Proof.
  exact (natural_exp_impossible_notation _ _ _ SchutteMatrix.VF_has_cantor_decomposition
           SchutteMatrix.schutte_matrix_has_all_interpolants).
Qed.
