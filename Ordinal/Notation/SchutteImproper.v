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
From Ordinal Require Import Reflection.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.
From Ordinal Require Import SchutteAbsorb.
From Ordinal Require Import Notation.CantorDecomposition.
From Ordinal Require Import Notation.SchutteMatrix.

Open Scope ord_scope.

(** * Normalizing arbitrary Schütte matrices

[VF_normalize] (in @SchutteMatrix.v@) handles proper matrices only:
strictly decreasing heights.  Here every [VForm] is normalized:
columns in any order, repeated heights, zero entries, height-0 columns
anywhere.  The ordinal facts are in @SchutteAbsorb.v@: a column
followed by a strictly higher one is absorbed, at the cost of a shift
of the argument ([absorb_shift_list]); equal heights merge
([schutte_column_merge]); a height-1 column over a translation is the
low-regime exception ([low_regime_veblen]).  This file computes the
shifts ([VF_offset]) and assembles the normalizer [VF_normalizeX]. *)

Local Hint Resolve VForm_complete normal_complete schutte_matrix_normal onePlus_normal succ_complete zero_complete addOrd_complete : core.

Definition md := matrix_denote.
Definition MX (L:list (VForm*VForm)) : Ord -> Ord := schutte_matrix (addOrd 1) (md L).

Definition nfL (L:list (VForm*VForm)) : Prop := each (fun c => VF_normal (fst c) /\ VF_normal (snd c)) L.

Lemma md_complete L : all_complete (md L).
Proof. apply VForm_all_complete. Qed.

Local Hint Resolve md_complete : core.

Lemma MX_normal L : normal_function (MX L).
Proof. unfold MX. apply schutte_matrix_normal; auto. Qed.

Local Hint Resolve MX_normal : core.

Lemma normal_eq f x y : normal_function f -> x ≈ y -> f x ≈ f y.
Proof. intros Hf E. split; apply normal_monotone; auto; apply E. Qed.

Lemma normal_mono' f : normal_function f -> forall a b, a ≤ b -> f a ≤ f b.
Proof. intros Hf a b H. apply normal_monotone; auto. Qed.

Local Hint Resolve normal_mono' ord_le_refl complete_subord : core.

Lemma md_app L1 L2 : md (L1 ++ L2) = md L1 ++ md L2.
Proof. unfold md, matrix_denote. apply map_app. Qed.

Lemma VF_denote_N L : VF_denote (N L) = MX L 0.
Proof. reflexivity. Qed.

Lemma cmp_spec x y : VF_normal x -> VF_normal y ->
  ordering_correct (VF_compare x y) (VF_denote x) (VF_denote y).
Proof. intros. apply VF_compare_correct; apply VF_normal_proper; auto. Qed.

Lemma cmp_eq x y : VF_normal x -> VF_normal y -> VF_compare x y = EQ -> x = y.
Proof.
  intros Hx Hy E. assert (H := cmp_spec x y Hx Hy). rewrite E in H.
  apply VF_normal_form_unique; auto.
Qed.

Lemma nfL_app L1 L2 : nfL (L1 ++ L2) <-> nfL L1 /\ nfL L2.
Proof. unfold nfL. induction L1; simpl; intuition. Qed.

Lemma In_md b a L : In (b,a) (md L) -> exists b' a', In (b',a') L /\ b = VF_denote b' /\ a = VF_denote a'.
Proof.
  unfold md, matrix_denote. intro H. apply in_map_iff in H. destruct H as [[b' a'] [E Hin]].
  inversion E; subst. exists b', a'. auto.
Qed.

Lemma In_nfL b a L : nfL L -> In (b,a) L -> VF_normal b /\ VF_normal a.
Proof.
  unfold nfL. induction L as [|[b' a'] L IH]; simpl; [ tauto | ].
  intros [Hc HL] [E|Hin]; [ inversion E; subst; auto | auto ].
Qed.

(** * Lexicographic comparison of column lists *)

Fixpoint lexcmp (Y X : list (VForm*VForm)) : ordering :=
  match Y, X with
  | [], [] => EQ
  | [], _ :: _ => LT
  | _ :: _, [] => GT
  | (g,d)::Y', (h,e)::X' =>
    match VF_compare g h with
    | EQ => match VF_compare d e with
            | EQ => lexcmp Y' X'
            | o => o
            end
    | o => o
    end
  end.

Lemma lexcmp_spec : forall Y X, nfL Y -> nfL X ->
  match lexcmp Y X with
  | LT => mlt (md Y) (md X)
  | EQ => Y = X
  | GT => mlt (md X) (md Y)
  end.
Proof.
  induction Y as [|[g d] Y IH]; intros [|[h e] X] HY HX; simpl; auto.
  - constructor.
  - constructor.
  - destruct HY as [[Hg Hd] HY]. destruct HX as [[Hh He] HX]. simpl in *.
    assert (Hc := cmp_spec g h Hg Hh).
    destruct (VF_compare g h) eqn:Egh.
    + apply mlt_height. exact Hc.
    + assert (E := cmp_eq g h Hg Hh Egh). subst h.
      assert (Hc2 := cmp_spec d e Hd He).
      destruct (VF_compare d e) eqn:Ede.
      * apply mlt_entry. exact Hc2.
      * assert (E := cmp_eq d e Hd He Ede). subst e.
        specialize (IH X HY HX). destruct (lexcmp Y X).
        -- apply mlt_cons with (c := (VF_denote g, VF_denote d)). exact IH.
        -- subst. reflexivity.
        -- apply mlt_cons with (c := (VF_denote g, VF_denote d)). exact IH.
      * apply mlt_entry. exact Hc2.
    + apply mlt_height. exact Hc.
Qed.

(** * Structure of proper column lists *)

Lemma proper_desc : forall L, VF_matrix_proper L -> desc (md L).
Proof.
  assert (Hhead : forall L b a, VF_matrix_proper ((b,a)::L) ->
            forall b' a', In (b',a') (md L) -> b' < VF_denote b).
  { induction L as [|[b2 a2] L IH]; intros b a H b' a' Hin; simpl in *; [ contradiction | ].
    destruct H as [_ [_ [Hlt H]]].
    destruct Hin as [E|Hin]; [ inversion E; subst; auto | ].
    eapply ord_lt_trans; [ apply (IH b2 a2 H b' a' Hin) | exact Hlt ]. }
  induction L as [|[b a] L IH]; simpl; auto. intro H. split.
  - intros b' a' Hin. apply (Hhead L b a H b' a' Hin).
  - apply IH. destruct L as [|[??]?]; simpl in *; intuition.
Qed.

Lemma proper_heights_nonzero : forall L c, VF_matrix_proper (L ++ [c]) ->
  forall b a, In (b,a) L -> b <> Z.
Proof.
  induction L as [|[b1 a1] L IH]; intros c H b a Hin; [ contradiction | ].
  simpl in H. destruct Hin as [E|Hin].
  - inversion E; subst. intro E'. subst.
    remember (L ++ [c]) as Lc. destruct Lc as [|[b2 a2] rest]; [ destruct L; discriminate | ].
    destruct H as [_ [_ [Hlt _]]]. simpl in Hlt. apply (ord_lt_irreflexive 0).
    eapply ord_le_lt_trans; [ apply zero_least | exact Hlt ].
  - apply (IH c) with a; auto. destruct L as [|[??]?]; simpl in *; intuition.
Qed.

Definition posL (L:list (VForm*VForm)) : Prop := forall b a, In (b,a) L -> b <> Z /\ a <> Z.

Lemma posL_poscols L : posL L -> poscols (md L).
Proof.
  intros H b a Hin. destruct (In_md b a L Hin) as [b' [a' [Hin' [E1 E2]]]]. subst.
  destruct (H b' a' Hin'). split; apply VF_nonzero; auto.
Qed.

Lemma sparse_In L b a : is_sparse L -> In (b,a) L -> a <> Z.
Proof.
  induction L as [|[b' a'] L IH]; simpl; [ tauto | ].
  intros [Ha HL] [E|Hin]; [ inversion E; subst; auto | auto ].
Qed.

Definition strip0 (ys : list (VForm*VForm)) : list (VForm*VForm) * VForm :=
  match rev ys with
  | (Z, y')::r => (rev r, y')
  | _ => (ys, Z)
  end.

Lemma strip0_spec ys :
  let (Y,y') := strip0 ys in
  ys = Y ++ [(Z,y')] \/ (ys = Y /\ y' = Z /\ forall c L, ys = L ++ [c] -> fst c <> Z).
Proof.
  unfold strip0. destruct (rev ys) as [|[b a] r] eqn:E.
  - right. split; [ auto | split; [ auto | ] ]. intros c L E'. subst.
    rewrite rev_app_distr in E. discriminate.
  - destruct b as [|l].
    + left. rewrite <- (rev_involutive ys), E. simpl. reflexivity.
    + right. split; [ auto | split; [ auto | ] ]. intros c L E'. subst.
      rewrite rev_app_distr in E. simpl in E. inversion E; subst. simpl. discriminate.
Qed.

Lemma VF_normal_N_pos ys : 0 < VF_denote (N ys).
Proof. rewrite VF_denote_N. apply normal_nonzero; auto. Qed.

(** What a normal matrix looks like after stripping its argument column. *)
Lemma strip0_normal ys : VF_normal (N ys) ->
  let (Y,y') := strip0 ys in
  nfL Y /\ VF_normal y' /\ VF_matrix_proper Y /\ posL Y /\
  (forall b a, In (b,a) Y -> VF_denote a < VF_denote (N ys)) /\ VF_denote y' < VF_denote (N ys) /\
  VF_denote (N ys) ≈ MX Y (VF_denote y').
Proof.
  intro Hn. assert (Hn' := Hn). cbn [VF_normal] in Hn'. destruct Hn' as [Hsp [Hpr [Hnf Hlt]]].
  assert (Hlt' : forall b a, In (b,a) ys -> VF_denote a < VF_denote (N ys)).
  { clear -Hlt. revert Hlt. generalize (VF_denote (N ys)). intro v.
    induction ys as [|[b' a'] ys IH]; simpl; [ tauto | ]. intros [H1 H2] b a [E|Hin]; [ inversion E; subst; exact H1 | apply (IH H2 b a Hin) ]. }
  assert (HnfY : forall Y, (exists R, ys = Y ++ R) -> nfL Y).
  { intros Y [R E]. subst. apply (proj1 (nfL_app Y R)). exact Hnf. }
  assert (Hpos : forall Y c, ys = Y ++ [c] -> fst c <> Z -> posL ys).
  { intros Y c E Hc b a Hin. split; [ | apply (sparse_In ys b a); auto ].
    rewrite E in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E'|[]]].
    - apply (proper_heights_nonzero Y c) with a; auto. rewrite <- E; auto.
    - subst. simpl in Hc. auto. }
  assert (Hval := strip0_spec ys). destruct (strip0 ys) as [Y y'].
  destruct Hval as [E|[E [Ey' Hlast]]].
  - assert (HnfY' : nfL Y) by (apply HnfY; eauto).
    assert (Hy' : VF_normal y').
    { rewrite E in Hnf. apply (proj1 (nfL_app Y _)) in Hnf. destruct Hnf as [_ [[_ H] _]]. exact H. }
    split; [ auto | split; [ auto | split; [ | split; [ | split; [ | split ] ] ] ] ].
    + apply VF_matrix_proper_app with [(Z,y')]. rewrite <- E; auto.
    + intros b a Hin. split.
      * apply (proper_heights_nonzero Y (Z,y')) with a; auto. rewrite <- E; auto.
      * apply (sparse_In ys b a); auto. rewrite E. apply in_or_app; auto.
    + intros b a Hin. apply Hlt' with b. rewrite E. apply in_or_app; auto.
    + apply Hlt' with Z. rewrite E. apply in_or_app; right; left; auto.
    + rewrite VF_denote_N. rewrite E. unfold MX. rewrite md_app, schutte_matrix_app. simpl.
      rewrite schutte_column0. apply normal_eq; auto. apply addOrd_zero_r.
  - subst Y y'. split; [ apply HnfY; exists []; rewrite app_nil_r; auto | split; [ exact I | split; [ auto | split; [ | split; [ auto | split ] ] ] ] ].
    + destruct ys as [|c L] using rev_ind; [ intros b a [] | ].
      apply (Hpos L c); auto. apply (Hlast c L); auto.
    + apply VF_normal_N_pos.
    + reflexivity.
Qed.

(** * Maximum of a list of notations *)

Fixpoint vmax (xs : list VForm) : VForm :=
  match xs with
  | [] => Z
  | x :: xs' => let m := vmax xs' in
                match VF_compare x m with LT => m | _ => x end
  end.

Lemma vmax_spec : forall xs, each VF_normal xs ->
  VF_normal (vmax xs) /\ (forall x, In x xs -> VF_denote x ≤ VF_denote (vmax xs)) /\
  (xs = [] \/ In (vmax xs) xs).
Proof.
  induction xs as [|x xs IH]; simpl; intros H.
  - split; [ exact I | split; [ tauto | auto ] ].
  - destruct H as [Hx Hxs]. destruct (IH Hxs) as [Hm [Hle Hin]].
    assert (Hc := cmp_spec x (vmax xs) Hx Hm).
    destruct (VF_compare x (vmax xs)); simpl in Hc.
    + split; [ auto | split ].
      * intros y [E|Hy]; [ subst; apply ord_lt_le; auto | auto ].
      * right. destruct Hin as [E|Hin]; [ subst; simpl in Hc | right; auto ].
        elim (ord_lt_irreflexive 0). eapply ord_le_lt_trans; [ apply zero_least | exact Hc ].
    + split; [ auto | split; [ | right; left; auto ] ].
      intros y [E|Hy]; [ subst; reflexivity | rewrite (Hle y Hy); apply Hc ].
    + split; [ auto | split; [ | right; left; auto ] ].
      intros y [E|Hy]; [ subst; reflexivity | rewrite (Hle y Hy); apply ord_lt_le; auto ].
Qed.

Lemma entry_size : forall ys b a, In (b,a) ys -> (VF_termSize a < VF_termSize (N ys))%nat.
Proof.
  induction ys as [|[b' a'] ys IH]; simpl; intros b a Hin; [ contradiction | ].
  destruct Hin as [E|Hin].
  - inversion E; subst. lia.
  - specialize (IH b a Hin). simpl in IH. lia.
Qed.

(** * Offsets

[VF_offset X m] is the least t with m < M_X(t), for a proper list X of
positive columns.  If m is not below M_X(0), compare the matrix of m
(argument column removed) with X: equal means m = M_X(y'); greater
means m is a fixpoint of M_X ([fix_gt]); smaller means the values of
M_X above m are those above its largest component ([nest]). *)

Fixpoint offN (fuel:nat) (X:list (VForm*VForm)) (m:VForm) : VForm :=
  match fuel with
  | O => Z
  | S fuel' =>
    match VF_compare m (N X) with
    | LT => Z
    | EQ => VF_one
    | GT =>
      match m with
      | Z => Z
      | N ys =>
        let (Y, y') := strip0 ys in
        match lexcmp Y X with
        | EQ => VF_succ y'
        | GT => VF_succ m
        | LT => offN fuel' X (vmax (y' :: map snd Y))
        end
      end
    end
  end.

Definition VF_offset (X:list (VForm*VForm)) (m:VForm) : VForm := offN (S (VF_termSize m)) X m.

Definition OffSpec (X:list (VForm*VForm)) (m t:VForm) : Prop :=
  VF_normal t /\ VF_denote m < MX X (VF_denote t) /\
  forall y, y < VF_denote t -> MX X y ≤ VF_denote m.

Lemma VF_one_normal : VF_normal VF_one.
Proof. simpl. intuition. Qed.

Lemma VF_one_denote : VF_denote VF_one ≈ 1.
Proof. simpl. apply addOrd_zero_r. Qed.

Lemma lt_one_le_zero y : y < 1 -> y ≤ 0.
Proof. intro H. rewrite ord_lt_unfold in H. destruct H as [[] H]. exact H. Qed.

Lemma succ_reflect x : VF_normal x -> VF_denote (VF_succ x) ≈ succOrd (VF_denote x) /\ VF_normal (VF_succ x).
Proof.
  intro Hx. destruct (VF_succ_reflects (VF_denote x) x (conj (ord_eq_refl _) Hx)) as [E N'].
  split; [ symmetry; exact E | exact N' ].
Qed.

Lemma add_reflect x y : VF_normal x -> VF_normal y ->
  VF_denote (VF_add x y) ≈ VF_denote x + VF_denote y /\ VF_normal (VF_add x y).
Proof.
  intros Hx Hy. destruct (VF_add_reflects (VF_denote x) x (conj (ord_eq_refl _) Hx)
                            (VF_denote y) y (conj (ord_eq_refl _) Hy)) as [E N'].
  split; [ symmetry; exact E | exact N' ].
Qed.

Lemma le_succ_lt y x : y < succOrd x -> y ≤ x.
Proof. intro H. rewrite ord_lt_unfold in H. destruct H as [[] H]. exact H. Qed.

Lemma entries_below_value X b a : In (b,a) X -> VF_denote a ≤ MX X 0.
Proof.
  intro Hin. destruct (in_split _ _ Hin) as [L1 [L2 E]]. subst X.
  unfold MX. rewrite md_app. simpl. apply matrix_member_le; auto.
Qed.

Section offset.
  Variable X : list (VForm*VForm).
  Hypothesis HnfX : nfL X.
  Hypothesis HprX : VF_matrix_proper X.
  Hypothesis HposX : posL X.

  Let HdX : desc (md X) := proper_desc X HprX.
  Let HpcX : poscols (md X) := posL_poscols X HposX.
  Let HFn : normal_function (MX X) := MX_normal X.

  Theorem offN_correct : forall fuel m, (VF_termSize m < fuel)%nat -> VF_normal m -> OffSpec X m (offN fuel X m).
  Proof.
    induction fuel as [|fuel IH]; intros m Hsz Hm; [ lia | ].
    assert (HpN : VF_proper (N X)) by (rewrite VF_proper_eq; auto).
    assert (Hc := VF_compare_correct m (N X) (VF_normal_proper m Hm) HpN).
    simpl offN. destruct (VF_compare m (N X)); cbn [ordering_correct] in Hc; rewrite VF_denote_N in Hc.
    - (* below M_X(0) *)
      split; [ exact I | split; [ exact Hc | ] ]. intros y Hy. elim (ord_lt_irreflexive 0).
      eapply ord_le_lt_trans; [ apply zero_least | exact Hy ].
    - (* equal to M_X(0) *)
      split; [ apply VF_one_normal | split ].
      + rewrite Hc. apply normal_increasing; auto. rewrite VF_one_denote. apply succ_lt.
      + intros y Hy. rewrite VF_one_denote in Hy. rewrite Hc. apply normal_monotone; auto.
        apply lt_one_le_zero; auto.
    - (* above M_X(0) *)
      destruct m as [|ys].
      { elim (ord_lt_irreflexive 0). eapply ord_le_lt_trans; [ apply zero_least | exact Hc ]. }
      assert (Hst := strip0_normal ys Hm). assert (Hsz' := entry_size ys).
      assert (Hst0 := strip0_spec ys).
      destruct (strip0 ys) as [Y y'].
      destruct Hst as [HnfY [Hy' [HprY [HposY [HYlt [Hylt EY]]]]]].
      assert (HdY := proper_desc Y HprY). assert (HpcY := posL_poscols Y HposY).
      assert (Hlx := lexcmp_spec Y X HnfY HnfX).
      destruct (lexcmp Y X).
      + (* Y < X: recurse on the largest component *)
        set (u := vmax (y' :: map snd Y)).
        assert (Hu : each VF_normal (y' :: map snd Y)).
        { simpl. split; auto. clear -HnfY. unfold nfL in HnfY. induction Y as [|[b a] Y IH]; simpl in *; intuition. }
        destruct (vmax_spec _ Hu) as [Hun [Hule [Hnil|Huin]]]; [ discriminate | ].
        fold u in Hun, Hule, Huin.
        assert (Hum : VF_denote u < VF_denote (N ys)).
        { destruct Huin as [E|Hin]; [ rewrite <- E; auto | ].
          apply in_map_iff in Hin. destruct Hin as [[b a] [E Hin]]. simpl in E. subst. eauto. }
        assert (Husz : (VF_termSize u < fuel)%nat).
        { assert (VF_termSize u < VF_termSize (N ys))%nat; [ | lia ].
          destruct Huin as [E|Hin].
          - rewrite <- E. destruct Hst0 as [E'|[E' [Ey _]]].
            + apply (Hsz' Z). rewrite E'. apply in_or_app. right; left; auto.
            + subst. simpl. lia.
          - apply in_map_iff in Hin. destruct Hin as [[b a] [E Hin]]. simpl in E. subst.
            destruct Hst0 as [E'|[E' _]]; apply (Hsz' b); rewrite E'; auto. apply in_or_app; auto. }
        destruct (IH u Husz Hun) as [Ht [Hut Hbelow]].
        split; [ exact Ht | split ].
        * rewrite EY. unfold MX.
          apply nest; auto.
          -- intros b a Hin. destruct (In_md b a Y Hin) as [b' [a' [Hin' [E1 E2]]]]. subst.
             eapply ord_le_lt_trans; [ | exact Hut ]. apply Hule. right. apply in_map_iff. exists (b',a'). auto.
          -- eapply ord_le_lt_trans; [ | exact Hut ]. apply Hule. left; auto.
        * intros y Hy. rewrite (Hbelow y Hy). apply ord_lt_le; auto.
      + (* Y = X: m is a value of M_X *)
        subst Y. destruct (succ_reflect y' Hy') as [Es Ns].
        split; [ exact Ns | split ].
        * apply ord_lt_le_trans with (MX X (succOrd (VF_denote y'))).
          -- rewrite EY. apply normal_increasing; auto. apply succ_lt.
          -- apply normal_monotone; auto. apply Es.
        * intros y Hy. rewrite Es in Hy. rewrite EY. apply normal_monotone; auto. apply le_succ_lt; auto.
      + (* Y > X: m is a fixpoint of M_X *)
        assert (Hfix : MX X (VF_denote (N ys)) ≤ VF_denote (N ys)).
        { transitivity (MX X (MX Y (VF_denote y'))); [ apply normal_monotone; auto; apply EY | ].
          rewrite EY. unfold MX. apply fix_gt; auto.
          intros b a Hin. destruct (In_md b a X Hin) as [b' [a' [Hin' [E1 E2]]]]. subst.
          rewrite <- EY. eapply ord_le_lt_trans; [ apply (entries_below_value X b' a' Hin') | exact Hc ]. }
        destruct (succ_reflect (N ys) Hm) as [Es Ns].
        split; [ exact Ns | split ].
        * apply ord_lt_le_trans with (MX X (succOrd (VF_denote (N ys)))).
          -- eapply ord_le_lt_trans; [ apply normal_inflationary; auto | ].
             apply normal_increasing; auto. apply succ_lt.
          -- apply normal_monotone; auto. apply Es.
        * intros y Hy. rewrite Es in Hy. rewrite <- Hfix. apply normal_monotone; auto. apply le_succ_lt; auto.
  Qed.

  Corollary VF_offset_correct m : VF_normal m -> OffSpec X m (VF_offset X m).
  Proof. intro Hm. apply offN_correct; auto. Qed.
End offset.

(** * The leading exponent of a notation *)

Definition lead (d:VForm) : VForm :=
  match VF_decompose d with
  | x :: _ => x
  | [] => Z
  end.

Lemma cantor_bound : forall xs a, cantor_ordered VF_denote xs ->
  (forall x, In x xs -> VF_denote x ≤ a) -> complete a ->
  cantor_denote VF_denote xs < expOrd ω (succOrd a).
Proof.
  assert (Hω : complete ω) by apply omega_complete.
  induction xs as [|x xs IH]; intros a Ho Hle Ha; simpl.
  - apply expOrd_nonzero.
  - apply expOmega_additively_closed; auto using succ_complete.
    + apply expOrd_increasing; [ apply omega_gt1 | ].
      apply ord_le_lt_trans with a; [ apply Hle; left; auto | apply succ_lt ].
    + apply IH; auto. destruct Ho; auto.
      intros y Hy. apply Hle. right; auto.
Qed.

Lemma lead_spec d : VF_normal d -> 0 < VF_denote d ->
  VF_normal (lead d) /\ expOrd ω (VF_denote (lead d)) ≤ VF_denote d /\
  VF_denote d < expOrd ω (succOrd (VF_denote (lead d))).
Proof.
  intros Hd Hpos.
  destruct (VF_decompose_correct d Hd) as [Hnf [Ho E]].
  unfold lead. destruct (VF_decompose d) as [|x xs] eqn:Ed.
  - simpl in E. elim (ord_lt_irreflexive 0). eapply ord_lt_le_trans; [ exact Hpos | apply E ].
  - simpl in Hnf. destruct Hnf as [Hx Hxs]. split; [ exact Hx | split ].
    + rewrite E. simpl. apply addOrd_le1.
    + rewrite E. apply cantor_bound; auto.
      * intros y [Ey|Hy]; [ subst; reflexivity | ].
        (* ordered: every later exponent is at most the first *)
        clear -Ho Hy. revert x Ho. induction xs as [|x2 xs IH]; intros x Ho; [ contradiction | ].
        destruct Ho as [H12 Ho]. destruct Hy as [Ey|Hy]; [ subst; exact H12 | ].
        rewrite (IH Hy x2 Ho). exact H12.
Qed.

(** * Pushing a column onto a proper list, merging equal heights *)

Fixpoint mpush (L:list (VForm*VForm)) (h e:VForm) : list (VForm*VForm) :=
  match L with
  | [] => [(h,e)]
  | [(b,a)] => match VF_compare b h with
               | EQ => [(b, VF_add a e)]
               | _ => [(b,a); (h,e)]
               end
  | c :: L' => c :: mpush L' h e
  end.

Lemma mpush_head c L h e : exists a' L', mpush (c::L) h e = (fst c, a') :: L'.
Proof.
  destruct L as [|c2 L].
  - destruct c as [b a]. simpl. destruct (VF_compare b h); eauto.
  - destruct c as [b a]. exists a, (mpush (c2::L) h e). reflexivity.
Qed.

Lemma VF_nonzero' x : VF_normal x -> 0 < VF_denote x -> x <> Z.
Proof. intros _ H E. subst. simpl in H. apply (ord_lt_irreflexive 0); auto. Qed.

Lemma mpush_spec : forall L h e, nfL L -> VF_matrix_proper L -> posL L ->
  (forall b a, In (b,a) L -> VF_denote h ≤ VF_denote b) ->
  VF_normal h -> VF_normal e -> h <> Z -> e <> Z ->
  nfL (mpush L h e) /\ VF_matrix_proper (mpush L h e) /\ posL (mpush L h e) /\
  forall f x, normal_function f -> complete x ->
    schutte_matrix f (md (mpush L h e)) x ≈ schutte_column (schutte_matrix f (md L)) (VF_denote h) (VF_denote e) x.
Proof.
  induction L as [|[b a] L IH]; intros h e HnfL HprL HposL Hge Hh He Hh0 He0.
  - simpl. split; [ unfold nfL in *; simpl in *; intuition | split; [ simpl; split; [ apply VF_normal_proper; auto | split; auto; apply VF_normal_proper; auto ] | split ] ].
    + intros b a [E|[]]. inversion E; subst. auto.
    + intros. reflexivity.
  - destruct HnfL as [[Hb Ha] HnfL]. simpl fst in Hb. simpl snd in Ha.
    destruct (HposL b a (or_introl eq_refl)) as [Hb0 Ha0].
    assert (Hpos' : posL L) by (intros b' a' Hin; apply HposL; right; auto).
    destruct L as [|c2 L].
    + (* a single column *)
      simpl mpush. assert (Hc := cmp_spec b h Hb Hh).
      assert (Hhb : VF_denote h ≤ VF_denote b) by (apply (Hge b a); left; auto).
      destruct (VF_compare b h) eqn:Ebh.
      * elim (ord_lt_irreflexive (VF_denote b)). eapply ord_lt_le_trans; eauto.
      * assert (E := cmp_eq b h Hb Hh Ebh). subst h.
        destruct (add_reflect a e Ha He) as [Eae Nae].
        assert (Hae0 : VF_add a e <> Z).
        { apply VF_nonzero'; auto. rewrite Eae. eapply ord_lt_le_trans; [ apply (proj2 (VF_nonzero a)); auto | apply addOrd_le1 ]. }
        split; [ unfold nfL in *; simpl in *; intuition | split; [ simpl; split; [ apply VF_normal_proper; auto | split; auto; apply VF_normal_proper; auto ] | split ] ].
        -- intros b' a' [E|[]]. inversion E; subst. auto.
        -- intros f x Hf Hx. simpl.
           transitivity (schutte_column f (VF_denote b) (VF_denote a + VF_denote e) x).
           ++ split; apply schutte_column_monotone; auto; try apply Eae; reflexivity.
           ++ symmetry. apply schutte_column_merge; auto.
      * split; [ unfold nfL in *; simpl in *; intuition | split; [ simpl; split; [ apply VF_normal_proper; auto | split; [ apply VF_normal_proper; auto | split; [ exact Hc | ] ] ] | split ] ].
        -- simpl. split; [ apply VF_normal_proper; auto | split; auto; apply VF_normal_proper; auto ].
        -- intros b' a' [E|[E|[]]]; inversion E; subst; auto.
        -- intros. reflexivity.
    + (* at least two columns: keep the first *)
      assert (HprL' : VF_matrix_proper (c2::L)) by (destruct c2; simpl in HprL |- *; tauto).
      destruct (IH h e HnfL HprL' Hpos') as [Hnf' [Hpr' [Hpo' Hsem]]]; auto.
      { intros b' a' Hin. apply (Hge b' a'). right; auto. }
      destruct (mpush_head c2 L h e) as [a2 [L2 E2]].
      change (mpush ((b,a)::c2::L) h e) with ((b,a) :: mpush (c2::L) h e).
      split; [ unfold nfL in *; simpl in *; intuition | split; [ | split ] ].
      * rewrite E2 in Hpr' |- *. simpl. split; [ apply VF_normal_proper; auto | split; [ apply VF_normal_proper; auto | split ] ].
        -- destruct c2 as [b2 a2']. simpl in HprL |- *. tauto.
        -- exact Hpr'.
      * intros b' a' [E|Hin]; [ inversion E; subst; auto | apply Hpo'; auto ].
      * intros f x Hf Hx. simpl. apply Hsem; auto. apply schutte_column_normal; auto.
Qed.

Lemma In_md_intro b a L : In (b,a) L -> In (VF_denote b, VF_denote a) (md L).
Proof. intro H. unfold md, matrix_denote. apply in_map_iff. exists (b,a). auto. Qed.

(** Splitting off the suffix of columns lower than h. *)
Fixpoint split_lower (h:VForm) (L:list (VForm*VForm)) : list (VForm*VForm) * list (VForm*VForm) :=
  match L with
  | [] => ([], [])
  | (b,a)::L' =>
    match VF_compare b h with
    | LT => ([], L)
    | _ => let (k,p) := split_lower h L' in ((b,a)::k, p)
    end
  end.

Lemma split_lower_spec : forall L h, nfL L -> VF_matrix_proper L -> VF_normal h ->
  let (k,p) := split_lower h L in
  L = k ++ p /\ (forall b a, In (b,a) k -> VF_denote h ≤ VF_denote b) /\
  (forall b a, In (b,a) p -> VF_denote b < VF_denote h).
Proof.
  induction L as [|[b a] L IH]; intros h HnfL HprL Hh; simpl.
  - split; [ auto | split; intros ? ? [] ].
  - destruct HnfL as [[Hb Ha] HnfL]. simpl in Hb.
    assert (HdL := proper_desc ((b,a)::L) HprL). simpl in HdL. destruct HdL as [Hbelow _].
    assert (Hc := cmp_spec b h Hb Hh).
    assert (HprL' : VF_matrix_proper L) by (destruct L as [|[??]?]; simpl in *; tauto).
    destruct (VF_compare b h); simpl in Hc.
    + split; [ auto | split; [ intros ? ? [] | ] ].
      intros b' a' [E|Hin]; [ inversion E; subst; auto | ].
      eapply ord_lt_trans; [ apply (Hbelow _ _ (In_md_intro b' a' L Hin)) | exact Hc ].
    + specialize (IH h HnfL HprL' Hh). destruct (split_lower h L) as [k p].
      destruct IH as [E [Hk Hp]]. subst L. split; [ auto | split; [ | auto ] ].
      intros b' a' [E|Hin]; [ inversion E; subst; apply Hc | apply (Hk b' a' Hin) ].
    + specialize (IH h HnfL HprL' Hh). destruct (split_lower h L) as [k p].
      destruct IH as [E [Hk Hp]]. subst L. split; [ auto | split; [ | auto ] ].
      intros b' a' [E|Hin]; [ inversion E; subst; apply ord_lt_le; auto | apply (Hk b' a' Hin) ].
Qed.

(** * Small facts used by the step *)

Lemma col_base_eq F G β α x : normal_function F -> normal_function G ->
  (forall y, complete y -> F y ≈ G y) -> complete β -> complete α -> complete x ->
  schutte_column F β α x ≈ schutte_column G β α x.
Proof. intros. split; apply col_base_le; auto; intros; apply H1; auto. Qed.

Lemma col_height_eq f β β' α x : normal_function f -> β ≈ β' ->
  schutte_column f β α x ≈ schutte_column f β' α x.
Proof. intros Hf E. split; apply schutte_column_monotoneβ; auto; apply E. Qed.

Lemma MX_snoc L b a x : MX (L ++ [(b,a)]) x = schutte_column (MX L) (VF_denote b) (VF_denote a) x.
Proof. unfold MX. rewrite md_app, schutte_matrix_app. reflexivity. Qed.

Lemma MX_app L1 L2 x : MX (L1 ++ L2) x = schutte_matrix (MX L1) (md L2) x.
Proof. unfold MX. rewrite md_app, schutte_matrix_app. reflexivity. Qed.

Lemma proper_snoc0 : forall L T, VF_matrix_proper L -> posL L -> nfL L -> VF_normal T ->
  VF_matrix_proper (L ++ [(Z,T)]).
Proof.
  induction L as [|[b a] L IH]; intros T Hpr Hpos Hnf HT; simpl.
  - split; [ exact I | split; [ apply VF_normal_proper; auto | exact I ] ].
  - destruct Hnf as [[Hb Ha] Hnf]. simpl in Hb, Ha.
    assert (Hpos' : posL L) by (intros b' a' Hin; apply Hpos; right; auto).
    split; [ apply VF_normal_proper; auto | split; [ apply VF_normal_proper; auto | ] ].
    destruct L as [|[b2 a2] L].
    + simpl. split; [ | split; [ exact I | split; [ apply VF_normal_proper; auto | exact I ] ] ].
      destruct (Hpos b a (or_introl eq_refl)) as [Hb0 _]. apply VF_nonzero; auto.
    + simpl in Hpr. destruct Hpr as [_ [_ [Hlt Hpr]]].
      change (((b2, a2) :: L) ++ [(Z, T)]) with ((b2,a2) :: (L ++ [(Z,T)])).
      split; [ exact Hlt | ]. apply IH; auto.
Qed.

Lemma pos_ge1 b : VF_normal b -> b <> Z -> 1 ≤ VF_denote b.
Proof. intros Hb H. apply succ_least. apply VF_nonzero; auto. Qed.

(** Matrices of height at most 1 over 1 + y are translations. *)
Lemma low_shape a0 : VF_normal a0 -> forall w, complete w ->
  MX [(VF_one, a0)] w ≈ expOrd ω (VF_denote a0) + w.
Proof.
  intros Ha0 w Hw. unfold MX. simpl.
  transitivity (schutte_column (addOrd 1) 1 (VF_denote a0) w).
  { apply col_height_eq; auto. apply VF_one_denote. }
  rewrite schutte_column_veblen; auto. apply veblen_onePlus; auto.
Qed.

Definition high (L:list (VForm*VForm)) : bool :=
  match L with
  | (b,_)::_ => match VF_compare b VF_one with GT => true | _ => false end
  | [] => false
  end.

Definition regime (h:VForm) (L:list (VForm*VForm)) : bool :=
  match VF_compare h VF_one with GT => true | _ => high L end.

(** * One step of the normalizer *)

Definition step (st : list (VForm*VForm) * VForm) (c : VForm*VForm) : list (VForm*VForm) * VForm :=
  let (L, T) := st in
  let (h, e) := c in
  match h with
  | Z => (L, VF_add T e)
  | N _ =>
    match e with
    | Z => (L, T)
    | N _ =>
      let (k, p) := split_lower h L in
      match p, T with
      | [], Z => (mpush L h e, Z)
      | _, _ =>
        if regime h L then
          let L' := mpush k h e in (L', VF_offset L' (vmax (T :: map snd p)))
        else ([(VF_one, VF_add (lead (VF_normalize (N (L ++ [(Z,T)])))) e)], Z)
      end
    end
  end.

Definition Good (st : list (VForm*VForm) * VForm) : Prop :=
  nfL (fst st) /\ VF_matrix_proper (fst st) /\ posL (fst st) /\ VF_normal (snd st).

Definition Sem (I:list (VForm*VForm)) (st : list (VForm*VForm) * VForm) : Prop :=
  forall x, complete x -> MX I x ≈ MX (fst st) (VF_denote (snd st) + x).

Lemma sem_base I L T : Sem I (L,T) -> forall y, complete y -> MX I y ≈ MX (L ++ [(Z,T)]) y.
Proof.
  intros H y Hy. unfold Sem in H. cbn [fst snd] in H. rewrite MX_snoc. rewrite H; auto. symmetry. apply schutte_column0.
Qed.

Lemma nfL_sub k p : nfL (k ++ p) -> nfL k /\ nfL p.
Proof. apply nfL_app. Qed.

Lemma posL_app k p : posL (k ++ p) -> posL k /\ posL p.
Proof. intro H. split; intros b a Hin; apply H; apply in_or_app; auto. Qed.

Lemma vmax_entries T p : VF_normal T -> nfL p ->
  let m := vmax (T :: map snd p) in
  VF_normal m /\
  forall z, (forall b a, In (b,a) (md (p ++ [(Z,T)])) -> a < z) <-> VF_denote m < z.
Proof.
  intros HT Hp. cbv zeta.
  assert (Hn : each VF_normal (T :: map snd p)).
  { simpl. split; auto. clear -Hp. unfold nfL in Hp. induction p as [|[b a] p IH]; simpl in *; intuition. }
  destruct (vmax_spec _ Hn) as [Hm [Hle [Hnil|Hin]]]; [ discriminate | ].
  split; [ exact Hm | ]. intro z. split.
  - intro H. destruct Hin as [E|Hin].
    + rewrite <- E. apply (H 0). rewrite md_app. apply in_or_app. right. left. reflexivity.
    + apply in_map_iff in Hin. destruct Hin as [[b a] [E Hin]]. cbn [snd] in E. rewrite <- E.
      apply (H (VF_denote b)). rewrite md_app. apply in_or_app. left. apply In_md_intro; auto.
  - clear Hin. intros H b a Hin. rewrite md_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|[]]].
    + destruct (In_md b a p Hin) as [b' [a' [Hin' [E1 E2]]]]. subst.
      eapply ord_le_lt_trans; [ | exact H ]. apply Hle. right. apply in_map_iff. exists (b',a'). auto.
    + inversion E; subst. eapply ord_le_lt_trans; [ | exact H ]. apply Hle. left; auto.
Qed.

Lemma no_low_pop L h p k : posL L -> nfL L -> L = k ++ p ->
  (forall b a, In (b,a) p -> VF_denote b < VF_denote h) -> VF_denote h ≤ 1 -> p = [].
Proof.
  intros Hpos Hnf E Hp Hh. destruct p as [|[b a] p]; auto. exfalso.
  assert (Hin : In (b,a) L) by (rewrite E; apply in_or_app; right; left; auto).
  destruct (Hpos b a Hin) as [Hb0 _]. destruct (In_nfL b a L Hnf Hin) as [Hb _].
  assert (H1 := pos_ge1 b Hb Hb0). assert (H2 := Hp b a (or_introl eq_refl)).
  apply (ord_lt_irreflexive 1). eapply ord_le_lt_trans; [ exact H1 | ]. eapply ord_lt_le_trans; eauto.
Qed.


Lemma high_Prin L : nfL L -> posL L -> high L = true -> Prin (MX L).
Proof.
  intros Hnf Hpos H. destruct L as [|[b0 a0] L']; simpl in H; [ discriminate | ].
  destruct Hnf as [[Hb0 _] _]. simpl in Hb0.
  assert (Hc := cmp_spec b0 VF_one Hb0 VF_one_normal).
  destruct (VF_compare b0 VF_one) eqn:E; try discriminate. simpl in Hc.
  unfold MX. apply Prin_matrix; auto. right. exists (VF_denote b0), (VF_denote a0).
  split; [ left; reflexivity | split ].
  - eapply ord_le_lt_trans; [ apply VF_one_denote | exact Hc ].
  - destruct (Hpos b0 a0 (or_introl eq_refl)). apply VF_nonzero; auto.
Qed.

Lemma VF_le_one h : VF_normal h -> VF_compare h VF_one <> GT -> VF_denote h ≤ 1.
Proof.
  intros Hh H. assert (Hc := cmp_spec h VF_one Hh VF_one_normal).
  destruct (VF_compare h VF_one); simpl in Hc.
  - rewrite <- VF_one_denote. apply ord_lt_le; auto.
  - rewrite <- VF_one_denote. apply Hc.
  - contradiction.
Qed.

Lemma VF_is_one h : VF_normal h -> h <> Z -> VF_compare h VF_one <> GT -> h = VF_one.
Proof.
  intros Hh H0 H. apply VF_normal_form_unique; auto using VF_one_normal.
  rewrite VF_one_denote. split; [ apply VF_le_one; auto | apply pos_ge1; auto ].
Qed.


Lemma low_step L T e : nfL L -> VF_matrix_proper L -> posL L -> VF_normal T -> T <> Z ->
  VF_normal e -> e <> Z -> (L = [] \/ exists a0, L = [(VF_one, a0)]) ->
  let d := VF_normalize (N (L ++ [(Z,T)])) in
  Good ([(VF_one, VF_add (lead d) e)], Z) /\
  forall x, complete x ->
    schutte_column (MX (L ++ [(Z,T)])) 1 (VF_denote e) x ≈ MX [(VF_one, VF_add (lead d) e)] (0 + x).
Proof.
  intros HnfL HprL HposL HT HT0 He He0 Hshape d.
  assert (Hω : complete ω) by apply omega_complete.
  assert (Hpr : VF_proper (N (L ++ [(Z,T)]))) by (rewrite VF_proper_eq; apply proper_snoc0; auto).
  destruct (VF_normalize_correct _ Hpr) as [Ed Nd]. fold d in Ed, Nd.
  (* the base is a translation y ↦ c0 + y *)
  assert (Hc0 : exists c0, complete c0 /\ forall w, complete w -> MX L w ≈ c0 + w).
  { destruct Hshape as [E|[a0 E]]; subst L.
    - exists 1. split; [ apply succ_complete; auto | ]. intros w Hw. reflexivity.
    - destruct HnfL as [[_ Ha0] _]. simpl in Ha0.
      exists (expOrd ω (VF_denote a0)). split; [ apply expOrd_complete; auto using omega_gt0 | ].
      apply low_shape; auto. }
  destruct Hc0 as [c0 [Hc0c Hc0]].
  set (D := VF_denote d).
  assert (HD : complete D) by (unfold D; auto).
  assert (EB : forall y, complete y -> MX (L ++ [(Z,T)]) y ≈ D + y).
  { intros y Hy. rewrite MX_snoc. change (VF_denote Z) with 0. rewrite schutte_column0.
    rewrite Hc0; auto. unfold D. rewrite Ed. rewrite VF_denote_N, MX_snoc. change (VF_denote Z) with 0.
    rewrite schutte_column0. rewrite Hc0; auto. rewrite addOrd_zero_r. apply addOrd_assoc. }
  assert (HD0 : 0 < D).
  { unfold D. rewrite Ed. rewrite VF_denote_N. apply normal_nonzero; auto. }
  destruct (lead_spec d Nd HD0) as [Nl [Hl1 Hl2]].
  destruct (add_reflect (lead d) e Nl He) as [Ele Nle].
  set (le := VF_add (lead d) e) in *.
  assert (He' : 0 < VF_denote e) by (apply VF_nonzero; auto).
  split.
  - split; [ unfold nfL; simpl; repeat split; auto using VF_one_normal | split; [ | split; [ | exact I ] ] ].
    + simpl. repeat split; try apply VF_normal_proper; auto using VF_one_normal.
    + intros b a [E|[]]. inversion E; subst. split; [ discriminate | ].
      apply VF_nonzero'; auto. rewrite Ele. eapply ord_lt_le_trans; [ exact He' | apply addOrd_le2 ].
  - intros x Hx.
    transitivity (schutte_column (addOrd D) 1 (VF_denote e) x).
    { apply col_base_eq; auto. apply normal_addOrd; auto. }
    rewrite schutte_column_veblen; auto; [ | apply normal_addOrd; auto ].
    rewrite (low_regime_veblen (VF_denote e) x D (VF_denote (lead d))); auto.
    unfold MX. simpl.
    transitivity (schutte_column (addOrd 1) 1 (VF_denote le) x).
    2: { split; apply schutte_column_monotone_full; auto; try apply VF_one_denote; try apply addOrd_le2;
         try reflexivity. rewrite addOrd_zero_l. reflexivity. }
    rewrite schutte_column_veblen; auto. rewrite veblen_onePlus; auto.
    apply addOrd_eq_mor; [ | reflexivity ].
    split; apply expOrd_monotone; apply Ele.
Qed.

Lemma low_shape_of L : nfL L -> VF_matrix_proper L -> posL L -> high L = false ->
  L = [] \/ exists a0, L = [(VF_one, a0)].
Proof.
  intros Hnf Hpr Hpos Hhi. destruct L as [|[b0 a0] L']; [ left; auto | right ].
  destruct Hnf as [[Hb0 _] Hnf']. simpl in Hb0.
  assert (Hng : VF_compare b0 VF_one <> GT) by (intro E; simpl in Hhi; rewrite E in Hhi; discriminate).
  destruct (Hpos b0 a0 (or_introl eq_refl)) as [Hb00 _].
  assert (E := VF_is_one b0 Hb0 Hb00 Hng). subst b0.
  exists a0. destruct L' as [|[b1 a1] L'']; auto. exfalso.
  simpl in Hpr. destruct Hpr as [_ [_ [Hlt _]]].
  destruct (Hpos b1 a1 (or_intror (or_introl eq_refl))) as [Hb10 _].
  destruct Hnf' as [[Hb1 _] _]. simpl in Hb1.
  apply (ord_lt_irreflexive 1). eapply ord_le_lt_trans; [ apply (pos_ge1 b1); auto | ].
  eapply ord_lt_le_trans; [ exact Hlt | apply VF_one_denote ].
Qed.

Theorem step_correct I L T h e : Good (L,T) -> Sem I (L,T) -> VF_normal h -> VF_normal e ->
  Good (step (L,T) (h,e)) /\ Sem (I ++ [(h,e)]) (step (L,T) (h,e)).
Proof.
  intros HG HS Hh He. destruct HG as [HnfL [HprL [HposL HT]]]. cbn [fst snd] in HnfL, HprL, HposL, HT.
  assert (HB := sem_base I L T HS). unfold Sem in HS. cbn [fst snd] in HS.
  destruct h as [|hl]; [ | destruct e as [|el] ].
  - (* a height-0 column adds to the pending shift *)
    destruct (add_reflect T e HT He) as [Ete Nte].
    simpl step. split; [ split; [ exact HnfL | split; [ exact HprL | split; [ exact HposL | exact Nte ] ] ] | ].
    unfold Sem; cbn [fst snd]; intros x Hx. rewrite MX_snoc. simpl VF_denote at 1.
    rewrite schutte_column0. rewrite HS; auto.
    apply normal_eq; auto. rewrite Ete. apply addOrd_assoc.
  - (* zero entry *)
    simpl step. split; [ split; [ exact HnfL | split; [ exact HprL | split; [ exact HposL | exact HT ] ] ] | ].
    unfold Sem; cbn [fst snd]; intros x Hx. rewrite MX_snoc. simpl VF_denote at 2.
    rewrite schutte_column_arg0; auto.
  - set (h := N hl) in *. set (e := N el) in *.
    assert (Hh0 : h <> Z) by discriminate. assert (He0 : e <> Z) by discriminate.
    assert (Hhp : 0 < VF_denote h) by (apply VF_nonzero; auto).
    assert (Hep : 0 < VF_denote e) by (apply VF_nonzero; auto).
    assert (Hsem0 : forall x, complete x ->
              MX (I ++ [(h,e)]) x ≈ schutte_column (MX (L ++ [(Z,T)])) (VF_denote h) (VF_denote e) x).
    { unfold Sem; cbn [fst snd]; intros x Hx. rewrite MX_snoc. apply col_base_eq; auto. }
    change (step (L,T) (h,e)) with
      (let (k, p) := split_lower h L in
       match p, T with
       | [], Z => (mpush L h e, Z)
       | _, _ =>
         if regime h L then
           let L' := mpush k h e in (L', VF_offset L' (vmax (T :: map snd p)))
         else ([(VF_one, VF_add (lead (VF_normalize (N (L ++ [(Z,T)])))) e)], Z)
       end).
    clearbody h e.
    assert (Hsp := split_lower_spec L h HnfL HprL Hh).
    destruct (split_lower h L) as [k p]. destruct Hsp as [EL [Hk Hp]].
    assert (Hk' := nfL_sub k p). rewrite <- EL in Hk'. destruct (Hk' HnfL) as [Hnfk Hnfp].
    destruct (posL_app k p) as [Hposk Hposp]; [ rewrite <- EL; auto | ].
    assert (Hprk : VF_matrix_proper k) by (apply VF_matrix_proper_app with p; rewrite <- EL; auto).
    (* the principal-regime outcome, shared by two branches *)
    assert (Hprincipal : Reg (MX k) (VF_denote h) ->
      Good (mpush k h e, VF_offset (mpush k h e) (vmax (T :: map snd p))) /\
      Sem (I ++ [(h,e)]) (mpush k h e, VF_offset (mpush k h e) (vmax (T :: map snd p)))).
    { intro Hreg.
      destruct (mpush_spec k h e Hnfk Hprk Hposk Hk Hh He Hh0 He0) as [Hnf' [Hpr' [Hpos' Hsem']]].
      set (L' := mpush k h e) in *.
      destruct (vmax_entries T p HT Hnfp) as [Hm Hmax]. set (m := vmax (T :: map snd p)) in *.
      destruct (VF_offset_correct L' Hnf' Hpr' Hpos' m Hm) as [Hs [Hs1 Hs2]].
      set (s := VF_offset L' m) in *.
      split; [ split; [ auto | split; [ auto | split; auto ] ] | ].
      unfold Sem; cbn [fst snd]; intros x Hx. rewrite Hsem0; auto.
      assert (EM : forall y, complete y -> MX (L ++ [(Z,T)]) y = schutte_matrix (MX k) (md (p ++ [(Z,T)])) y).
      { intros y Hy. rewrite EL, <- app_assoc. apply MX_app. }
      transitivity (schutte_column (schutte_matrix (MX k) (md (p ++ [(Z,T)]))) (VF_denote h) (VF_denote e) x).
      { apply col_base_eq; auto. intros y Hy. rewrite EM; auto. reflexivity. }
      rewrite (absorb_shift_list (MX k) (md (p ++ [(Z,T)])) (VF_denote h) (VF_denote e) (VF_denote m) (VF_denote s)); auto.
      - symmetry. apply Hsem'; auto.
      - intros b a Hin. rewrite md_app in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[E|[]]].
        + destruct (In_md b a p Hin) as [b' [a' [Hin' [E1 E2]]]]. subst. apply Hp with a'; auto.
        + inversion E; subst. exact Hhp.
      - eapply ord_lt_le_trans; [ exact Hs1 | ]. apply Hsem'; auto.
      - intros y Hy. rewrite ord_lt_unfold in Hy. destruct Hy as [i Hi].
        transitivity (schutte_column (MX k) (VF_denote h) (VF_denote e) (VF_denote s i)).
        { apply schutte_column_monotone; auto. }
        rewrite <- (Hsem' (addOrd 1) (VF_denote s i)); auto. apply Hs2. apply index_lt. }
    destruct p as [|c p'] eqn:Ep; [ destruct T as [|Tl] | ].
    + (* nothing absorbed *)
      rewrite app_nil_r in EL. subst k.
      destruct (mpush_spec L h e HnfL HprL HposL Hk Hh He Hh0 He0) as [Hnf' [Hpr' [Hpos' Hsem']]].
      split; [ split; [ auto | split; [ auto | split; auto ] ] | ].
      unfold Sem; cbn [fst snd]; intros x Hx. rewrite Hsem0; auto.
      transitivity (MX (mpush L h e) x).
      * unfold MX at 2. rewrite Hsem'; auto. apply col_base_eq; auto. intros y Hy.
        rewrite MX_snoc. change (VF_denote Z) with 0. rewrite schutte_column0. apply normal_eq; auto. apply addOrd_zero_l.
      * apply normal_eq; auto. change (VF_denote Z) with 0. symmetry. apply addOrd_zero_l.
    + (* only the pending shift is absorbed *)
      rewrite app_nil_r in EL. subst k.
      destruct (regime h L) eqn:Er.
      * apply Hprincipal. unfold regime in Er.
        assert (Hc := cmp_spec h VF_one Hh VF_one_normal).
        destruct (VF_compare h VF_one) eqn:Eh1; cbn [ordering_correct] in Hc.
        -- left. apply high_Prin; auto.
        -- left. apply high_Prin; auto.
        -- right. eapply ord_le_lt_trans; [ apply VF_one_denote | exact Hc ].
      * (* the low regime *)
        assert (Hng : VF_compare h VF_one <> GT) by (intro E; unfold regime in Er; rewrite E in Er; discriminate).
        assert (Hhi : high L = false).
        { unfold regime in Er. destruct (VF_compare h VF_one); [ exact Er | exact Er | contradiction ]. }
        assert (Eh := VF_is_one h Hh Hh0 Hng). subst h.
        assert (Hshape := low_shape_of L HnfL HprL HposL Hhi).
        destruct (low_step L (N Tl) e HnfL HprL HposL HT ltac:(discriminate) He He0 Hshape) as [Hg Hs].
        split; [ exact Hg | ].
        unfold Sem; cbn [fst snd]; intros x Hx. rewrite Hsem0; auto.
        transitivity (schutte_column (MX (L ++ [(Z,N Tl)])) 1 (VF_denote e) x); [ apply col_height_eq; auto; apply VF_one_denote | ].
        rewrite Hs; auto. reflexivity.
    + (* some columns are popped: the height is at least 2 *)
      assert (Hh1 : VF_compare h VF_one = GT).
      { destruct (VF_compare h VF_one) eqn:E; auto; exfalso;
          assert (Hp0 := no_low_pop L h (c::p') k HposL HnfL EL Hp (VF_le_one h Hh ltac:(rewrite E; discriminate)));
          discriminate. }
      assert (Er : regime h L = true) by (unfold regime; rewrite Hh1; reflexivity).
      rewrite Er. apply Hprincipal. right.
      assert (Hc := cmp_spec h VF_one Hh VF_one_normal). rewrite Hh1 in Hc.
      eapply ord_le_lt_trans; [ apply VF_one_denote | exact Hc ].
Qed.

(** * The normalizer *)

Definition process (I : list (VForm*VForm)) : list (VForm*VForm) * VForm := fold_left step I ([], Z).

Theorem process_correct : forall I, nfL I -> Good (process I) /\ Sem I (process I).
Proof.
  induction I as [|c I IH] using rev_ind; intro HI.
  - split; [ unfold Good; simpl; repeat split; auto; intros ? ? [] | ].
    unfold Sem. simpl. intros x Hx. unfold MX. simpl. apply addOrd_eq_mor; [ reflexivity | ].
    symmetry. apply addOrd_zero_l.
  - apply nfL_app in HI. destruct HI as [HI [[Hh He] _]].
    unfold process. rewrite fold_left_app. simpl. fold (process I).
    destruct (IH HI) as [HG HS]. destruct (process I) as [L T]. destruct c as [h e].
    apply step_correct; auto.
Qed.

Fixpoint VF_normalizeX (x:VForm) : VForm :=
  match x with
  | Z => Z
  | N l =>
    let st := process (map (fun c => (VF_normalizeX (fst c), VF_normalizeX (snd c))) l) in
    Nnorm (fst st ++ [(Z, snd st)])
  end.

Lemma matrix_entries_eq : forall xs ys f g y,
  normal_function f -> normal_function g -> (forall w, complete w -> f w ≈ g w) -> complete y ->
  Forall2 (fun c d => VF_denote (fst c) ≈ VF_denote (fst d) /\ VF_denote (snd c) ≈ VF_denote (snd d)) xs ys ->
  schutte_matrix f (md xs) y ≈ schutte_matrix g (md ys) y.
Proof.
  intros xs ys f g y Hf Hg Hfg Hy H. revert f g Hf Hg Hfg.
  induction H as [|[b a] [b' a'] xs ys [Eb Ea] H IH]; intros f g Hf Hg Hfg; simpl; auto.
  apply IH; auto.
  - apply schutte_column_normal; auto.
  - apply schutte_column_normal; auto.
  - intros w Hw. transitivity (schutte_column g (VF_denote b) (VF_denote a) w).
    + apply col_base_eq; auto.
    + split; apply schutte_column_monotone_full; auto; try apply Eb; try apply Ea; reflexivity.
Qed.

Theorem VF_normalizeX_correct : forall x,
  VF_denote (VF_normalizeX x) ≈ VF_denote x /\ VF_normal (VF_normalizeX x).
Proof.
  induction x as [|xs Hxs] using VForm_induction.
  - simpl. split; [ reflexivity | exact I ].
  - set (l' := map (fun c => (VF_normalizeX (fst c), VF_normalizeX (snd c))) xs).
    assert (Hnf : nfL l').
    { unfold l', nfL. clear -Hxs. induction xs as [|[b a] xs IH]; simpl in *; intuition. }
    assert (Heq : Forall2 (fun c d => VF_denote (fst c) ≈ VF_denote (fst d) /\ VF_denote (snd c) ≈ VF_denote (snd d)) l' xs).
    { unfold l'. clear -Hxs. induction xs as [|[b a] xs IH]; simpl in *; constructor; intuition. }
    destruct (process_correct l' Hnf) as [HG HS].
    change (VF_normalizeX (N xs)) with (Nnorm (fst (process l') ++ [(Z, snd (process l'))])).
    destruct (process l') as [L T]. unfold Good in HG. unfold Sem in HS. cbn [fst snd] in HG, HS |- *.
    destruct HG as [HnfL [HprL [HposL HT]]].
    assert (Hpr := proper_snoc0 L T HprL HposL HnfL HT).
    split.
    + rewrite Nnorm_eq; auto. rewrite !VF_denote_N. rewrite MX_snoc. change (VF_denote Z) with 0.
      rewrite schutte_column0.
      transitivity (MX l' 0).
      * rewrite HS; auto. reflexivity.
      * unfold MX. apply matrix_entries_eq; auto. intros; reflexivity.
    + apply Nnorm_normal; auto. apply nfL_app. split; auto. unfold nfL. simpl. auto.
Qed.

(** On proper matrices it agrees with [VF_normalize], and normal forms are fixed. *)
Corollary VF_normalizeX_proper x : VF_proper x -> VF_normalizeX x = VF_normalize x.
Proof.
  intro Hx. destruct (VF_normalizeX_correct x) as [E1 N1]. destruct (VF_normalize_correct x Hx) as [E2 N2].
  apply VF_normal_form_unique; auto. rewrite E1, E2. reflexivity.
Qed.

Corollary VF_normalizeX_normal x : VF_normal x -> VF_normalizeX x = x.
Proof.
  intro Hx. destruct (VF_normalizeX_correct x) as [E N1]. apply VF_normal_form_unique; auto.
Qed.

(** ** Examples, by computation *)

Definition VF_Γ0 := N [(VF_two, VF_one)].

(** [(0,1),(1,1)]: the first fixpoint of 2 + y is ω. *)
Example nx_low : VF_normalizeX (N [(Z, VF_one); (VF_one, VF_one)]) = VF_omega.
Proof. vm_compute. reflexivity. Qed.

(** [(1,1),(2,1)]: the column (1,1) is absorbed; Γ₀ > ω, so no shift. *)
Example nx_absorb : VF_normalizeX (N [(VF_one, VF_one); (VF_two, VF_one)]) = VF_Γ0.
Proof. vm_compute. reflexivity. Qed.

(** [(0,Γ₀),(2,1)] and [(1,Γ₀),(2,1)]: the first Γ-number above Γ₀ is Γ₁. *)
Example nx_shift0 : VF_normalizeX (N [(Z, VF_Γ0); (VF_two, VF_one)]) = N [(VF_two, VF_one); (Z, VF_one)].
Proof. vm_compute. reflexivity. Qed.

Example nx_shift1 : VF_normalizeX (N [(VF_one, VF_Γ0); (VF_two, VF_one)]) = N [(VF_two, VF_one); (Z, VF_one)].
Proof. vm_compute. reflexivity. Qed.

(** Equal heights merge. *)
Example nx_merge : VF_normalizeX (N [(VF_two, VF_one); (VF_two, VF_one)]) = N [(VF_two, VF_two)].
Proof. vm_compute. reflexivity. Qed.

(** [(1,ω),(0,1),(1,1)]: φ over y ↦ ω^ω + 1 + y gives ω^(ω+1). *)
Example nx_low2 : VF_normalizeX (N [(VF_one, VF_omega); (Z, VF_one); (VF_one, VF_one)]) =
                  N [(VF_one, N [(VF_one, VF_one); (Z, VF_one)])].
Proof. vm_compute. reflexivity. Qed.
