From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.

Import ListNotations.

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
From Ordinal Require Import BachmannCfe.
From Ordinal Require Import BachmannNormal.
From Ordinal Require Import BachmannAgree.
From Ordinal Require Import BachmannFacts.

Open Scope ord_scope.

(** * The enumerator: interpolation, change of base, merges, shifted enumerations

Facts about @cfe@ and @bphi@ used by the notation system: every value
lies below a word of components, enumerators for different bases are
comparable, equal exponents merge, and an enumeration cut off above a
threshold is a shifted enumeration. *)

(** ** Interpolation for the common-fixpoint enumerator

Everything below a value @cfe y@ lies below f y, or below a finite
composition of f and the components ("a word") applied either to 0 or
to the successor of an earlier value @cfe (y j)@.  The starting points
lie below @cfe y@, and in the second case there is a component, so
@cfe y@ is a fixpoint of f and of every component; hence the whole
composition stays below @cfe y@.  This is the semantic half of
interpolation for notations built on @bphi@. *)

Section cfe_interp.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.
  Variable I : Type.
  Variable F : I -> Ord -> Ord.
  Hypothesis HF : forall i, normal_function (F i).

  Fixpoint wev (w:list (option I)) (x:Ord) : Ord :=
    match w with
    | [] => x
    | None :: w' => f (wev w' x)
    | Some i :: w' => F i (wev w' x)
    end.

  Lemma wev_monotone w : forall x y, x ≤ y -> wev w x ≤ wev w y.
  Proof.
    induction w as [|[i|] w IH]; simpl; auto.
    - intros. apply normal_monotone; auto.
    - intros. apply normal_monotone; auto.
  Qed.

  Lemma wev_complete w : forall x, complete x -> complete (wev w x).
  Proof.
    induction w as [|[i|] w IH]; simpl; auto.
    - intros. apply normal_complete; auto.
    - intros. apply normal_complete; auto.
  Qed.

  Lemma wev_continuous w : scott_continuous (wev w).
  Proof.
    intros A g a0 Hdir Hc.
    induction w as [|o w IH]; simpl; [ reflexivity | ].
    assert (Hdir' : directed A (fun a => wev w (g a))).
    { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
      exists a'. split; apply wev_monotone; auto. }
    assert (Hc' : forall a, complete (wev w (g a))) by (intro; apply wev_complete; auto).
    destruct o as [i|].
    - transitivity (F i (supOrd (fun a => wev w (g a)))); [ apply normal_monotone; auto | ].
      apply (normal_continuous _ (HF i) A _ a0 Hdir' Hc').
    - transitivity (f (supOrd (fun a => wev w (g a)))); [ apply normal_monotone; auto | ].
      apply (normal_continuous _ Hf A _ a0 Hdir' Hc').
  Qed.

  Lemma wev_app w1 w2 x : wev (w1 ++ w2) x = wev w1 (wev w2 x).
  Proof. induction w1 as [|[i|] w1 IH]; simpl; auto; rewrite IH; auto. Qed.

  Definition word (p:(I * list I)%type) : list (option I) :=
    Some (fst p) :: map Some (snd p) ++ [None].

  Lemma wev_comps L x : wev (map Some L ++ [None]) x = comps f I F L x.
  Proof. induction L as [|i L IH]; simpl; auto. rewrite IH; auto. Qed.

  Lemma wev_word p x : wev (word p) x = c1 f I F p x.
  Proof. unfold word, c1. simpl. rewrite wev_comps. reflexivity. Qed.

  Fixpoint iterw (p:(I * list I)%type) (k:nat) : list (option I) :=
    match k with
    | O => []
    | S k' => word p ++ iterw p k'
    end.

  Lemma wev_iterw p k x : wev (iterw p k) x = iter_f (c1 f I F p) x k.
  Proof.
    induction k as [|k IH]; [ reflexivity | ].
    change (wev (word p ++ iterw p k) x = c1 f I F p (iter_f (c1 f I F p) x k)).
    rewrite wev_app, IH, wev_word. reflexivity.
  Qed.

  Definition cstart (y:Ord) (o:option y) : Ord :=
    match o with
    | None => 0
    | Some j => succOrd (cfe f I F (y j))
    end.

  Theorem cfe_interp (y:Ord) i : complete y -> i < cfe f I F y ->
    i < f y \/
    (inhabited I /\ exists (o:option y) (w:list (option I)),
       i < wev w (cstart y o) /\ cstart y o ≤ cfe f I F y).
  Proof.
    intros Hy Hi.
    rewrite (cfe_unroll f I F y) in Hi.
    apply sup_lt in Hi. destruct Hi as [[p|] Hi]; simpl in Hi; [ right | left; auto ].
    split; [ exact (inhabits (fst p)) | ].
    set (s := limOrd (fun j => cfe f I F (y j))) in *.
    assert (Hsc : s ≤ cfe f I F y).
    { transitivity (fixOrd (c1 f I F p) s); [ apply fixOrd_above | ].
      apply (cfe_ge_term f I F y (Some p)). }
    unfold fixOrd in Hi. apply sup_lt in Hi. destruct Hi as [k Hk].
    rewrite <- wev_iterw in Hk.
    destruct y as [Y h]. destruct Hy as [Hdir [_ Hc]].
    assert (Hdir' : directed (option (ord Y h)) (cstart (ord Y h))).
    { intros [j1|] [j2|]; simpl.
      - destruct (Hdir j1 j2) as [j3 [H1 H2]]. exists (Some j3). simpl.
        split; apply succ_monotone, cfe_monotone; auto.
      - exists (Some j1). split; [ reflexivity | apply zero_least ].
      - exists (Some j2). split; [ apply zero_least | reflexivity ].
      - exists None. split; reflexivity. }
    assert (Hcs : forall o, complete (cstart (ord Y h) o)).
    { intros [j|]; simpl; [ apply succ_complete, cfe_complete; auto | apply zero_complete ]. }
    assert (Hs : s ≤ supOrd (cstart (ord Y h))).
    { apply limit_least. intro j.
      eapply ord_lt_le_trans; [ | apply (sup_le _ _ (Some j)) ].
      apply succ_lt. }
    assert (Hk' : i < supOrd (fun o => wev (iterw p k) (cstart (ord Y h) o))).
    { eapply ord_lt_le_trans; [ exact Hk | ].
      transitivity (wev (iterw p k) (supOrd (cstart (ord Y h)))); [ apply wev_monotone; auto | ].
      apply (wev_continuous (iterw p k) _ _ None Hdir' Hcs). }
    apply sup_lt in Hk'. destruct Hk' as [o Ho].
    exists o, (iterw p k). split; auto.
    destruct o as [j|]; simpl; [ | apply zero_least ].
    apply succ_least. eapply ord_lt_le_trans; [ | exact Hsc ].
    apply (limit_lt _ (fun j => cfe f I F (ord Y h j)) j).
  Qed.
End cfe_interp.

(** The same, for @bphi@: the components of a node are those of
    @bphi_fam@. *)
Lemma bphi_interp f (Hf : normal_function f) X y i : bgood f X -> complete y -> i < bphi f X y ->
  i < f y \/
  (inhabited (bsmall X + bbig X) /\
   exists (o:option y) (w:list (option (bsmall X + bbig X))),
     i < wev f _ (bphi_fam f (bsmallSz X) (bbigSz X)) w
           (match o with None => 0 | Some j => succOrd (bphi f X (y j)) end) /\
     match o with None => 0 | Some j => succOrd (bphi f X (y j)) end ≤ bphi f X y).
Proof.
  destruct X as [A g C h]. intros HX Hy Hi.
  exact (cfe_interp f Hf (A + C) (bphi_fam f g h) (bphi_fam_normal' f Hf A g C h HX) y i Hy Hi).
Qed.

(** Structural inclusion implies the index order. *)
Lemma bsub_ble : forall x y, bsub x y -> ble x y.
Proof.
  induction x as [A g IHg C h IHh]. intros [B g' D h'] [H1 H2].
  rewrite ble_unfold. intros [a|[c ξ]]; simpl; rewrite blt_unfold.
  - destruct (H1 a) as [b Hb]. exists (inl b). apply IHg; auto.
  - destruct (H2 c) as [d Hd]. exists (inr (d, ξ)). apply IHh; auto.
Qed.

Lemma bsub_child_blt x y i : bsub x (bchild y i) -> blt x y.
Proof. intro H. apply ble_lt_trans with (bchild y i); [ apply bsub_ble; auto | apply bindex_lt ]. Qed.

(** ** Changing the base: comparing two enumerators

@cfe f I F@ lies below @cfe f' J F'@ when f is dominated pointwise by f'
or by a component of the second family, and every component of the
first family by one of the second. *)

Section cfe_dom.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.
  Variable I : Type.
  Variable F : I -> Ord -> Ord.
  Hypothesis HF : forall i, normal_function (F i).
  Variable f' : Ord -> Ord.
  Hypothesis Hf' : normal_function f'.
  Variable J : Type.
  Variable F' : J -> Ord -> Ord.
  Hypothesis HF' : forall j, normal_function (F' j).

  Hypothesis H0 : forall x, complete x -> f x ≤ f' x \/ exists j, f x ≤ F' j x.
  Hypothesis H1 : forall i, exists j, forall x, complete x -> F i x ≤ F' j x.
  Hypothesis HJ : inhabited J \/ ~ inhabited I.

  Lemma cfe_dom_base y : complete y -> f y ≤ cfe f' J F' y.
  Proof.
    intro Hy. destruct (H0 y Hy) as [H|[j H]].
    - rewrite H. apply cfe_ge_f.
    - rewrite H. transitivity (F' j (cfe f' J F' y)).
      + apply normal_monotone; auto. apply cfe_inflationary; auto.
      + apply cfe_fix_F; auto.
  Qed.

  Theorem cfe_dom : forall y, complete y -> cfe f I F y ≤ cfe f' J F' y.
  Proof.
    destruct HJ as [[j0]|HnI].
    - induction y as [Y h IH]. intro Hy.
      assert (Hz : complete (cfe f' J F' (ord Y h))) by (apply cfe_complete; auto).
      assert (Hfz : f' (cfe f' J F' (ord Y h)) ≤ cfe f' J F' (ord Y h)) by (apply (cfe_fix_f f' Hf' J F' HF' j0); auto).
      apply (cfe_least f Hf I F HF).
      + apply cfe_dom_base; auto.
      + apply limit_least. intro a.
        assert (Ha : complete (h a)) by (apply (complete_subord (ord Y h)); auto).
        eapply ord_le_lt_trans; [ apply IH; auto | ].
        apply (cfe_increasing f' Hf' J F' HF' (or_introl (inhabits j0))); auto.
        apply (index_lt (ord Y h) a).
      + intro i. destruct (H1 i) as [j Hj]. split.
        * rewrite Hj; auto. apply cfe_fix_F; auto.
        * destruct (H0 _ Hz) as [H|[j' H]]; rewrite H; auto. apply cfe_fix_F; auto.
    - intros y Hy. rewrite (cfe_unroll f I F y). apply sup_least. intros [p|].
      + elim HnI. exact (inhabits (fst p)).
      + apply cfe_dom_base; auto.
  Qed.
End cfe_dom.

Lemma bphi_unfold f X : bphi f X = cfe f (bsmall X + bbig X) (bphi_fam f (bsmallSz X) (bbigSz X)).
Proof. destruct X; reflexivity. Qed.

Lemma bphi_fam_normal'' f (Hf : normal_function f) X : bgood f X ->
  forall k, normal_function (bphi_fam f (bsmallSz X) (bbigSz X) k).
Proof. destruct X. apply bphi_fam_normal'; auto. Qed.

Lemma bcd_good f (Hf : normal_function f) T : bcd T -> bgood f T.
Proof. intros [H1 H2]. apply (bcanon_good f Hf T H1 H2). Qed.

(** φ^{ω^x}_T lies below φ^{1+x}_{Ω+T}: the Ω-family of Ω+T supplies
    ξ ↦ ω^ξ, and the other children of Ω+T are Ω + (children of T). *)
Theorem bphi_powOmega_shift : forall T, bcd T -> forall y, complete y ->
  bphi powOmega T y ≤ bphi (addOrd 1) (badd bOmega T) y.
Proof.
  induction T as [A g IHg C h IHh]; intros HT y Hy.
  rewrite (bphi_unfold powOmega), (bphi_unfold (addOrd 1)).
  destruct (badd_big_l bOmega (bnode A g C h) tt) as [k0 Hk0].
  apply (cfe_dom powOmega powOmega_normal _ _ (bphi_fam_normal'' _ powOmega_normal _ (bcd_good _ powOmega_normal _ HT))
                 (addOrd 1) onePlus_normal _ _
                 (bphi_fam_normal'' _ onePlus_normal _ (bcd_good _ onePlus_normal _ (bcd_badd _ _ bcd_Ω HT)))); auto.
  - intros x Hx. right. exists (inr k0). cbn [bphi_fam]. rewrite Hk0.
    change (expOrd ω x ≤ bphi (addOrd 1) (embed x) 0).
    rewrite (bphi_onePlus_embed x 0 Hx zero_complete). apply addOrd_le1.
  - intros [a|c].
    + destruct (badd_small_r bOmega (bnode A g C h) a) as [k Hk].
      exists (inl k). intros x Hx. cbn [bphi_fam]. rewrite Hk. apply IHg; auto. apply (bcd_small _ a HT).
    + destruct (badd_big_r bOmega (bnode A g C h) c) as [k Hk].
      exists (inr k). intros x Hx. cbn [bphi_fam]. rewrite Hk. apply IHh; auto using zero_complete.
      apply (bcd_big _ c x HT Hx).
Qed.

(** φ^{1+x}_T lies below φ^{ω^x}_T. *)
Theorem bphi_base_mono : forall T, bcd T -> forall y, complete y ->
  bphi (addOrd 1) T y ≤ bphi powOmega T y.
Proof.
  induction T as [A g IHg C h IHh]; intros HT y Hy.
  rewrite (bphi_unfold (addOrd 1)), (bphi_unfold powOmega).
  apply (cfe_dom (addOrd 1) onePlus_normal _ _ (bphi_fam_normal'' _ onePlus_normal _ (bcd_good _ onePlus_normal _ HT))
                 powOmega powOmega_normal _ _
                 (bphi_fam_normal'' _ powOmega_normal _ (bcd_good _ powOmega_normal _ HT))); auto.
  - intros x Hx. left. apply onePlus_least_normal; auto. apply powOmega_normal.
  - intros [a|c]; exists (inl a) || exists (inr c); intros x Hx; simpl.
    + apply IHg; auto. apply (bcd_small _ a HT).
    + apply IHh; auto using zero_complete. apply (bcd_big _ c x HT Hx).
  - destruct HT as [_ [Hd _]]. simpl in Hd. destruct Hd as [H|H]; [ left | right ]; auto.
Qed.

(** Ω + tower n lies z-reachably below tower (n+2). *)
Lemma Ω_le_bexp Y (a:bsmall Y) : bsub bOmega (bexpΩ Y).
Proof.
  apply bsub_intro; [ intros [] | intros [] ].
  destruct (bexpΩ_fam_s Y a) as [t Ht]. exists t. intro ξ. rewrite Ht.
  apply embed_le_mul, bexpΩ_small_zero.
Qed.

Lemma btower_small n : bsmall (btower n).
Proof.
  destruct n as [|n]; [ exact tt | ].
  simpl. destruct (btower n). exact (inl tt).
Defined.

Lemma zlt_Ω_tower n z : oinf z -> zlt z (badd bOmega (btower n)) (btower (S (S n))).
Proof.
  intro Hz.
  destruct (tower_rel n z Hz) as [D [H1 H2]].
  assert (Hl : zlt z (btower n) (btower (S n))) by (exists D; auto).
  apply zlt_bleZ with (bmul (btower (S n)) (embed z)); [ | apply zlt_exp; auto ].
  apply zlt_mono_r with (badd bOmega (btower (S n))); [ apply zlt_shift; auto | ].
  set (X := btower (S n)).
  apply bsub_trans with (badd X X).
  { apply bsub_badd_l. apply (Ω_le_bexp (btower n) (btower_small n)). }
  apply bsub_trans with (badd (bmul X (embed 1)) X).
  { apply bsub_badd_l. apply bsub_bmul_one. }
  eapply bsub_trans; [ apply bsub_mul_succ | ].
  apply bsub_bmul_r, bsub_embed. apply (Hz 2%nat).
Qed.

(** ** Merging equal exponents

Improper indices with equal adjacent exponents normalize up to
@bequiv@: sums of embedded ordinals are embeddings of sums, and
multiplication distributes over addition on the left. *)

(** The children of a + b are those of a, and a + (children of b). *)
Lemma bequiv_embed_add : forall b a, bequiv (embed (a + b)) (badd (embed a) (embed b)).
Proof.
  induction b as [B k IH]. intros [A g].
  rewrite addOrd_unfold.
  split; apply bsub_intro.
  - intros [x|[i []]].
    + exists (inl x). apply bsub_refl.
    + exists (inr i). apply (proj1 (IH i (ord A g))).
  - intros [].
  - intros [x|i].
    + exists (inl x). apply bsub_refl.
    + exists (inr (existT _ i tt)). apply (proj2 (IH i (ord A g))).
  - intros [[]|[]].
Qed.

Lemma bsub_badd_intro A B Z : bsub A Z ->
  (forall b, exists t, bsub (badd A (bsmallSz B b)) (bsmallSz Z t)) ->
  (forall d, exists t, forall ξ, bsub (badd A (bbigSz B d ξ)) (bbigSz Z t ξ)) ->
  bsub (badd A B) Z.
Proof.
  intros H1 H2 H3. apply bsub_intro.
  - intro a. destruct (badd_small_cases A B a) as [[a' E]|[b E]]; rewrite E; auto.
    apply (bsub_small _ _ H1 a').
  - intro c. destruct (badd_big_cases A B c) as [[c' E]|[d E]].
    + destruct (bsub_big _ _ H1 c') as [t Ht]. exists t. intro ξ. rewrite E. auto.
    + destruct (H3 d) as [t Ht]. exists t. intro ξ. rewrite E. auto.
Qed.

Lemma bmul_small_cases P Y t : exists q s, bsmallSz (bmul P Y) t = bsmallSz (badd (bmul P (bsmallSz Y q)) P) s.
Proof. destruct Y as [B g D h]. destruct t as [[q s]|[]]. exists q, s. reflexivity. Qed.

Lemma bmul_big_cases P Y t :
  (exists q s, forall ξ, bbigSz (bmul P Y) t ξ = bbigSz (badd (bmul P (bsmallSz Y q)) P) s ξ) \/
  (exists d, forall ξ, bbigSz (bmul P Y) t ξ = bmul P (bbigSz Y d ξ)).
Proof.
  destruct Y as [B g D h]. destruct t as [[q s]|d].
  - left. exists q, s. reflexivity.
  - right. exists d. reflexivity.
Qed.

Lemma bsub_bmul_intro P Y Z :
  (forall q, bsub (badd (bmul P (bsmallSz Y q)) P) Z) ->
  (forall d, exists t, forall ξ, bsub (bmul P (bbigSz Y d ξ)) (bbigSz Z t ξ)) ->
  bsub (bmul P Y) Z.
Proof.
  intros H1 H2. apply bsub_intro.
  - intro a. destruct (bmul_small_cases P Y a) as [q [s E]]. rewrite E.
    apply (bsub_small _ _ (H1 q) s).
  - intro c. destruct (bmul_big_cases P Y c) as [[q [s E]]|[d E]].
    + destruct (bsub_big _ _ (H1 q) s) as [t Ht]. exists t. intro ξ. rewrite E. auto.
    + destruct (H2 d) as [t Ht]. exists t. intro ξ. rewrite E. auto.
Qed.

Lemma bmul_small_via P Y q W : bsmallSz Y q = W ->
  forall s, exists t, bsmallSz (bmul P Y) t = bsmallSz (badd (bmul P W) P) s.
Proof. intros E s. subst W. apply bmul_small_r. Qed.

Lemma bmul_big_via P Y q W : bsmallSz Y q = W ->
  forall s, exists t, forall ξ, bbigSz (bmul P Y) t ξ = bbigSz (badd (bmul P W) P) s ξ.
Proof. intros E s. subst W. apply bmul_big_r. Qed.

(** Left distributivity, up to @bequiv@. *)
Theorem bequiv_bmul_badd P x : forall y, bequiv (bmul P (badd x y)) (badd (bmul P x) (bmul P y)).
Proof.
  induction y as [B g IHg D h IHh]. split.
  - apply bsub_bmul_intro.
    + intro q. destruct (badd_small_cases x (bnode B g D h) q) as [[a E]|[b E]]; rewrite E.
      * eapply bsub_trans; [ apply bsub_bmul_step | apply bsub_le_badd ].
      * eapply bsub_trans; [ apply bsub_badd_l, (proj1 (IHg b)) | ].
        eapply bsub_trans; [ apply (proj1 (bequiv_badd_assoc _ _ _)) | ].
        apply bsub_badd_r. apply (bsub_bmul_step P (bnode B g D h) b).
    + intro d. destruct (badd_big_cases x (bnode B g D h) d) as [[c E]|[d' E]].
      * destruct (bmul_big_fam P x c) as [t1 E1].
        destruct (badd_big_l (bmul P x) (bmul P (bnode B g D h)) t1) as [t E2].
        exists t. intro ξ. rewrite E, E2, E1. apply bsub_refl.
      * destruct (bmul_big_fam P (bnode B g D h) d') as [t1 E1].
        destruct (badd_big_r (bmul P x) (bmul P (bnode B g D h)) t1) as [t E2].
        exists t. intro ξ. rewrite E, E2, E1. apply (proj1 (IHh d' ξ)).
  - apply bsub_badd_intro.
    + apply bsub_bmul_r, bsub_le_badd.
    + intro k. destruct (bmul_small_cases P (bnode B g D h) k) as [q [s E]]. rewrite E.
      (* P·x + (P·y_q + P) ⊑ P·(x + y_q) + P, a child-container of P·(x+y) *)
      assert (H : bsub (badd (bmul P x) (badd (bmul P (g q)) P)) (badd (bmul P (badd x (g q))) P)).
      { eapply bsub_trans; [ apply (proj2 (bequiv_badd_assoc _ _ _)) | ].
        apply bsub_badd_l, (proj2 (IHg q)). }
      destruct (badd_small_r (bmul P x) (badd (bmul P (g q)) P) s) as [s1 E1].
      destruct (bsub_small _ _ H s1) as [s2 H2].
      destruct (badd_small_r x (bnode B g D h) q) as [q' Eq].
      destruct (bmul_small_via P _ q' _ Eq s2) as [t Et].
      exists t. rewrite Et. rewrite E1 in H2. exact H2.
    + intro k. destruct (bmul_big_cases P (bnode B g D h) k) as [[q [s E]]|[d E]].
      * assert (H : bsub (badd (bmul P x) (badd (bmul P (g q)) P)) (badd (bmul P (badd x (g q))) P)).
        { eapply bsub_trans; [ apply (proj2 (bequiv_badd_assoc _ _ _)) | ].
          apply bsub_badd_l, (proj2 (IHg q)). }
        destruct (badd_big_r (bmul P x) (badd (bmul P (g q)) P) s) as [s1 E1].
        destruct (bsub_big _ _ H s1) as [s2 H2].
        destruct (badd_small_r x (bnode B g D h) q) as [q' Eq].
        destruct (bmul_big_via P _ q' _ Eq s2) as [t Et].
        exists t. intro ξ. rewrite Et, E. specialize (H2 ξ). rewrite E1 in H2. exact H2.
      * destruct (badd_big_r x (bnode B g D h) d) as [d' Ed].
        destruct (bmul_big_fam P (badd x (bnode B g D h)) d') as [t Et].
        exists t. intro ξ. rewrite Et, E, Ed. apply (proj2 (IHh d ξ)).
Qed.

(** Equal exponents merge: Ω^e·c + (Ω^e·c' + r) ≈ Ω^e·(c+c') + r. *)
Theorem bequiv_merge E c c' r :
  bequiv (badd (bmul E (embed c)) (badd (bmul E (embed c')) r)) (badd (bmul E (embed (c + c'))) r).
Proof.
  eapply bequiv_trans; [ apply bequiv_sym, bequiv_badd_assoc | ].
  apply bequiv_badd; [ | apply bequiv_refl ].
  eapply bequiv_trans; [ apply bequiv_sym, bequiv_bmul_badd | ].
  apply bequiv_bmul; [ apply bequiv_refl | apply bequiv_sym, bequiv_embed_add ].
Qed.

(** ** Shifted enumerations *)

Lemma addOrd_lt_cases t y a : a < t + y -> a < t \/ exists j:y, a ≤ t + y j.
Proof.
  rewrite addOrd_unfold. intro H. apply lub_lt in H. destruct H as [H|H]; [ left; auto | right ].
  apply sup_lt in H. destruct H as [j Hj]. exists j.
  rewrite ord_lt_unfold in Hj. destruct Hj as [[] Hj]. exact Hj.
Qed.

(** ** Enumerating a class cut off above a threshold

If the common fixpoints of (f, F) are exactly those of (f, G) that lie
in an upward-closed region U, and the region contains all values of
the first enumerator, then the first enumerator is the second shifted
by the least argument t landing in U.  The shift needs the fixpoints of
(f, G) to be additively principal. *)

Section cfe_offset.
  Variable f : Ord -> Ord.
  Hypothesis Hf : normal_function f.
  Variables I J : Type.
  Variable F : I -> Ord -> Ord.
  Variable G : J -> Ord -> Ord.
  Hypothesis HF : forall i, normal_function (F i).
  Hypothesis HG : forall j, normal_function (G j).
  Variable i0 : I.
  Variable j0 : J.

  Let fixI z := f z ≤ z /\ forall i, F i z ≤ z.
  Let fixJ z := f z ≤ z /\ forall j, G j z ≤ z.

  Variable U : Ord -> Prop.
  Hypothesis HU : forall a b, a ≤ b -> U a -> U b.
  Hypothesis H1 : forall z, complete z -> fixI z -> fixJ z.
  Hypothesis H2 : forall z, complete z -> fixJ z -> U z -> fixI z.
  Hypothesis H3 : forall y, complete y -> U (cfe f I F y).
  Hypothesis Hp : forall z, complete z -> fixJ z -> forall a, a < z -> a + z ≤ z.

  Variable t : Ord.
  Hypothesis Ht0 : complete t.
  Hypothesis Ht1 : U (cfe f J G t).
  Hypothesis Ht2 : forall z, complete z -> fixJ z -> U z -> cfe f J G t ≤ z.
  Hypothesis Ht3 : t < cfe f J G t.

  Let decJ : inhabited J \/ ~ inhabited J := or_introl (inhabits j0).
  Let decI : inhabited I \/ ~ inhabited I := or_introl (inhabits i0).

  Lemma fixJ_value x : complete x -> fixJ (cfe f J G x).
  Proof. intro Hx. split; [ apply (cfe_fix_f f Hf J G HG j0); auto | intro j; apply cfe_fix_F; auto ]. Qed.

  Lemma fixI_value x : complete x -> fixI (cfe f I F x).
  Proof. intro Hx. split; [ apply (cfe_fix_f f Hf I F HF i0); auto | intro i; apply cfe_fix_F; auto ]. Qed.

  Theorem cfe_offset : forall y, complete y -> cfe f I F y ≈ cfe f J G (t + y).
  Proof.
    induction y as [y IH] using ordinal_induction. intro Hy.
    assert (Hty : complete (t + y)) by (apply addOrd_complete; auto).
    split.
    - apply (cfe_least f Hf I F HF).
      + transitivity (f (t + y)); [ apply normal_monotone; auto; apply addOrd_le2 | apply cfe_ge_f ].
      + apply limit_least. intro j.
        assert (Hj : complete (y j)) by (apply complete_subord; auto).
        eapply ord_le_lt_trans; [ apply (proj1 (IH (y j) (index_lt y j) Hj)) | ].
        apply (cfe_increasing f Hf J G HG decJ); auto. apply addOrd_increasing, index_lt.
      + intro i. destruct (H2 _ (cfe_complete f Hf J G HG _ Hty) (fixJ_value _ Hty)) as [Hf1 Hf2].
        * apply HU with (cfe f J G t); auto. apply cfe_monotone; auto. apply addOrd_le1.
        * split; auto.
    - set (z := cfe f I F y).
      assert (Hz : complete z) by (apply cfe_complete; auto).
      assert (HzJ : fixJ z) by (apply H1; auto; apply fixI_value; auto).
      assert (HzI := fixI_value y Hy). fold z in HzI.
      assert (Htz : cfe f J G t ≤ z) by (apply Ht2; auto; apply H3; auto).
      apply (cfe_least f Hf J G HG).
      + transitivity (f z); [ apply normal_monotone; auto | apply HzI ].
        transitivity (t + z); [ apply addOrd_monotone; [ reflexivity | apply cfe_inflationary; auto ] | ].
        apply Hp; auto. eapply ord_lt_le_trans; eauto.
      + apply limit_least. intro k.
        assert (Hk : (t + y) k < t + y) by apply index_lt.
        assert (Hkc : complete ((t + y) k)) by (apply complete_subord; auto).
        destruct (addOrd_lt_cases t y _ Hk) as [Hk1|[j Hk1]].
        * eapply ord_lt_le_trans; [ | exact Htz ].
          apply (cfe_increasing f Hf J G HG decJ); auto.
        * assert (Hj : complete (y j)) by (apply complete_subord; auto).
          eapply ord_le_lt_trans; [ apply cfe_monotone; eauto | ].
          eapply ord_le_lt_trans; [ apply (proj2 (IH (y j) (index_lt y j) Hj)) | ].
          apply (cfe_increasing f Hf I F HF decI); auto. apply index_lt.
      + intro j. split; [ apply HzJ | apply HzJ ].
  Qed.
End cfe_offset.

(** The least value of φ_T at a successor lies below every common
    fixpoint above the previous value. *)
Lemma bphi_succ_le f (Hf : normal_function f) T z a : bgood f T -> complete z -> bfix f T z ->
  complete a -> bphi f T a < z -> bphi f T (succOrd a) ≤ z.
Proof.
  intros HT Hz [H1 [H2 H3]] Ha Hlt.
  rewrite bphi_unfold.
  apply (cfe_least f Hf _ _ (bphi_fam_normal'' f Hf T HT)).
  - transitivity (f z); auto. apply normal_monotone; auto.
    apply succ_least. eapply ord_le_lt_trans; [ | exact Hlt ].
    apply normal_inflationary; auto. apply bphi_normal; auto.
  - apply limit_least. intros []. rewrite <- bphi_unfold. exact Hlt.
  - intros [k|k]; simpl; split; auto.
Qed.

Lemma bsmall_mul_embed_inh y x : 0 < x -> inhabited (bsmall (bmul (bexpΩ y) (embed x))).
Proof.
  destruct x as [X g]. intro H. rewrite ord_lt_unfold in H. destruct H as [q _].
  destruct (bexpΩ_small_zero y) as [t0 _].
  destruct (badd_small_r (bmul (bexpΩ y) (embed (g q))) (bexpΩ y) t0) as [s _].
  destruct (bmul_small_r (bexpΩ y) (embed (ord X g)) q s) as [t _].
  exact (inhabits t).
Qed.

Lemma zlt_embed_Ω z a : a < z -> zlt z (embed a) bOmega.
Proof.
  intro Ha. exists (embed (succOrd a)). split; [ apply bslt_embed, succ_lt | ].
  apply (LZ_big z _ bOmega tt (succOrd a)); [ apply succ_least; auto | apply LZ_sub, bsub_refl ].
Qed.
