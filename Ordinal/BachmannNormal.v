From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.

Import ListNotations.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannAssoc.
From Ordinal Require Import BachmannPower.
From Ordinal Require Import BachmannCfe.

Open Scope ord_scope.

(** * Normality of Bachmann's hierarchy, proved directly

In @BachmannCalibration@ the hierarchy is calibrated against known normal
functions (Veblen, Schütte's columns), which takes us as far as the
Large Veblen Ordinal.  Beyond that there is nothing to calibrate
against, so here we prove normality of φ directly.

The proof splits in two; (A) and the definition of @bphi@ are in
@BachmannCfe@, and the agreement of @bphi@ with Bachmann's @bach@ in
@BachmannAgree@.

 (A) A generic construction, independent of index trees.  Given a base
     normal function f and a family of normal functions F_i, let E y
     be f y joined with the least fixpoints, above the previous
     values, of the nonempty compositions F_i ∘ F_{i_1} ∘ … ∘ F_{i_n}
     ∘ f.  The compositions form a directed family (any two are
     dominated by their concatenation), and every one of them
     dominates f, so the family of terms is directed without deciding
     whether there are any F_i.  With no F_i, E is f itself;
     otherwise E enumerates the common fixpoints of f and the F_i.
     Strict monotonicity of E does need that decision, but only as a
     proposition.

 (B) The Bachmann-specific content.  The hierarchy @bphi@ applies E
     at each node to the node's components; it is normal by
     construction on trees whose nodes decide whether they have
     components.  Bachmann's φ takes least fixpoints of the components
     one at a time, and agrees with @bphi@ when the components are
     suitably nested and directed.  We show, by structural conditions
     preserved by the tree arithmetic, that this holds on the
     canonical trees up to ε_{Ω+1}; in particular φ_{ε_{Ω+1}}(0) is
     the Bachmann–Howard ordinal.
*)


(** ** φ is monotone in the index, for @bsub@ *)

Theorem bphi_mono_index f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall y, bfam y ->
    (forall a b, a ≤ b -> bphi f y a ≤ bphi f y b) /\
    (forall x, bsub x y -> forall z, bphi f x z ≤ bphi f y z).
Proof.
  induction y as [B g' Hg D h' Hh]; intros [Hy1 [Hy2 Hy3]].
  assert (HFm : forall k x y, x ≤ y -> bphi_fam f g' h' k x ≤ bphi_fam f g' h' k y).
  { intros [b|d] x y Hxy; simpl.
    - apply (proj1 (Hg b (Hy1 b))); auto.
    - apply (proj2 (Hh d y (Hy2 d y))). apply Hy3; auto. }
  split.
  - change (forall a b, a ≤ b -> cfe f (B + D) (bphi_fam f g' h') a ≤ cfe f (B + D) (bphi_fam f g' h') b).
    apply cfe_monotone_gen; auto.
  - intros [A g C h] [Hs1 Hs2] z.
    change (cfe f (A + C) (bphi_fam f g h) z ≤ cfe f (B + D) (bphi_fam f g' h') z).
    apply cfe_mono_family; auto.
    intros [a|c].
    + destruct (Hs1 a) as [b Hb]. exists (inl b). intro x. simpl.
      apply (proj2 (Hg b (Hy1 b))); auto.
    + destruct (Hs2 c) as [d Hd]. exists (inr d). intro x. simpl.
      apply (proj2 (Hh d x (Hy2 d x))); auto.
Qed.


(** ** Strict increase along a family *)

(** x lies strictly below y if it lies below a small child of y, or
    (recursively) strictly below a small child of y or a member of one
    of y's Ω-families at a finite argument. *)
Inductive bslt : BOrd -> BOrd -> Prop :=
| bslt_small : forall x y b, bsub x (bsmallSz y b) -> bslt x y
| bslt_big : forall x y d n, bslt x (bbigSz y d (natOrdSize n)) -> bslt x y
| bslt_desc : forall x y b, bslt x (bsmallSz y b) -> bslt x y.

Lemma fix_onePlus_finite f (Hf : normal_function f) z :
  complete z -> f z ≤ z -> forall n, natOrdSize n ≤ z.
Proof.
  intros Hz Hfz n.
  induction n as [|n IH]; simpl; [ apply zero_least | ].
  apply succ_least.
  eapply ord_lt_le_trans; [ apply onePlus_finite | ].
  transitivity (1 + z); [ apply addOrd_monotone; auto; reflexivity | ].
  transitivity (f z); auto.
  apply onePlus_least_normal; auto.
Qed.


(** ** Structural conditions on Ω-families *)

Fixpoint bcanon (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (forall a, bcanon (g a)) /\
    (forall c ξ, bcanon (h c ξ)) /\
    (forall c ξ ξ', ξ ≤ ξ' -> bsub (h c ξ) (h c ξ')) /\
    (forall c ξ ξ', complete ξ' -> ξ < ξ' -> bslt (h c ξ) (h c ξ')) /\
    (forall c B (k:B -> Ord) (b0:B), directed B k -> (forall b, complete (k b)) ->
       bsub (h c (supOrd k)) (bsup (fun b => h c (k b))))
  end.


Lemma bcanon_bfam : forall T, bcanon T -> bfam T.
Proof.
  induction T as [A g Hg C h Hh]; intros [H1 [H2 [H3 _]]].
  simpl. split; [ intro a; apply Hg; auto | split; [ intros c ξ; apply Hh; auto | exact H3 ] ].
Qed.

(** ** First instances: ordinary ordinals and Ω *)

Lemma bcanon_embed : forall ξ, bcanon (embed ξ).
Proof.
  induction ξ as [X k Hk]; simpl.
  split; [ auto | repeat split; intros [] ].
Qed.

Lemma embed_small (x:Ord) (c:x) : exists q, bsmallSz (embed x) q = embed (x c).
Proof. destruct x. exists c. reflexivity. Qed.

Lemma bcanon_Ω : bcanon bOmega.
Proof.
  simpl. split; [ intros [] | split; [ intros _ ξ; apply bcanon_embed | split; [ | split ] ] ].
  - intros _ ξ ξ' H. apply bsub_embed; auto.
  - intros _ ξ [X' k'] _ H.
    rewrite ord_lt_unfold in H. destruct H as [j Hj].
    apply (bslt_small (embed ξ) (embed (ord X' k')) j).
    change (bsub (embed ξ) (embed (k' j))). apply bsub_embed; auto.
  - intros _ B k b0 _ _.
    apply bsub_intro.
    + intros [b c].
      destruct (embed_small (k b) c) as [q Hq].
      exists (existT _ b q).
      change (bsub (embed (k b c)) (bsmallSz (embed (k b)) q)).
      rewrite Hq. apply bsub_refl.
    + intros [].
Qed.


(** ** The arithmetic preserves @bcanon@ *)

Lemma bcanon_small x a : bcanon x -> bcanon (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bcanon_big x c ξ : bcanon x -> bcanon (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bcanon_fmono x c ξ ξ' : bcanon x -> ξ ≤ ξ' -> bsub (bbigSz x c ξ) (bbigSz x c ξ').
Proof. destruct x; simpl; intros [? [? [H ?]]]; auto. Qed.

Lemma bcanon_fstrict x c ξ ξ' : bcanon x -> complete ξ' -> ξ < ξ' ->
  bslt (bbigSz x c ξ) (bbigSz x c ξ').
Proof. destruct x; simpl; intros [? [? [? [H ?]]]]; auto. Qed.

Lemma bcanon_fcont x c B (k:B -> Ord) (b0:B) : bcanon x -> directed B k -> (forall b, complete (k b)) ->
  bsub (bbigSz x c (supOrd k)) (bsup (fun b => bbigSz x c (k b))).
Proof. destruct x; simpl; intros [? [? [? [? H]]]]; eauto. Qed.

Lemma bcanon_blub x y : bcanon x -> bcanon y -> bcanon (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [H1 [H2 [H3 [H4 H5]]]] [H1' [H2' [H3' [H4' H5']]]].
  repeat split.
  - intros [a|b]; auto.
  - intros [c|d] ξ; auto.
  - intros [c|d]; auto.
  - intros [c|d]; auto.
  - intros [c|d]; eauto.
Qed.

Lemma bcanon_bsup {I:Type} (F:I -> BOrd) : (forall i, bcanon (F i)) -> bcanon (bsup F).
Proof.
  intro H; simpl. repeat split.
  - intros [i a]. apply bcanon_small; auto.
  - intros [i c] ξ. apply bcanon_big; auto.
  - intros [i c] ξ ξ' Hξ. apply bcanon_fmono; auto.
  - intros [i c] ξ ξ' Hc Hξ. apply bcanon_fstrict; auto.
  - intros [i c] B k b0 Hdir Hk. apply (bcanon_fcont (F i) c B k b0); auto.
Qed.

Lemma bcanon_bzero : bcanon bzero.
Proof. simpl. repeat split; intros []. Qed.

Lemma bcanon_bsucc x : bcanon x -> bcanon (bsucc x).
Proof. intro H. simpl. split; [ auto | repeat split; intros [] ]. Qed.

(** *** @bsub@ and @bslt@ bookkeeping *)

Lemma bsub_bzero_l x : bsub bzero x.
Proof. apply bsub_intro; intros []. Qed.

Lemma bsub_le_badd w z : bsub w (badd w z).
Proof. rewrite (badd_eq w z). apply bsub_blub_l. Qed.

Lemma bsub_bsup_le {I:Type} (F:I -> BOrd) i : bsub (F i) (bsup F).
Proof.
  apply bsub_intro.
  - intro a. exists (existT _ i a). apply bsub_refl.
  - intro c. exists (existT _ i c). intro; apply bsub_refl.
Qed.

Lemma bslt_bsub_l a' a b : bsub a' a -> bslt a b -> bslt a' b.
Proof.
  intros H1 H2. induction H2 as [a b j Hj | a b d n H IH | a b j H IH].
  - apply (bslt_small _ _ j). eapply bsub_trans; eauto.
  - apply (bslt_big _ _ d n). auto.
  - apply (bslt_desc _ _ j). auto.
Qed.

Lemma bslt_bsub_r a b b' : bslt a b -> bsub b b' -> bslt a b'.
Proof.
  intro H. revert b'.
  induction H as [a b j Hj | a b d n H IH | a b j H IH]; intros b' Hb.
  - destruct (bsub_small _ _ Hb j) as [j' Hj'].
    apply (bslt_small _ _ j'). eapply bsub_trans; eauto.
  - destruct (bsub_big _ _ Hb d) as [d' Hd'].
    apply (bslt_big _ _ d' n). apply IH. apply Hd'.
  - destruct (bsub_small _ _ Hb j) as [j' Hj'].
    apply (bslt_desc _ _ j'). apply IH. exact Hj'.
Qed.

Definition bpos (z:BOrd) : Prop := bslt bzero z.

(** w lies strictly below w + z whenever z is strictly above something. *)
Lemma bslt_badd_pos w : forall x z, bslt x z -> bslt w (badd w z).
Proof.
  intros x z H.
  induction H as [x z j Hj | x z d n H IH | x z j H IH].
  - destruct (badd_small_r w z j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_le_badd.
  - destruct (badd_big_r w z d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (badd_small_r w z j) as [t Ht].
    apply (bslt_desc _ _ t). rewrite Ht. exact IH.
Qed.

Lemma bslt_badd_r x : forall a b, bslt a b -> bslt (badd x a) (badd x b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - destruct (badd_small_r x b j) as [t Ht].
    apply (bslt_small _ _ t). rewrite Ht. apply bsub_badd_r; auto.
  - destruct (badd_big_r x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (badd_small_r x b j) as [t Ht].
    apply (bslt_desc _ _ t). rewrite Ht. exact IH.
Qed.

Lemma bsub_badd_bsup x {B:Type} (H:B -> BOrd) (b0:B) :
  bsub (badd x (bsup H)) (bsup (fun b => badd x (H b))).
Proof.
  apply bsub_intro.
  - intro s.
    destruct (badd_small_cases x (bsup H) s) as [[a Ha]|[[b q] Hq]]; rewrite Ha || rewrite Hq.
    + destruct (badd_small_l x (H b0) a) as [t Ht].
      exists (existT _ b0 t). change (bsub (bsmallSz x a) (bsmallSz (badd x (H b0)) t)).
      rewrite Ht. apply bsub_refl.
    + destruct (badd_small_r x (H b) q) as [t Ht].
      exists (existT _ b t). change (bsub (badd x (bsmallSz (H b) q)) (bsmallSz (badd x (H b)) t)).
      rewrite Ht. apply bsub_refl.
  - intro c.
    destruct (badd_big_cases x (bsup H) c) as [[e He]|[[b q] Hq]].
    + destruct (badd_big_l x (H b0) e) as [t Ht].
      exists (existT _ b0 t). intro ξ. rewrite He.
      change (bsub (bbigSz x e ξ) (bbigSz (badd x (H b0)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (badd_big_r x (H b) q) as [t Ht].
      exists (existT _ b t). intro ξ. rewrite Hq.
      change (bsub (badd x (bbigSz (H b) q ξ)) (bbigSz (badd x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

Lemma bcanon_badd x y : bcanon x -> bcanon y -> bcanon (badd x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intro Hy.
  destruct Hy as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (badd_eq x (bnode B g D h)).
  apply bcanon_blub; auto.
  unfold baddR; simpl. repeat split.
  - intro b. apply Hg; auto.
  - intros d ξ. apply Hh; auto.
  - intros d ξ ξ' H. apply bsub_badd_r; auto.
  - intros d ξ ξ' Hc H. apply bslt_badd_r; auto.
  - intros d B' k b0 Hdir Hk.
    eapply bsub_trans; [ apply bsub_badd_r, (Hy5 d B' k b0); auto | ].
    apply bsub_badd_bsup; auto.
Qed.

(** *** Multiplication *)

Lemma bmul_small_r x y q s :
  exists t, bsmallSz (bmul x y) t = bsmallSz (badd (bmul x (bsmallSz y q)) x) s.
Proof. destruct y as [B g D h]. exists (inl (existT _ q s)). reflexivity. Qed.

Lemma bmul_big_r x y q c :
  exists t, forall ξ, bbigSz (bmul x y) t ξ = bbigSz (badd (bmul x (bsmallSz y q)) x) c ξ.
Proof. destruct y as [B g D h]. exists (inl (existT _ q c)). intro; reflexivity. Qed.

Lemma bmul_big_fam x y d :
  exists t, forall ξ, bbigSz (bmul x y) t ξ = bmul x (bbigSz y d ξ).
Proof. destruct y as [B g D h]. exists (inr d). intro; reflexivity. Qed.

Lemma bsub_bmul_bsup x {B:Type} (H:B -> BOrd) :
  bsub (bmul x (bsup H)) (bsup (fun b => bmul x (H b))).
Proof.
  apply bsub_intro.
  - intros [[[b q] s]|[]].
    destruct (bmul_small_r x (H b) q s) as [t Ht].
    exists (existT _ b t).
    change (bsub (bsmallSz (badd (bmul x (bsmallSz (H b) q)) x) s) (bsmallSz (bmul x (H b)) t)).
    rewrite Ht. apply bsub_refl.
  - intros [[[b q] c]|[b d]].
    + destruct (bmul_big_r x (H b) q c) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bbigSz (badd (bmul x (bsmallSz (H b) q)) x) c ξ) (bbigSz (bmul x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (bmul_big_fam x (H b) d) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bmul x (bbigSz (H b) d ξ)) (bbigSz (bmul x (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

(** x·b_j + x ⊑ x·b, for any small child b_j of b. *)
Lemma bsub_bmul_step x b j : bsub (badd (bmul x (bsmallSz b j)) x) (bmul x b).
Proof.
  rewrite (bmul_eq x b).
  eapply bsub_trans; [ | apply bsub_blub_l ].
  apply (bsub_bsup_le (fun j => badd (bmul x (bsmallSz b j)) x) j).
Qed.

Lemma bslt_bmul_r x : bpos x -> forall a b, bslt a b -> bslt (bmul x a) (bmul x b).
Proof.
  intros Hx a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - eapply bslt_bsub_l; [ apply bsub_bmul_r, Hj | ].
    eapply bslt_bsub_r; [ | apply bsub_bmul_step ].
    apply (bslt_badd_pos _ bzero x Hx).
  - destruct (bmul_big_fam x b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - eapply bslt_bsub_r; [ exact IH | ].
    eapply bsub_trans; [ apply bsub_le_badd | apply bsub_bmul_step ].
Qed.

Lemma bcanon_bmul x y : bcanon x -> bpos x -> bcanon y -> bcanon (bmul x y).
Proof.
  intros Hx Hpos.
  induction y as [B g Hg D h Hh]; intro Hy.
  assert (Hy' := Hy). destruct Hy' as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (bmul_eq x (bnode B g D h)).
  apply bcanon_blub.
  - unfold bmulS. apply bcanon_bsup. intro b.
    apply bcanon_badd; auto.
  - unfold bmulB; simpl. repeat split.
    + intros [].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bmul_r; auto.
    + intros d ξ ξ' Hc H. apply bslt_bmul_r; auto.
    + intros d B' k b0 Hdir Hk.
      eapply bsub_trans; [ apply bsub_bmul_r, (Hy5 d B' k b0); auto | ].
      apply bsub_bmul_bsup.
Qed.

Lemma bpos_Ω : bpos bOmega.
Proof.
  apply (bslt_big bzero bOmega tt 1).
  apply (bslt_small bzero (embed 1) tt).
  apply bsub_bzero_l.
Qed.

(** *** Exponentiation *)

Lemma bexpΩ_small_zero y : exists t, bsmallSz (bexpΩ y) t = bzero.
Proof. destruct y. exists (inl tt). reflexivity. Qed.

Lemma bpos_bexpΩ y : bpos (bexpΩ y).
Proof.
  destruct (bexpΩ_small_zero y) as [t Ht].
  apply (bslt_small _ _ t). rewrite Ht. apply bsub_refl.
Qed.

Lemma bexpΩ_big_s y q c :
  exists t, forall ξ, bbigSz (bexpΩ y) t ξ = bbigSz (bmul (bexpΩ (bsmallSz y q)) bOmega) c ξ.
Proof. destruct y. exists (inr (inl (existT _ q c))). intro; reflexivity. Qed.

Lemma bexpΩ_big_b y d : exists t, forall ξ, bbigSz (bexpΩ y) t ξ = bexpΩ (bbigSz y d ξ).
Proof. destruct y. exists (inr (inr d)). intro; reflexivity. Qed.

(** A positive P lies strictly below P·2. *)
Lemma bslt_two P : bpos P -> bslt P (bmul P (embed 2)).
Proof.
  intro HP.
  eapply bslt_bsub_l; [ apply (proj2 (bsub_bmul_one P)) | ].
  eapply bslt_bsub_r; [ | apply (bsub_bmul_step P (embed 2) tt) ].
  exact (bslt_badd_pos (bmul P (embed 1)) bzero P HP).
Qed.

Lemma bsub_P_P2 P : bsub P (bmul P (embed 2)).
Proof.
  eapply bsub_trans; [ apply (proj2 (bsub_bmul_one P)) | ].
  eapply bsub_trans; [ apply (bsub_le_badd (bmul P (embed 1)) P) | ].
  apply (bsub_bmul_step P (embed 2) tt).
Qed.

Lemma bslt_bexpΩ : forall a b, bslt a b -> bslt (bexpΩ a) (bexpΩ b).
Proof.
  intros a b H.
  induction H as [a b j Hj | a b d n H IH | a b j H IH].
  - eapply bslt_bsub_l; [ apply bsub_bexpΩ, Hj | ].
    destruct (bexpΩ_big_s b j (inr tt)) as [t Ht].
    apply (bslt_big _ _ t 2). rewrite Ht.
    change (bslt (bexpΩ (bsmallSz b j)) (bmul (bexpΩ (bsmallSz b j)) (embed 2))).
    apply bslt_two, bpos_bexpΩ.
  - destruct (bexpΩ_big_b b d) as [t Ht].
    apply (bslt_big _ _ t n). rewrite Ht. auto.
  - destruct (bexpΩ_big_s b j (inr tt)) as [t Ht].
    apply (bslt_big _ _ t 2). rewrite Ht.
    change (bslt (bexpΩ a) (bmul (bexpΩ (bsmallSz b j)) (embed 2))).
    eapply bslt_bsub_r; [ exact IH | apply bsub_P_P2 ].
Qed.

Lemma bsub_bexpΩ_bsup {B:Type} (H:B -> BOrd) (b0:B) :
  bsub (bexpΩ (bsup H)) (bsup (fun b => bexpΩ (H b))).
Proof.
  apply bsub_intro.
  - intros [[]|[[p [[[] _]|[]]]|[]]].
    destruct (bexpΩ_small_zero (H b0)) as [t Ht].
    exists (existT _ b0 t).
    change (bsub bzero (bsmallSz (bexpΩ (H b0)) t)).
    rewrite Ht. apply bsub_refl.
  - intros [[]|[[[b q] c]|[b d]]].
    + destruct (bexpΩ_big_s (H b) q c) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bbigSz (bmul (bexpΩ (bsmallSz (H b) q)) bOmega) c ξ) (bbigSz (bexpΩ (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
    + destruct (bexpΩ_big_b (H b) d) as [t Ht].
      exists (existT _ b t). intro ξ.
      change (bsub (bexpΩ (bbigSz (H b) d ξ)) (bbigSz (bexpΩ (H b)) t ξ)).
      rewrite Ht. apply bsub_refl.
Qed.

Lemma bcanon_bexpΩ y : bcanon y -> bcanon (bexpΩ y).
Proof.
  induction y as [B g Hg D h Hh]; intro Hy.
  assert (Hy' := Hy). destruct Hy' as [Hy1 [Hy2 [Hy3 [Hy4 Hy5]]]].
  rewrite (bexpΩ_eq (bnode B g D h)).
  apply bcanon_blub; [ apply bcanon_bsucc, bcanon_bzero | apply bcanon_blub ].
  - unfold bexpS. apply bcanon_bsup. intro b.
    apply bcanon_bmul; auto using bcanon_Ω, bpos_bexpΩ.
  - unfold bexpB; simpl. repeat split.
    + intros [].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bexpΩ; auto.
    + intros d ξ ξ' Hc H. apply bslt_bexpΩ; auto.
    + intros d B' k b0 Hdir Hk.
      eapply bsub_trans; [ apply bsub_bexpΩ, (Hy5 d B' k b0); auto | ].
      apply bsub_bexpΩ_bsup; auto.
Qed.

(** *** The tower and ε_{Ω+1} *)

Lemma bcanon_btower n : bcanon (btower n).
Proof.
  induction n.
  - change (bcanon (bsucc bOmega)). apply bcanon_bsucc, bcanon_Ω.
  - change (bcanon (bexpΩ (btower n))). apply bcanon_bexpΩ; auto.
Qed.

Lemma bcanon_bεΩ1 : bcanon bεΩ1.
Proof.
  simpl. split; [ apply bcanon_btower | repeat split; intros [] ].
Qed.

(** ** Deciding whether a node has components *)

(** Every node decides, as a proposition, whether it has any
    components; Ω-family members are required to do so only at complete
    arguments.  Ordinary trees cannot decide this constructively, but
    every tree the arithmetic builds from complete ordinals does.  The
    structural layer carries the decision so that it is available to
    hierarchy @bphi@, which needs it for strictness. *)
Fixpoint bdec (T:BOrd) : Prop :=
  match T with
  | bnode A g C h =>
    (inhabited (A + C) \/ ~ inhabited (A + C)) /\
    (forall a, bdec (g a)) /\
    (forall c ξ, complete ξ -> bdec (h c ξ))
  end.

Lemma bdec_small x a : bdec x -> bdec (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bdec_big x c ξ : bdec x -> complete ξ -> bdec (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bdec_bzero : bdec bzero.
Proof. simpl. split; [ right; intros [[[]|[]]] | split; intros [] ]. Qed.

Lemma bdec_bsucc x : bdec x -> bdec (bsucc x).
Proof. intro H. simpl. split; [ left; exact (inhabits (inl tt)) | split; [ auto | intros [] ] ]. Qed.

Lemma bdec_blub x y : bdec x -> bdec y -> bdec (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [Dx [Hx1 Hx2]] [Dy [Hy1 Hy2]]. split; [ | split ].
  - destruct Dx as [[[a|c]]|Nx].
    + left. exact (inhabits (inl (inl a))).
    + left. exact (inhabits (inr (inl c))).
    + destruct Dy as [[[b|d]]|Ny].
      * left. exact (inhabits (inl (inr b))).
      * left. exact (inhabits (inr (inr d))).
      * right. intros [[[a|b]|[c|d]]];
          [ apply Nx; exact (inhabits (inl a)) | apply Ny; exact (inhabits (inl b))
          | apply Nx; exact (inhabits (inr c)) | apply Ny; exact (inhabits (inr d)) ].
  - intros [a|b]; auto.
  - intros [c|d] ξ Hξ; auto.
Qed.

Lemma bdec_blimΩ h : (forall ξ, complete ξ -> bdec (h ξ)) -> bdec (blimΩ h).
Proof. intro H. simpl. split; [ left; exact (inhabits (inr tt)) | split; [ intros [] | auto ] ]. Qed.

Lemma bdec_blimΩ_inv h : bdec (blimΩ h) -> forall ξ, complete ξ -> bdec (h ξ).
Proof. simpl. intros [_ [_ H]] ξ Hξ. apply (H tt); auto. Qed.

Lemma bdec_badd x y : bdec x -> bdec y -> bdec (badd x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  rewrite (badd_eq x (bnode B g D h)). apply bdec_blub; auto.
  simpl. split; [ exact Dy | split; [ intro b; apply Hg; auto | intros d ξ Hξ; apply Hh; auto ] ].
Qed.

Lemma bslt_inh x y : bslt x y -> inhabited (bsmall y + bbig y).
Proof. intros [x' y' b _ | x' y' d n _ | x' y' b _]; constructor; [ left | right | left ]; assumption. Qed.

Lemma bdec_bmul x y : inhabited (bsmall x + bbig x) -> bdec x -> bdec y -> bdec (bmul x y).
Proof.
  intros Hi Hx.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  simpl. split; [ | split ].
  - destruct Dy as [[[b|d]]|N].
    + left. destruct Hi as [[s|c]].
      * destruct (badd_small_r (bmul x (g b)) x s) as [t _].
        exact (inhabits (inl (inl (existT _ b t)))).
      * destruct (badd_big_r (bmul x (g b)) x c) as [t _].
        exact (inhabits (inr (inl (existT _ b t)))).
    + left. exact (inhabits (inr (inr d))).
    + right. intros [[[[b _]|[]]|[[b _]|d]]]; apply N; constructor; [ left | left | right ]; assumption.
  - intros [[b s]|[]].
    exact (bdec_small (badd (bmul x (g b)) x) s (bdec_badd _ _ (Hg b (Hy1 b)) Hx)).
  - intros [[b c]|d] ξ Hξ.
    + exact (bdec_big (badd (bmul x (g b)) x) c ξ (bdec_badd _ _ (Hg b (Hy1 b)) Hx) Hξ).
    + apply Hh; auto.
Qed.

Lemma bexpΩ_inh y : inhabited (bsmall (bexpΩ y) + bbig (bexpΩ y)).
Proof. destruct y. exact (inhabits (inl (inl tt))). Qed.

Lemma bdec_embed ξ : complete ξ -> bdec (embed ξ).
Proof.
  induction ξ as [X k Hk]; intros [_ [Hi Hc]]. simpl.
  split; [ | split; [ intro a; apply Hk; auto | intros [] ] ].
  destruct Hi as [[x]|N]; [ left; exact (inhabits (inl x)) | right; intros [[x|[]]]; apply N; exact (inhabits x) ].
Qed.

Lemma bdec_Ω : bdec bOmega.
Proof. apply bdec_blimΩ, bdec_embed. Qed.

Lemma bdec_bexpΩ y : bdec y -> bdec (bexpΩ y).
Proof.
  induction y as [B g Hg D h Hh]; intros [Dy [Hy1 Hy2]].
  simpl. split; [ left; exact (inhabits (inl (inl tt))) | split ].
  - intros [[]|[[b s]|[]]]; [ apply bdec_bzero | ].
    exact (bdec_small (bmul (bexpΩ (g b)) bOmega) s
             (bdec_bmul _ _ (bexpΩ_inh _) (Hg b (Hy1 b)) bdec_Ω)).
  - intros [[]|[[b c]|d]] ξ Hξ.
    + exact (bdec_big (bmul (bexpΩ (g b)) bOmega) c ξ
               (bdec_bmul _ _ (bexpΩ_inh _) (Hg b (Hy1 b)) bdec_Ω) Hξ).
    + apply Hh; auto.
Qed.

Lemma bdec_btower n : bdec (btower n).
Proof.
  induction n; [ exact (bdec_bsucc _ bdec_Ω) | exact (bdec_bexpΩ _ IHn) ].
Qed.

Lemma bdec_bεΩ1 : bdec bεΩ1.
Proof. simpl. split; [ left; exact (inhabits (inl 0%nat)) | split; [ apply bdec_btower | intros [] ] ]. Qed.

(** Canonical and decided. *)
Definition bcd (T:BOrd) : Prop := bcanon T /\ bdec T.

Lemma bcd_small x a : bcd x -> bcd (bsmallSz x a).
Proof. intros [H1 H2]. split; [ apply bcanon_small | apply bdec_small ]; auto. Qed.

Lemma bcd_big x c ξ : bcd x -> complete ξ -> bcd (bbigSz x c ξ).
Proof. intros [H1 H2] Hξ. split; [ apply bcanon_big | apply bdec_big ]; auto. Qed.

Lemma bcd_badd x y : bcd x -> bcd y -> bcd (badd x y).
Proof. intros [H1 H2] [H3 H4]. split; [ apply bcanon_badd | apply bdec_badd ]; auto. Qed.

Lemma bcd_bmul x y : bcd x -> bpos x -> bcd y -> bcd (bmul x y).
Proof.
  intros [H1 H2] Hp [H3 H4]. split; [ apply bcanon_bmul | apply bdec_bmul ]; auto.
  exact (bslt_inh _ _ Hp).
Qed.

Lemma bcd_bexpΩ y : bcd y -> bcd (bexpΩ y).
Proof. intros [H1 H2]. split; [ apply bcanon_bexpΩ | apply bdec_bexpΩ ]; auto. Qed.

Lemma bcd_embed ξ : complete ξ -> bcd (embed ξ).
Proof. intro H. split; [ apply bcanon_embed | apply bdec_embed ]; auto. Qed.

Lemma bcd_Ω : bcd bOmega.
Proof. split; [ apply bcanon_Ω | apply bdec_Ω ]. Qed.

Lemma bcd_btower n : bcd (btower n).
Proof. split; [ apply bcanon_btower | apply bdec_btower ]. Qed.

Lemma bcd_bεΩ1 : bcd bεΩ1.
Proof. split; [ apply bcanon_bεΩ1 | apply bdec_bεΩ1 ]. Qed.


(** ** Strict increase along a family *)

Lemma bphi_child_lt f (Hf : normal_function f) y b :
  bgood f y -> bphi f (bsmallSz y b) 0 < bphi f y 0.
Proof.
  intros Hgood.
  eapply ord_lt_le_trans; [ | apply (bphi_fix_small' f Hf y b 0 Hgood zero_complete) ].
  apply normal_increasing.
  - apply bphi_normal; auto. apply bgood_small; auto.
  - apply bphi_complete; auto using zero_complete.
  - apply bphi_nonzero; auto.
Qed.

Theorem bphi_strict f (Hf : normal_function f) :
  forall x y, bslt x y -> bgood f y -> bfam y -> bphi f x 0 < bphi f y 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros x y H.
  induction H as [x y b Hb | x y d n H IH | x y b H IH]; intros Hgood Hfam.
  - apply ord_le_lt_trans with (bphi f (bsmallSz y b) 0).
    { apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ Hfam b))); auto. }
    apply bphi_child_lt; auto.
  - eapply ord_lt_le_trans; [ apply IH | ].
    + apply bgood_big; auto using natOrdSize_complete.
    + apply bfam_big; auto.
    + eapply ord_le_trans; [ | apply (bphi_fix_big' f Hf y d 0 Hgood zero_complete) ].
      apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ Hfam d _))).
      apply (bfam_fam _ Hfam d).
      apply (fix_onePlus_finite f Hf).
      * apply bphi_complete; auto using zero_complete.
      * apply (bphi_fix_base' f Hf y 0 Hgood (inhabits (inr d)) zero_complete).
  - eapply ord_lt_trans; [ apply IH | apply bphi_child_lt; auto ].
    + apply bgood_small; auto.
    + apply bfam_small; auto.
Qed.

(** ** Continuity of the diagonal *)

Lemma bsub_inh x y : bsub x y -> inhabited (bsmall x + bbig x) -> inhabited (bsmall y + bbig y).
Proof.
  intros H [[a|c]].
  - destruct (bsub_small _ _ H a) as [b _]. exact (inhabits (inl b)).
  - destruct (bsub_big _ _ H c) as [d _]. exact (inhabits (inr d)).
Qed.

Theorem bphi_diag_cont f (Hf : normal_function f) (h : Ord -> BOrd) :
  (forall ξ, complete ξ -> bgood f (h ξ)) -> (forall ξ, bfam (h ξ)) ->
  (forall ξ ξ', ξ ≤ ξ' -> bsub (h ξ) (h ξ')) ->
  (forall A (g:A -> Ord) (a0:A), directed A g -> (forall a, complete (g a)) ->
     bsub (h (supOrd g)) (bsup (fun a => h (g a)))) ->
  scott_continuous (fun ξ => bphi f (h ξ) 0).
Proof.
  intros Hgood Hfam Hmono Hcont A g a0 Hdir Hc.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (Hg : forall a, bgood f (h (g a))) by (intro a; apply Hgood; auto).
  assert (Hzc : forall a, complete (bphi f (h (g a)) 0)).
  { intro a. apply bphi_complete; auto using zero_complete. }
  assert (Hzmono : forall a b, g a ≤ g b -> bphi f (h (g a)) 0 ≤ bphi f (h (g b)) 0).
  { intros a b Hab. apply (proj2 (bphi_mono_index f Hfm _ (Hfam _))). apply Hmono; auto. }
  assert (Hzdir : directed A (fun a => bphi f (h (g a)) 0)).
  { intros a1 a2. destruct (Hdir a1 a2) as [a' [H1 H2]].
    exists a'. split; apply Hzmono; auto. }
  set (z := supOrd (fun a => bphi f (h (g a)) 0)).
  (* if some member has a component, z is a fixpoint of f *)
  assert (Hfz : forall a, inhabited (bsmall (h (g a)) + bbig (h (g a))) -> f z ≤ z).
  { intros a Ha.
    eapply ord_le_trans; [ apply (normal_continuous f Hf A _ a0 Hzdir Hzc) | ].
    apply sup_least. intro b.
    destruct (Hdir a b) as [b' [Hab' Hbb']].
    eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
    transitivity (f (bphi f (h (g b')) 0)); [ apply Hfm; auto | ].
    apply bphi_fix_base'; auto using zero_complete.
    apply bsub_inh with (h (g a)); auto. }
  transitivity (bphi f (bsup (fun a => h (g a))) 0).
  { apply (proj2 (bphi_mono_index f Hfm _ (bfam_bsup _ (fun a => Hfam (g a))))).
    apply Hcont; auto. }
  assert (HFam : forall k, normal_function
             (bphi_fam f (fun p : sigT (fun a => bsmall (h (g a))) => bsmallSz (h (g (projT1 p))) (projT2 p))
                          (fun p : sigT (fun a => bbig (h (g a))) => bbigSz (h (g (projT1 p))) (projT2 p)) k)).
  { intros [[a s]|[a c]]; simpl.
    - apply bphi_normal; auto. apply bgood_small; auto.
    - apply bgood_diag; auto. }
  apply (cfe_least f Hf _ _ HFam).
  - transitivity (bphi f (h (g a0)) 0); [ apply bphi_ge_f | apply (sup_le _ (fun a => bphi f (h (g a)) 0) a0) ].
  - apply limit_least. intros [].
  - intros [[a s]|[a c]]; simpl; split.
    + assert (HG : normal_function (bphi f (bsmallSz (h (g a)) s))).
      { apply bphi_normal; auto. apply bgood_small; auto. }
      eapply ord_le_trans; [ apply (normal_continuous _ HG A _ a0 Hzdir Hzc) | ].
      apply sup_least. intro b.
      destruct (Hdir a b) as [b' [Hab' Hbb']].
      destruct (bsub_small _ _ (Hmono _ _ Hab') s) as [s' Hs'].
      eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
      transitivity (bphi f (bsmallSz (h (g a)) s) (bphi f (h (g b')) 0)).
      { apply normal_monotone; auto. }
      transitivity (bphi f (bsmallSz (h (g b')) s') (bphi f (h (g b')) 0)).
      { apply (proj2 (bphi_mono_index f Hfm _ (bfam_small _ (Hfam _) s'))); auto. }
      apply bphi_fix_small'; auto using zero_complete.
    + apply (Hfz a). exact (inhabits (inl s)).
    + assert (HD : normal_function (fun ξ => bphi f (bbigSz (h (g a)) c ξ) 0)).
      { apply bgood_diag; auto. }
      eapply ord_le_trans; [ apply (normal_continuous _ HD A _ a0 Hzdir Hzc) | ].
      apply sup_least. intro b.
      destruct (Hdir a b) as [b' [Hab' Hbb']].
      destruct (bsub_big _ _ (Hmono _ _ Hab') c) as [c' Hc'].
      eapply ord_le_trans; [ | apply (sup_le _ (fun a => bphi f (h (g a)) 0) b') ].
      transitivity (bphi f (bbigSz (h (g a)) c (bphi f (h (g b')) 0)) 0).
      { apply normal_monotone with (f := fun ξ => bphi f (bbigSz (h (g a)) c ξ) 0); auto. }
      transitivity (bphi f (bbigSz (h (g b')) c' (bphi f (h (g b')) 0)) 0).
      { apply (proj2 (bphi_mono_index f Hfm _ (bfam_big _ (Hfam _) c' _))); auto. }
      apply bphi_fix_big'; auto using zero_complete.
    + apply (Hfz a). exact (inhabits (inr c)).
Qed.

(** ** Canonical, decided trees are good *)

Theorem bcanon_good f (Hf : normal_function f) : forall T, bcanon T -> bdec T -> bfam T /\ bgood f T.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  intros T HT HD. split; [ apply (bcanon_bfam T HT) | ].
  revert HT HD.
  induction T as [A g Hg C h Hh]; intros HT [D1 [D2 D3]].
  assert (HT' := HT). destruct HT' as [H1 [H2 [H3 [H4 H5]]]].
  assert (HF : forall c ξ, bfam (h c ξ)) by (intros c ξ; apply bcanon_bfam; auto).
  assert (HG : forall c ξ, complete ξ -> bgood f (h c ξ)) by (intros c ξ Hξ; apply Hh; auto).
  simpl. split; [ intro a; apply Hg; auto | split; [ exact HG | split; [ | split; [ | exact D1 ] ] ] ].
  - intro c. constructor.
    + intros x y Hxy.
      apply (proj2 (bphi_mono_index f Hfm (h c y) (HF c y))). apply H3; auto.
    + intros x y Hy Hxy.
      apply bphi_strict; [ exact Hf | apply H4; auto | apply HG; auto | apply HF ].
    + apply bphi_diag_cont;
        [ exact Hf | intros; apply HG; auto | intro; apply HF | intros ξ ξ' H; apply H3; auto
        | intros B k b0 Hdir Hk; apply (H5 c B k b0); auto ].
    + intros x Hx. apply bphi_complete; auto using zero_complete.
    + intro x. apply bphi_nonzero; auto.
  - intros c ξ Hξ Hpos. apply (bslt_inh (h c 0)). apply H4; auto.
Qed.


(** ** Normality of the canonical hierarchy *)

Corollary bcanon_normal f (Hf : normal_function f) T : bcd T -> normal_function (bphi f T).
Proof. intros [H1 H2]. apply bphi_normal; auto. apply (bcanon_good f Hf T H1 H2). Qed.

Corollary bphi_Ω_normal f (Hf : normal_function f) : normal_function (bphi f bOmega).
Proof. apply bcanon_normal; auto using bcd_Ω. Qed.

(** φ_{ε_{Ω+1}} is a normal function. *)
Theorem bphi_εΩ1_normal f : normal_function f -> normal_function (bphi f bεΩ1).
Proof. intro Hf. apply bcanon_normal; auto using bcd_bεΩ1. Qed.

(** The Bachmann–Howard ordinal, defined via the provably normal
    hierarchy @bphi@. *)
Definition BachmannHoward : Ord := bphi powOmega bεΩ1 0.

Lemma BachmannHoward_complete : complete BachmannHoward.
Proof.
  unfold BachmannHoward.
  apply normal_complete; auto using zero_complete.
  apply bphi_εΩ1_normal, powOmega_normal.
Qed.

(** Every canonical tree Ω^ζ·ξ, and Ω^Ω, gives a normal function. *)
Corollary bphi_canonical_normal f : normal_function f ->
  forall ξ ζ, complete ξ -> complete ζ ->
    normal_function (bphi f (bmul (bexpΩ (embed ζ)) (embed ξ))) /\
    normal_function (bphi f (bexpΩ bOmega)).
Proof.
  intros Hf ξ ζ Hξ Hζ. split; apply bcanon_normal; auto.
  - apply bcd_bmul; auto using bcd_embed, bpos_bexpΩ, bcd_bexpΩ.
  - apply bcd_bexpΩ, bcd_Ω.
Qed.
