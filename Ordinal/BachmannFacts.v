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
From Ordinal Require Import BachmannDefs.
From Ordinal Require Import BachmannNormal.

Open Scope ord_scope.

(** * Semantic facts about Bachmann's hierarchy, for notation systems

Prerequisites for the notation system in @Notation.BachmannNotation@:
small identities between canonical trees, up to @bsub@ in both
directions (φ depends on the tree, not only on the order type of the
index), and calibrations of @bphi@ at the base 1+x. *)

(** ** Trees with no components *)

Lemma bphi_bzero f (Hf : normal_function f) y : bphi f bzero y ≈ f y.
Proof.
  split; [ | apply bphi_ge_f ].
  change (cfe f (False + False) (bphi_fam f (False_rect BOrd) (False_rect (Ord -> BOrd))) y ≤ f y).
  rewrite cfe_unroll. apply sup_least. intros [[[[]|[]] _]|]; simpl. reflexivity.
Qed.

(** ** Identities between canonical trees, up to @bsub@ *)

Definition bequiv (x y:BOrd) : Prop := bsub x y /\ bsub y x.

Lemma bequiv_refl x : bequiv x x.
Proof. split; apply bsub_refl. Qed.

Lemma bequiv_sym x y : bequiv x y -> bequiv y x.
Proof. intros [H1 H2]; split; auto. Qed.

Lemma bequiv_trans x y z : bequiv x y -> bequiv y z -> bequiv x z.
Proof. intros [H1 H2] [H3 H4]; split; eapply bsub_trans; eauto. Qed.

Lemma bequiv_embed ξ ξ' : ξ ≈ ξ' -> bequiv (embed ξ) (embed ξ').
Proof. intros [H1 H2]; split; apply bsub_embed; auto. Qed.

Lemma bequiv_badd x x' y y' : bequiv x x' -> bequiv y y' -> bequiv (badd x y) (badd x' y').
Proof.
  intros [H1 H2] [H3 H4]; split.
  - eapply bsub_trans; [ apply bsub_badd_l, H1 | apply bsub_badd_r, H3 ].
  - eapply bsub_trans; [ apply bsub_badd_l, H2 | apply bsub_badd_r, H4 ].
Qed.

Lemma bequiv_bmul x x' y y' : bequiv x x' -> bequiv y y' -> bequiv (bmul x y) (bmul x' y').
Proof.
  intros [H1 H2] [H3 H4]; split.
  - eapply bsub_trans; [ apply bsub_bmul_l, H1 | apply bsub_bmul_r, H3 ].
  - eapply bsub_trans; [ apply bsub_bmul_l, H2 | apply bsub_bmul_r, H4 ].
Qed.

Lemma bequiv_bexpΩ x x' : bequiv x x' -> bequiv (bexpΩ x) (bexpΩ x').
Proof. intros [H1 H2]; split; apply bsub_bexpΩ; auto. Qed.

(** 0 + x and x + 0 are x. *)
Lemma bequiv_badd_zero_l x : bequiv (badd bzero x) x.
Proof. apply bsub_badd_empty_l; intros []. Qed.

Lemma bequiv_badd_zero_r x : bequiv (badd x bzero) x.
Proof.
  split; apply bsub_intro.
  - intro a. destruct (badd_small_cases x bzero a) as [[a' E]|[[] _]].
    exists a'. rewrite E. apply bsub_refl.
  - intro c. destruct (badd_big_cases x bzero c) as [[c' E]|[[] _]].
    exists c'. intro ξ. rewrite E. apply bsub_refl.
  - intro a. destruct (badd_small_l x bzero a) as [a' E].
    exists a'. rewrite E. apply bsub_refl.
  - intro c. destruct (badd_big_l x bzero c) as [c' E].
    exists c'. intro ξ. rewrite E. apply bsub_refl.
Qed.

(** Ω^0 = 1 has the single small child 0 and no families. *)
Lemma bexpΩ_bzero_small (t:bsmall (bexpΩ bzero)) : bsmallSz (bexpΩ bzero) t = bzero.
Proof. destruct t as [[]|[[[] _]|[]]]; reflexivity. Qed.

Lemma bexpΩ_bzero_big (t:bbig (bexpΩ bzero)) : False.
Proof. destruct t as [[]|[[[] _]|[]]]. Qed.

Lemma embed_big ξ (c:bbig (embed ξ)) : False.
Proof. destruct ξ. destruct c. Qed.

(** Ω^0·ξ is ξ. *)
Lemma bequiv_one_mul ξ : bequiv (bmul (bexpΩ bzero) (embed ξ)) (embed ξ).
Proof.
  induction ξ as [X k IH].
  split; apply bsub_intro.
  - intros [[x s]|[]]. exists x.
    change (bsub (bsmallSz (badd (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero)) s) (embed (k x))).
    destruct (badd_small_cases (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) s) as [[a' E]|[b E]];
      rewrite E.
    + destruct (bsub_small _ _ (proj1 (IH x)) a') as [j Hj].
      eapply bsub_trans; [ exact Hj | ].
      destruct (k x) as [Y m]. apply bsub_embed. apply ord_lt_le, (index_lt (ord Y m) j).
    + rewrite bexpΩ_bzero_small.
      eapply bsub_trans; [ apply (proj1 (bequiv_badd_zero_r _)) | apply (proj1 (IH x)) ].
  - intros [[x c]|[]].
    destruct (badd_big_cases (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) c) as [[c' E]|[d E]].
    + destruct (bsub_big _ _ (proj1 (IH x)) c') as [d _]. elim (embed_big _ d).
    + elim (bexpΩ_bzero_big d).
  - intro x.
    destruct (bexpΩ_small_zero bzero) as [t0 Ht0].
    destruct (badd_small_r (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero) t0) as [s Hs].
    destruct (bmul_small_r (bexpΩ bzero) (embed (ord X k)) x s) as [t Ht].
    exists t. rewrite Ht.
    change (bsub (embed (k x)) (bsmallSz (badd (bmul (bexpΩ bzero) (embed (k x))) (bexpΩ bzero)) s)).
    rewrite Hs, Ht0.
    eapply bsub_trans; [ apply (proj2 (IH x)) | apply (proj2 (bequiv_badd_zero_r _)) ].
  - intros [].
Qed.

(** ** Transferring representations along @bequiv@ *)

Lemma BRep_bequiv f (Hf : forall x y, x ≤ y -> f x ≤ f y) T T' G :
  bequiv T T' -> bfam T -> bfam T' -> BRep f T G -> BRep f T' G.
Proof. intros [H1 H2] HT HT' HR. apply BRep_bsub_equiv with T; auto. Qed.

(** ** The base 1+x *)

(** Below Ω, with base 1+x, φ_α(y) = ω^α + y. *)
Theorem bphi_onePlus_embed α y : complete α -> complete y ->
  bphi (addOrd 1) (embed α) y ≈ expOrd ω α + y.
Proof.
  intros Hα Hy.
  rewrite (bphi_embed (addOrd 1) onePlus_normal α Hα y Hy).
  apply veblen_onePlus; auto.
Qed.

(** A node with a component has values that are fixpoints of 1+x,
    i.e., infinite. *)
Lemma bphi_onePlus_absorb T y : bgood (addOrd 1) T -> inhabited (bsmall T + bbig T) -> complete y ->
  1 + bphi (addOrd 1) T y ≈ bphi (addOrd 1) T y.
Proof.
  intros HT Hi Hy. split.
  - apply (bphi_fix_base' (addOrd 1) onePlus_normal T y HT Hi Hy).
  - apply addOrd_le2.
Qed.
