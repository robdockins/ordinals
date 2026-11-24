From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.

Unset Printing Records.

From Ordinal Require Import Defs.
From Ordinal Require Import Operators.
From Ordinal Require Import Arith.
From Ordinal Require Import Fixpoints.
From Ordinal Require Import VeblenDefs.
From Ordinal Require Import VeblenCon.
From Ordinal Require Import VeblenFacts.
From Ordinal Require Import AckermannTower.
From Ordinal Require Import SchutteColumn.
From Ordinal Require Import SchutteColumnFacts.

From Ordinal Require Import BachmannDefs.

Open Scope ord_scope.

(** * Associativity of addition and the invariant @bfam@ *)

(** ** Associativity of addition, up to φ

Tree addition is not syntactically associative, but it is associative
up to the family-respecting order @bsub@ in both directions, and hence
up to φ.  This is needed to shift the step theorems to an arbitrary
base: the components of β + (γ + δ) must be compared with those of
(β + γ) + δ. *)

Lemma bsub_trans x y z : bsub x y -> bsub y z -> bsub x z.
Proof.
  revert y z.
  induction x as [A g Hg C h Hh]; intros [B g' D h'] [E g'' F h''].
  simpl. intros [Hxy1 Hxy2] [Hyz1 Hyz2]. split.
  - intro a. destruct (Hxy1 a) as [b Hb]. destruct (Hyz1 b) as [e He].
    exists e. eapply Hg; eauto.
  - intro c. destruct (Hxy2 c) as [d Hd]. destruct (Hyz2 d) as [e He].
    exists e. intro ξ. eapply Hh; eauto.
Qed.

Lemma bsub_intro x y :
  (forall a, exists b, bsub (bsmallSz x a) (bsmallSz y b)) ->
  (forall c, exists d, forall ξ, bsub (bbigSz x c ξ) (bbigSz y d ξ)) ->
  bsub x y.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

(** The children of x + y: those of x, and x + (children of y). *)
Lemma badd_small_cases x y a :
  (exists a', bsmallSz (badd x y) a = bsmallSz x a') \/
  (exists b, bsmallSz (badd x y) a = badd x (bsmallSz y b)).
Proof.
  destruct x as [A g C h]; destruct y as [B k D l]; destruct a as [a0|b0].
  - left; exists a0; reflexivity.
  - right; exists b0; reflexivity.
Qed.

Lemma badd_big_cases x y c :
  (exists c', forall ξ, bbigSz (badd x y) c ξ = bbigSz x c' ξ) \/
  (exists d, forall ξ, bbigSz (badd x y) c ξ = badd x (bbigSz y d ξ)).
Proof.
  destruct x as [A g C h]; destruct y as [B k D l]; destruct c as [c0|d0].
  - left; exists c0; reflexivity.
  - right; exists d0; reflexivity.
Qed.

Lemma badd_small_l x y a' : exists a, bsmallSz (badd x y) a = bsmallSz x a'.
Proof. destruct x as [A g C h]; destruct y as [B k D l]; exists (inl a'); reflexivity. Qed.

Lemma badd_small_r x y b : exists a, bsmallSz (badd x y) a = badd x (bsmallSz y b).
Proof. destruct x as [A g C h]; destruct y as [B k D l]; exists (inr b); reflexivity. Qed.

Lemma badd_big_l x y c' : exists c, forall ξ, bbigSz (badd x y) c ξ = bbigSz x c' ξ.
Proof. destruct x as [A g C h]; destruct y as [B k D l]; exists (inl c'); reflexivity. Qed.

Lemma badd_big_r x y d : exists c, forall ξ, bbigSz (badd x y) c ξ = badd x (bbigSz y d ξ).
Proof. destruct x as [A g C h]; destruct y as [B k D l]; exists (inr d); reflexivity. Qed.

Lemma badd_assoc_1 α β : forall γ,
  bsub (badd (badd α β) γ) (badd α (badd β γ)).
Proof.
  intro γ.
  induction γ as [G g Hg D h Hh].
  apply bsub_intro.
  - intro s.
    destruct (badd_small_cases (badd α β) (bnode G g D h) s) as [[s' Hs]|[b Hs]]; rewrite Hs.
    + destruct (badd_small_cases α β s') as [[a Ha]|[b Hb]]; rewrite Ha || rewrite Hb.
      * destruct (badd_small_l α (badd β (bnode G g D h)) a) as [t Ht].
        exists t. rewrite Ht. apply bsub_refl.
      * destruct (badd_small_l β (bnode G g D h) b) as [u Hu].
        destruct (badd_small_r α (badd β (bnode G g D h)) u) as [t Ht].
        exists t. rewrite Ht, Hu. apply bsub_refl.
    + destruct (badd_small_r β (bnode G g D h) b) as [u Hu].
      destruct (badd_small_r α (badd β (bnode G g D h)) u) as [t Ht].
      exists t. rewrite Ht, Hu. apply Hg.
  - intro c.
    destruct (badd_big_cases (badd α β) (bnode G g D h) c) as [[c' Hc]|[d Hc]].
    + destruct (badd_big_cases α β c') as [[e He]|[e He]].
      * destruct (badd_big_l α (badd β (bnode G g D h)) e) as [t Ht].
        exists t. intro ξ. rewrite Hc, He, Ht. apply bsub_refl.
      * destruct (badd_big_l β (bnode G g D h) e) as [u Hu].
        destruct (badd_big_r α (badd β (bnode G g D h)) u) as [t Ht].
        exists t. intro ξ. rewrite Hc, He, Ht, Hu. apply bsub_refl.
    + destruct (badd_big_r β (bnode G g D h) d) as [u Hu].
      destruct (badd_big_r α (badd β (bnode G g D h)) u) as [t Ht].
      exists t. intro ξ. rewrite Hc, Ht, Hu. apply Hh.
Qed.

Lemma badd_assoc_2 α β : forall γ,
  bsub (badd α (badd β γ)) (badd (badd α β) γ).
Proof.
  intro γ.
  induction γ as [G g Hg D h Hh].
  apply bsub_intro.
  - intro s.
    destruct (badd_small_cases α (badd β (bnode G g D h)) s) as [[a Ha]|[u Hu]]; rewrite Ha || rewrite Hu.
    + destruct (badd_small_l α β a) as [v Hv].
      destruct (badd_small_l (badd α β) (bnode G g D h) v) as [t Ht].
      exists t. rewrite Ht, Hv. apply bsub_refl.
    + destruct (badd_small_cases β (bnode G g D h) u) as [[b Hb]|[b Hb]]; rewrite Hb.
      * destruct (badd_small_r α β b) as [v Hv].
        destruct (badd_small_l (badd α β) (bnode G g D h) v) as [t Ht].
        exists t. rewrite Ht, Hv. apply bsub_refl.
      * destruct (badd_small_r (badd α β) (bnode G g D h) b) as [t Ht].
        exists t. rewrite Ht. apply Hg.
  - intro c.
    destruct (badd_big_cases α (badd β (bnode G g D h)) c) as [[e He]|[u Hu]].
    + destruct (badd_big_l α β e) as [v Hv].
      destruct (badd_big_l (badd α β) (bnode G g D h) v) as [t Ht].
      exists t. intro ξ. rewrite He, Ht, Hv. apply bsub_refl.
    + destruct (badd_big_cases β (bnode G g D h) u) as [[e He]|[d Hd]].
      * destruct (badd_big_r α β e) as [v Hv].
        destruct (badd_big_l (badd α β) (bnode G g D h) v) as [t Ht].
        exists t. intro ξ. rewrite Hu, He, Ht, Hv. apply bsub_refl.
      * destruct (badd_big_r (badd α β) (bnode G g D h) d) as [t Ht].
        exists t. intro ξ. rewrite Hu, Hd, Ht. apply Hh.
Qed.

(** *** Monotonicity of the arithmetic in the order @bsub@ *)

Lemma bsub_badd_l x x' : bsub x x' -> forall y, bsub (badd x y) (badd x' y).
Proof.
  intros H y.
  induction y as [B g Hg D h Hh].
  rewrite (badd_eq x (bnode B g D h)), (badd_eq x' (bnode B g D h)).
  apply bsub_blub; auto.
  unfold baddR; simpl; split.
  - intro b. exists b. apply Hg.
  - intro d. exists d. intro ξ. apply Hh.
Qed.

Lemma bsub_badd_r x : forall y y', bsub y y' -> bsub (badd x y) (badd x y').
Proof.
  intro y.
  induction y as [B g Hg D h Hh]; intros [B' g' D' h'] H.
  rewrite (badd_eq x (bnode B g D h)), (badd_eq x (bnode B' g' D' h')).
  apply bsub_blub; [ apply bsub_refl | ].
  unfold baddR; simpl in *.
  destruct H as [H1 H2]; split.
  - intro b. destruct (H1 b) as [b' Hb]. exists b'. apply Hg; auto.
  - intro d. destruct (H2 d) as [d' Hd]. exists d'. intro ξ. apply Hh; auto.
Qed.

Lemma bsub_bmul_r x : forall y y', bsub y y' -> bsub (bmul x y) (bmul x y').
Proof.
  intro y.
  induction y as [B g Hg D h Hh]; intros y' H.
  rewrite (bmul_eq x (bnode B g D h)), (bmul_eq x y').
  apply bsub_blub.
  - unfold bmulS. apply bsub_bsup. intro b.
    destruct (bsub_small _ _ H b) as [b' Hb].
    exists b'. apply bsub_badd_l. apply Hg. exact Hb.
  - unfold bmulB; simpl. split; [ intros [] | ].
    intro d. destruct (bsub_big _ _ H d) as [d' Hd].
    exists d'. intro ξ. apply Hh. apply Hd.
Qed.

Lemma bsub_bmul_l x x' : bsub x x' -> forall y, bsub (bmul x y) (bmul x' y).
Proof.
  intros H y.
  induction y as [B g Hg D h Hh].
  rewrite (bmul_eq x (bnode B g D h)), (bmul_eq x' (bnode B g D h)).
  apply bsub_blub.
  - unfold bmulS. apply bsub_bsup. intro b.
    exists b.
    eapply bsub_trans; [ apply bsub_badd_l, Hg | apply bsub_badd_r, H ].
  - unfold bmulB; simpl. split; [ intros [] | ].
    intro d. exists d. intro ξ. apply Hh.
Qed.

Lemma bsub_bexpΩ : forall y y', bsub y y' -> bsub (bexpΩ y) (bexpΩ y').
Proof.
  intro y.
  induction y as [B g Hg D h Hh]; intros y' H.
  rewrite (bexpΩ_eq (bnode B g D h)), (bexpΩ_eq y').
  apply bsub_blub; [ apply bsub_refl | apply bsub_blub ].
  - unfold bexpS. apply bsub_bsup. intro b.
    destruct (bsub_small _ _ H b) as [b' Hb].
    exists b'. apply bsub_bmul_l. apply Hg. exact Hb.
  - unfold bexpB; simpl. split; [ intros [] | ].
    intro d. destruct (bsub_big _ _ H d) as [d' Hd].
    exists d'. intro ξ. apply Hh. apply Hd.
Qed.

Lemma bsub_embed : forall ξ ξ', ξ ≤ ξ' -> bsub (embed ξ) (embed ξ').
Proof.
  induction ξ as [X k Hk]; intros [X' k'] H; simpl.
  split; [ | intros [] ].
  intro a. destruct (ord_le_subord _ _ H a) as [b Hb].
  exists b. apply Hk. exact Hb.
Qed.

(** *** The invariant @bfam@: every Ω-family is @bsub@-monotone *)

Fixpoint bfam (x:BOrd) : Prop :=
  match x with
  | bnode A g C h =>
    (forall a, bfam (g a)) /\
    (forall c ξ, bfam (h c ξ)) /\
    (forall c ξ ξ', ξ ≤ ξ' -> bsub (h c ξ) (h c ξ'))
  end.

Lemma bfam_bmono f (Hf : forall x y, x ≤ y -> f x ≤ f y) : forall x, bfam x -> bmono f x.
Proof.
  induction x as [A g Hg C h Hh]; simpl.
  intros [H1 [H2 H3]].
  split; [ | split ]; auto.
  intros c ξ ξ' H.
  apply bach_mono_index; auto.
Qed.

Lemma bfam_small x : bfam x -> forall a, bfam (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bfam_big x : bfam x -> forall c ξ, bfam (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bfam_fam x : bfam x -> forall c ξ ξ', ξ ≤ ξ' -> bsub (bbigSz x c ξ) (bbigSz x c ξ').
Proof. destruct x; simpl; intuition. Qed.

Lemma bfam_blub x y : bfam x -> bfam y -> bfam (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [H1 [H2 H3]] [H1' [H2' H3']].
  split; [ | split ].
  - intros [a|b]; auto.
  - intros [c|d] ξ; auto.
  - intros [c|d]; [ apply H3 | apply H3' ].
Qed.

Lemma bfam_bsup {I:Type} (F:I -> BOrd) : (forall i, bfam (F i)) -> bfam (bsup F).
Proof.
  intro H; simpl.
  split; [ | split ].
  - intros [i a]. apply bfam_small; auto.
  - intros [i c] ξ. apply bfam_big; auto.
  - intros [i c] ξ ξ' Hξ. apply bfam_fam; auto.
Qed.

Lemma bfam_bzero : bfam bzero.
Proof. simpl; split; [ intros [] | split; intros [] ]. Qed.

Lemma bfam_bsucc x : bfam x -> bfam (bsucc x).
Proof. intro H; simpl; split; [ auto | split; intros [] ]. Qed.

Lemma bfam_embed ξ : bfam (embed ξ).
Proof. induction ξ as [X k Hk]; simpl; split; [ auto | split; intros [] ]. Qed.

Lemma bfam_Ω : bfam bOmega.
Proof.
  simpl; split; [ intros [] | split ].
  - intros _ ξ; apply bfam_embed.
  - intros _ ξ ξ' H; apply bsub_embed; auto.
Qed.

Lemma bfam_badd x y : bfam x -> bfam y -> bfam (badd x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intro Hy.
  destruct Hy as [Hy1 [Hy2 Hy3]].
  rewrite (badd_eq x (bnode B g D h)).
  apply bfam_blub; auto.
  unfold baddR; simpl.
  split; [ | split ].
  - intro b. apply Hg; auto.
  - intros d ξ. apply Hh; auto.
  - intros d ξ ξ' H. apply bsub_badd_r; auto.
Qed.

Lemma bfam_bmul x y : bfam x -> bfam y -> bfam (bmul x y).
Proof.
  intro Hx.
  induction y as [B g Hg D h Hh]; intro Hy.
  destruct Hy as [Hy1 [Hy2 Hy3]].
  rewrite (bmul_eq x (bnode B g D h)).
  apply bfam_blub.
  - unfold bmulS. apply bfam_bsup. intro b.
    apply bfam_badd; auto.
  - unfold bmulB; simpl.
    split; [ intros [] | split ].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bmul_r; auto.
Qed.

Lemma bfam_bexpΩ y : bfam y -> bfam (bexpΩ y).
Proof.
  induction y as [B g Hg D h Hh]; intro Hy.
  destruct Hy as [Hy1 [Hy2 Hy3]].
  rewrite (bexpΩ_eq (bnode B g D h)).
  apply bfam_blub; [ apply bfam_bsucc, bfam_bzero | apply bfam_blub ].
  - unfold bexpS. apply bfam_bsup. intro b.
    apply bfam_bmul; auto using bfam_Ω.
  - unfold bexpB; simpl.
    split; [ intros [] | split ].
    + intros d ξ. apply Hh; auto.
    + intros d ξ ξ' H. apply bsub_bexpΩ; auto.
Qed.

Lemma bfam_btower n : bfam (btower n).
Proof.
  induction n.
  - change (bfam (bsucc bOmega)). apply bfam_bsucc, bfam_Ω.
  - change (bfam (bexpΩ (btower n))). apply bfam_bexpΩ; auto.
Qed.

Lemma bfam_bεΩ1 : bfam bεΩ1.
Proof.
  simpl; split; [ apply bfam_btower | split; intros [] ].
Qed.

(** Trees that are @bsub@-equivalent have the same φ. *)
Lemma bach_bsub_eq f (Hf : forall x y, x ≤ y -> f x ≤ f y) x y :
  bsub x y -> bsub y x -> bfam x -> bfam y -> forall z, bach f x z ≈ bach f y z.
Proof.
  intros Hxy Hyx Hx Hy z; split;
    apply bach_mono_index; auto; apply bfam_bmono; auto.
Qed.

Theorem bach_badd_assoc f (Hf : forall x y, x ≤ y -> f x ≤ f y) α β γ :
  bfam α -> bfam β -> bfam γ ->
  forall z, bach f (badd α (badd β γ)) z ≈ bach f (badd (badd α β) γ) z.
Proof.
  intros Hα Hβ Hγ.
  apply bach_bsub_eq; auto using badd_assoc_1, badd_assoc_2, bfam_badd.
Qed.
