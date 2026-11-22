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

(** ** z-relative strict reachability

[zlt z x y]: x lies strictly below a tree D that is reachable from y
through small children and family members at arguments at most z.
If z is a common fixpoint of y's components, then φ_x fixes z. *)

Definition zlt (z:Ord) (x y:BOrd) : Prop := exists D, bslt x D /\ bleZ z D y.

Lemma zlt_bslt z x y : bslt x y -> zlt z x y.
Proof. intro H. exists y. split; auto. apply LZ_sub, bsub_refl. Qed.

Lemma zlt_mono_r z x y y' : zlt z x y -> bsub y y' -> zlt z x y'.
Proof. intros [D [H1 H2]] H. exists D. split; auto. eapply bleZ_mono_r; eauto. Qed.

Lemma zlt_mono_l z x x' y : bsub x' x -> zlt z x y -> zlt z x' y.
Proof. intros H [D [H1 H2]]. exists D. split; auto. eapply bslt_bsub_l; eauto. Qed.

Lemma zlt_shift z w x y : zlt z x y -> zlt z (badd w x) (badd w y).
Proof. intros [D [H1 H2]]. exists (badd w D). split; [ apply bslt_badd_r | apply bleZ_shift ]; auto. Qed.

Lemma zlt_big z x y t ξ : zlt z x (bbigSz y t ξ) -> ξ ≤ z -> zlt z x y.
Proof. intros [D [H1 H2]] Hξ. exists D. split; auto. apply (LZ_big _ _ _ t ξ Hξ); auto. Qed.

Lemma zlt_nest f (Hf : normal_function f) z x y :
  zlt z x y -> bgood f y -> bfam y -> complete z -> bfix f y z -> bphi f x z ≤ z.
Proof.
  intros [D [H1 H2]] Hg Hfam Hz Hfix.
  apply (bleZ_nest f Hf z D y x H2 H1 y (bsub_refl y)); auto.
Qed.

(** ** Indices below Ω^Ω

An index below Ω^Ω is a list of pairs (ζ, c) standing for
Ω^{ζ₁}·c₁ + … + Ω^{ζₙ}·cₙ with small ζ and c. *)

Definition oterm (p:Ord * Ord) : BOrd := bmul (bexpΩ (embed (fst p))) (embed (snd p)).

Fixpoint osum (l:list (Ord * Ord)) : BOrd :=
  match l with
  | [] => bzero
  | p :: l' => badd (oterm p) (osum l')
  end.

Definition ofold (acc:BOrd) (l:list (Ord * Ord)) : BOrd :=
  fold_left (fun acc p => badd acc (oterm p)) l acc.

Lemma bequiv_badd_assoc a b c : bequiv (badd (badd a b) c) (badd a (badd b c)).
Proof. split; [ apply badd_assoc_1 | apply badd_assoc_2 ]. Qed.

Lemma ofold_osum l : forall acc, bequiv (ofold acc l) (badd acc (osum l)).
Proof.
  induction l as [|p l IH]; intro acc; simpl.
  - apply bequiv_sym, bequiv_badd_zero_r.
  - eapply bequiv_trans; [ apply IH | ].
    apply bequiv_badd_assoc.
Qed.

(** Exponents strictly decreasing and bounded by ζ; coefficients positive. *)
Fixpoint odesc (ζ:Ord) (l:list (Ord * Ord)) : Prop :=
  match l with
  | [] => True
  | (e, c) :: l' => e < ζ /\ 0 < c /\ odesc e l'
  end.

Definition onormal (l:list (Ord * Ord)) : Prop :=
  match l with
  | [] => True
  | (e, c) :: l' => 0 < c /\ odesc e l'
  end.

Lemma odesc_onormal ζ l : odesc ζ l -> onormal l.
Proof. destruct l as [|[e c] l]; simpl; intuition. Qed.

Definition ocoef_lt (z:Ord) (l:list (Ord * Ord)) : Prop := each (fun p => snd p < z) l.

Definition oinf (z:Ord) : Prop := forall n, natOrdSize n ≤ z.

Lemma oterm_pos e c : 0 < c -> bpos (oterm (e, c)).
Proof.
  intro Hc. unfold oterm; simpl.
  apply bslt_bsub_r with (bexpΩ (embed e)); [ apply bpos_bexpΩ | apply bsub_P_Pz; auto ].
Qed.

(** P·c + P lies below P·(c+1). *)
Lemma bsub_mul_succ P c : bsub (badd (bmul P (embed c)) P) (bmul P (embed (succOrd c))).
Proof. exact (bsub_bmul_step P (embed (succOrd c)) tt). Qed.

(** A sum with exponents below ζ, and coefficients below z, is
    z-reachably below Ω^ζ. *)
Lemma osum_below l : forall ζ z, odesc ζ l -> ocoef_lt z l -> zlt z (osum l) (bexpΩ (embed ζ)).
Proof.
  induction l as [|[e c] l IH]; intros ζ z Hd Hc; simpl in *.
  - apply zlt_bslt, bpos_bexpΩ.
  - destruct Hd as [He [Hc0 Hd]]. destruct Hc as [Hcz Hc].
    destruct ζ as [Z k]. rewrite ord_lt_unfold in He. destruct He as [j Hj].
    destruct (bexpΩ_fam_s (embed (ord Z k)) j) as [t Ht].
    apply (zlt_big z _ _ t (succOrd c)); [ | apply succ_least; auto ].
    rewrite Ht. change (bsmallSz (embed (ord Z k)) j) with (embed (k j)).
    apply zlt_mono_r with (bmul (bexpΩ (embed e)) (embed (succOrd c))).
    + apply zlt_mono_r with (badd (bmul (bexpΩ (embed e)) (embed c)) (bexpΩ (embed e))).
      * apply zlt_shift. apply IH; auto.
      * apply bsub_mul_succ.
    + apply bsub_bmul_l, bsub_bexpΩ, bsub_embed; auto.
Qed.

(** Lexicographic order on Ω-Cantor normal forms below Ω^Ω. *)
Inductive olt : list (Ord * Ord) -> list (Ord * Ord) -> Prop :=
| olt_nil : forall p l, olt [] (p :: l)
| olt_exp : forall e c l e' c' l', e < e' -> olt ((e, c) :: l) ((e', c') :: l')
| olt_coef : forall e c l e' c' l', e ≈ e' -> c < c' -> olt ((e, c) :: l) ((e', c') :: l')
| olt_tail : forall e c l e' c' l', e ≈ e' -> c ≈ c' -> olt l l' -> olt ((e, c) :: l) ((e', c') :: l').

Lemma osum_pos p l : 0 < snd p -> bpos (osum (p :: l)).
Proof.
  destruct p as [e c]. intro Hc. simpl.
  apply bslt_bsub_r with (oterm (e, c)); [ apply oterm_pos; auto | apply bsub_le_badd ].
Qed.

Lemma bsub_oterm e c e' c' : e ≤ e' -> c ≤ c' -> bsub (oterm (e, c)) (oterm (e', c')).
Proof.
  intros He Hc. unfold oterm; simpl.
  eapply bsub_trans; [ apply bsub_bmul_l, bsub_bexpΩ, bsub_embed, He | ].
  apply bsub_bmul_r, bsub_embed; auto.
Qed.

(** The nesting theorem below Ω^Ω: a lexicographically smaller index is
    z-reachably below a larger one, provided its coefficients are below z. *)
Theorem olt_zlt l l' z : olt l l' -> onormal l -> onormal l' -> ocoef_lt z l ->
  zlt z (osum l) (osum l').
Proof.
  intro H. induction H as [p l | e c l e' c' l' He | e c l e' c' l' He Hc | e c l e' c' l' He Hc H IH];
    intros Hn Hn' Hz.
  - destruct p as [e c]. apply zlt_bslt, osum_pos. apply Hn'.
  - simpl in Hn, Hn'. destruct Hn' as [Hc' _].
    apply zlt_mono_r with (bexpΩ (embed e')).
    + apply (osum_below ((e, c) :: l)); simpl; intuition.
    + eapply bsub_trans; [ apply bsub_P_Pz, Hc' | apply bsub_le_badd ].
  - simpl in Hn, Hn'. destruct Hz as [_ Hz].
    simpl. apply zlt_mono_r with (badd (oterm (e, c)) (bexpΩ (embed e))).
    + apply zlt_shift, osum_below; intuition.
    + eapply bsub_trans; [ apply bsub_mul_succ | ].
      eapply bsub_trans; [ apply (bsub_oterm e (succOrd c) e' c'); [ apply He | apply succ_least, Hc ] | ].
      apply bsub_le_badd.
  - simpl in Hn, Hn'. destruct Hz as [_ Hz].
    simpl. apply zlt_mono_r with (badd (oterm (e, c)) (osum l')).
    + apply zlt_shift, IH; auto.
      * apply odesc_onormal with e; apply Hn.
      * apply odesc_onormal with e'; apply Hn'.
    + apply bsub_badd_l, bsub_oterm; [ apply He | apply Hc ].
Qed.

(** ** Semantic consequences *)

(** Values of a node with a component are common fixpoints of f and the
    node's components. *)
Lemma bfix_value_full f (Hf : normal_function f) y w :
  bgood f y -> inhabited (bsmall y + bbig y) -> complete w -> bfix f y (bphi f y w).
Proof.
  intros Hy Hi Hw. split; [ | split ].
  - apply bphi_fix_base'; auto.
  - intro a. apply bphi_fix_small'; auto.
  - intro c. apply bphi_fix_big'; auto.
Qed.

(** If x is z-reachably below y at a value z of φ_y, then z is a
    fixpoint of φ_x. *)
Lemma zlt_value f (Hf : normal_function f) x y w :
  zlt (bphi f y w) x y -> bgood f y -> bfam y -> inhabited (bsmall y + bbig y) -> complete w ->
  bphi f x (bphi f y w) ≤ bphi f y w.
Proof.
  intros H Hg Hfam Hi Hw.
  apply (zlt_nest f Hf _ x y H Hg Hfam); [ apply bphi_complete; auto | apply bfix_value_full; auto ].
Qed.

(** φ depends only on the tree up to @bequiv@. *)
Lemma bphi_bequiv f (Hf : forall x y, x ≤ y -> f x ≤ f y) T T' y :
  bequiv T T' -> bfam T -> bfam T' -> bphi f T y ≈ bphi f T' y.
Proof.
  intros [H1 H2] HT HT'. split.
  - apply (proj2 (bphi_mono_index f Hf T' HT')); auto.
  - apply (proj2 (bphi_mono_index f Hf T HT)); auto.
Qed.

(** Entrywise equal indices give equivalent trees. *)
Inductive oeq : list (Ord * Ord) -> list (Ord * Ord) -> Prop :=
| oeq_nil : oeq [] []
| oeq_cons : forall e c l e' c' l', e ≈ e' -> c ≈ c' -> oeq l l' -> oeq ((e, c) :: l) ((e', c') :: l').

Lemma oeq_osum l l' : oeq l l' -> bequiv (osum l) (osum l').
Proof.
  intro H. induction H as [|e c l e' c' l' He Hc H IH]; simpl; [ apply bequiv_refl | ].
  apply bequiv_badd; auto.
  unfold oterm; simpl. apply bequiv_bmul; [ apply bequiv_bexpΩ | ]; apply bequiv_embed; auto.
Qed.

Lemma bfam_oterm p : bfam (oterm p).
Proof. unfold oterm. apply bfam_bmul; [ apply bfam_bexpΩ | ]; apply bfam_embed. Qed.

Lemma bfam_osum l : bfam (osum l).
Proof. induction l; simpl; [ apply bfam_bzero | apply bfam_badd; auto using bfam_oterm ]. Qed.

Lemma bfam_ofold l : forall acc, bfam acc -> bfam (ofold acc l).
Proof. induction l; simpl; intros; auto. apply IHl, bfam_badd; auto using bfam_oterm. Qed.

(** ** Indices below Ω^Ω and Klammersymbols

Adding the summand Ω^ζ·c to an index adds the column (1+ζ, c) to the
Klammersymbol it represents (@bach_bexpΩ_rep@). *)

Definition ocols (l:list (Ord * Ord)) : list (Ord * Ord) := map (fun p => (1 + fst p, snd p)) l.

Lemma schutte_matrix_app f m1 m2 : forall x, schutte_matrix f (m1 ++ m2) x = schutte_matrix (schutte_matrix f m1) m2 x.
Proof. revert f. induction m1 as [|[b a] m1 IH]; intros f x; simpl; auto. Qed.

Theorem ofold_rep f (Hf : forall x y, x ≤ y -> f x ≤ f y) l : forall acc G,
  bfam acc -> BRep f acc G ->
  each (fun p => complete (fst p) /\ complete (snd p)) l ->
  BRep f (ofold acc l) (schutte_matrix G (ocols l)).
Proof.
  induction l as [|[e c] l IH]; intros acc G Hacc HR Hl; simpl in *; auto.
  destruct Hl as [[He Hc] Hl].
  apply IH; auto.
  - apply bfam_badd; auto using bfam_oterm.
  - apply bach_bexpΩ_rep; auto.
Qed.

(** Entrywise equal Klammersymbols denote the same function. *)
Inductive meq : list (Ord * Ord) -> list (Ord * Ord) -> Prop :=
| meq_nil : meq [] []
| meq_cons : forall b a m b' a' m', b ≈ b' -> a ≈ a' -> meq m m' -> meq ((b, a) :: m) ((b', a') :: m').

Lemma schutte_matrix_meq m m' : meq m m' -> forall f, (forall x y, x ≤ y -> f x ≤ f y) ->
  forall x, schutte_matrix f m x ≈ schutte_matrix f m' x.
Proof.
  intro H. induction H as [|b a m b' a' m' Hb Ha H IH]; intros f Hf x; simpl; [ reflexivity | ].
  rewrite IH; [ | intros; apply schutte_column_monotone; auto with ord ].
  split; apply schutte_matrix_monotone_func;
    try (intros; apply schutte_column_monotone; auto with ord);
    intro y; apply schutte_column_monotone_full; auto with ord; first [ apply Hb | apply Ha ].
Qed.

(** ** Reachability through exponents *)

Lemma zlt_bleZ z x y w : zlt z x y -> bleZ z y w -> zlt z x w.
Proof. intros [D [H1 H2]] H. exists D. split; auto. eapply bleZ_trans; eauto. Qed.

(** If a is z-reachably below b, then Ω^a·z is z-reachable from Ω^b. *)
Lemma zlt_exp z a b : zlt z a b -> oinf z -> bleZ z (bmul (bexpΩ a) (embed z)) (bexpΩ b).
Proof.
  intros [D [H1 H2]] Hz.
  eapply bleZ_trans; [ apply (bleZ_exp_lt a D H1 z Hz) | apply bleZ_exp; auto ].
Qed.

(** A value of a node with a component is infinite. *)
Lemma bphi_value_inf f (Hf : normal_function f) y w :
  (forall x, x ≤ f x) -> (forall x, complete x -> 1 + x ≤ f x) ->
  bgood f y -> inhabited (bsmall y + bbig y) -> complete w -> oinf (bphi f y w).
Proof.
  intros _ H1 Hg Hi Hw n.
  apply (fix_onePlus_finite (addOrd 1) onePlus_normal); [ apply bphi_complete; auto | ].
  transitivity (f (bphi f y w)); [ apply H1, bphi_complete; auto | ].
  apply bphi_fix_base'; auto.
Qed.

(** ** Dominance through strict contexts

A context is a tree with an ordinal hole that is canonical at complete
arguments and strictly increasing in the structural order @bslt@.
Along a context, ξ ↦ φ_{C ξ}(0) is strictly increasing, hence at least
ξ.  Contexts are built from @embed@ by adding on the left, multiplying
by a positive tree on the left, and exponentiating; together with
@bsub@-monotonicity this places every coefficient of an index below
φ_T(0). *)

Definition bctx (C:Ord -> BOrd) : Prop :=
  (forall ξ, complete ξ -> bcd (C ξ)) /\
  (forall ξ ξ', complete ξ' -> ξ < ξ' -> bslt (C ξ) (C ξ')).

Theorem bctx_dom f (Hf : normal_function f) C : bctx C -> forall ξ, complete ξ -> ξ ≤ bphi f (C ξ) 0.
Proof.
  intros [Hcd Hlt]. induction ξ as [X g IH]; intro Hc.
  rewrite ord_le_unfold. intro j.
  assert (Hj : complete (g j)) by (apply (complete_subord (ord X g)); auto).
  apply ord_le_lt_trans with (bphi f (C (g j)) 0); [ apply IH; auto | ].
  destruct (Hcd _ Hc) as [H1 H2].
  destruct (bcanon_good f Hf _ H1 H2) as [Hfam Hgood].
  apply bphi_strict; auto. apply Hlt; auto. apply (index_lt (ord X g) j).
Qed.

Lemma bslt_embed ξ ξ' : ξ < ξ' -> bslt (embed ξ) (embed ξ').
Proof.
  destruct ξ' as [X k]. intro H. rewrite ord_lt_unfold in H. destruct H as [j Hj].
  apply (bslt_small (embed ξ) (embed (ord X k)) j).
  change (bsub (embed ξ) (embed (k j))). apply bsub_embed; auto.
Qed.

Lemma bctx_embed : bctx embed.
Proof. split; [ apply bcd_embed | intros; apply bslt_embed; auto ]. Qed.

Lemma bctx_add A C : bcd A -> bctx C -> bctx (fun ξ => badd A (C ξ)).
Proof.
  intros HA [H1 H2]. split; intros.
  - apply bcd_badd; auto.
  - apply bslt_badd_r; auto.
Qed.

Lemma bctx_mul P C : bcd P -> bpos P -> bctx C -> bctx (fun ξ => bmul P (C ξ)).
Proof.
  intros HP Hp [H1 H2]. split; intros.
  - apply bcd_bmul; auto.
  - apply bslt_bmul_r; auto.
Qed.

Lemma bctx_exp C : bctx C -> bctx (fun ξ => bexpΩ (C ξ)).
Proof.
  intros [H1 H2]. split; intros.
  - apply bcd_bexpΩ; auto.
  - apply bslt_bexpΩ; auto.
Qed.

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

  Lemma wev_fix w z x : f z ≤ z -> (forall i, F i z ≤ z) -> x ≤ z -> wev w x ≤ z.
  Proof.
    intros H1 H2 Hx. induction w as [|[i|] w IH]; simpl; auto.
    - transitivity (F i z); auto. apply normal_monotone; auto.
    - transitivity (f z); auto. apply normal_monotone; auto.
  Qed.

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

(** ** The children of Ω^e·γ *)

Lemma bexpΩ_small_all y t : bsmallSz (bexpΩ y) t = bzero.
Proof. destruct y as [B g D h]. destruct t as [[]|[[b [[[] _]|[]]]|[]]]; reflexivity. Qed.

Lemma bexpΩ_big_cases y k :
  (exists q, forall ξ, bbigSz (bexpΩ y) k ξ = bmul (bexpΩ (bsmallSz y q)) (embed ξ)) \/
  (exists d, forall ξ, bbigSz (bexpΩ y) k ξ = bexpΩ (bbigSz y d ξ)).
Proof.
  destruct y as [B g D h].
  destruct k as [[]|[[b [[[] _]|[]]]|d]].
  - left. exists b. intro; reflexivity.
  - right. exists d. intro; reflexivity.
Qed.

(** The children of E·γ₀ are E·γ + K, for γ < γ₀ and K a child of E. *)
Lemma mul_small_form E : forall γ0 a, exists γ, γ < γ0 /\ exists k,
  bsmallSz (bmul E (embed γ0)) a = badd (bmul E (embed γ)) (bsmallSz E k).
Proof.
  induction γ0 as [G g IH]. intros [[j s]|[]].
  change (exists γ, γ < ord G g /\ exists k,
    bsmallSz (badd (bmul E (embed (g j))) E) s = badd (bmul E (embed γ)) (bsmallSz E k)).
  destruct (badd_small_cases (bmul E (embed (g j))) E s) as [[a' Ea]|[k Ek]].
  - rewrite Ea. destruct (IH j a') as [γ [Hγ [k Hk]]]. exists γ. split; [ | exists k; auto ].
    eapply ord_lt_trans; [ exact Hγ | apply (index_lt (ord G g) j) ].
  - rewrite Ek. exists (g j). split; [ apply (index_lt (ord G g) j) | exists k; auto ].
Qed.

Lemma mul_big_form E : forall γ0 d, exists γ, γ < γ0 /\ exists k, forall ξ,
  bbigSz (bmul E (embed γ0)) d ξ = badd (bmul E (embed γ)) (bbigSz E k ξ).
Proof.
  induction γ0 as [G g IH]. intros [[j s]|[]].
  change (exists γ, γ < ord G g /\ exists k, forall ξ,
    bbigSz (badd (bmul E (embed (g j))) E) s ξ = badd (bmul E (embed γ)) (bbigSz E k ξ)).
  destruct (badd_big_cases (bmul E (embed (g j))) E s) as [[a' Ea]|[k Ek]].
  - destruct (IH j a') as [γ [Hγ [k Hk]]]. exists γ. split.
    + eapply ord_lt_trans; [ exact Hγ | apply (index_lt (ord G g) j) ].
    + exists k. intro ξ. rewrite Ea. auto.
  - exists (g j). split; [ apply (index_lt (ord G g) j) | exists k; intro ξ; rewrite Ek; auto ].
Qed.

Lemma mul_small_back E (γ0:Ord) (j:γ0) k : exists a,
  bsmallSz (bmul E (embed γ0)) a = badd (bmul E (embed (γ0 j))) (bsmallSz E k).
Proof.
  destruct γ0 as [G g].
  destruct (badd_small_r (bmul E (embed (g j))) E k) as [s Hs].
  destruct (bmul_small_r E (embed (ord G g)) j s) as [t Ht].
  exists t. rewrite Ht. exact Hs.
Qed.

Lemma mul_big_back E (γ0:Ord) (j:γ0) k : exists d, forall ξ,
  bbigSz (bmul E (embed γ0)) d ξ = badd (bmul E (embed (γ0 j))) (bbigSz E k ξ).
Proof.
  destruct γ0 as [G g].
  destruct (badd_big_r (bmul E (embed (g j))) E k) as [s Hs].
  destruct (bmul_big_r E (embed (ord G g)) j s) as [t Ht].
  exists t. intro ξ. rewrite Ht. apply Hs.
Qed.

Lemma bsub_mul_zero x : bsub (bmul x (embed 0)) bzero.
Proof. apply bsub_intro; intros [[[] _]|[]]. Qed.

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
