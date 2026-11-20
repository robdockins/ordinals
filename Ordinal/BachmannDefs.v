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

Open Scope ord_scope.

(** * Bachmann's hierarchy, over Brouwer trees with two kinds of branching.

Bachmann indexes his hierarchy of normal functions φ_α by ordinals
α that may exceed Ω, and he equips each limit α with a fundamental
sequence of length either ω or Ω.  The two cases are treated
differently: at a limit of cofinality ω we take common fixpoints,
just as in the Veblen hierarchy; but at a limit of cofinality Ω we
diagonalize, enumerating those ξ which are fixpoints of the single
function ξ ↦ φ_{α[ξ]}(0).

Here we follow the uniform presentation of @Ord@: there is no
separate zero/successor/limit case analysis.  A node of an index tree
carries two kinds of children:

 - a family of "small" children @g : A -> BOrd@, indexed by an
   arbitrary small type, which are strict predecessors of the node
   and are treated by the Veblen "intersect" rule; and

 - a small-indexed collection of "Ω-families" @h : C -> Ord -> BOrd@,
   each of which is a fundamental sequence of length Ω, treated by
   Bachmann's "diagonalize" rule.

Branching over @Ord@ plays the role of cofinality Ω.  Note that Ω need
not be "the first uncountable ordinal" here; it is simply the type of
ordinals of the universe below, and its regularity comes from universe
stratification rather than from a choice principle.

Allowing both kinds of children in a single node (rather than having
one constructor for each kind) is what makes index trees closed under
binary and small suprema, and hence under the arithmetic operations,
which are defined just as for @Ord@.

Because @BOrd@ branches over @Ord@, it lives in a strictly larger
universe; we never attempt to embed @BOrd@ back into @Ord@.  The
function @bach@ is defined by plain structural recursion.
*)

Inductive BOrd : Type :=
  bnode : forall (A:Type), (A -> BOrd) ->
          forall (C:Type), (C -> Ord -> BOrd) -> BOrd.

Definition bsmall (x:BOrd) : Type :=
  match x with bnode A _ _ _ => A end.
Definition bsmallSz (x:BOrd) : bsmall x -> BOrd :=
  match x with bnode _ g _ _ => g end.
Definition bbig (x:BOrd) : Type :=
  match x with bnode _ _ C _ => C end.
Definition bbigSz (x:BOrd) : bbig x -> Ord -> BOrd :=
  match x with bnode _ _ _ h => h end.

(** ** The ordering on index trees

A node denotes the strict supremum of all of its children, where each
member of an Ω-family counts as a child.  The ordering is therefore
the same game as for @Ord@, with moves drawn from @A + C*Ord@.  This
is the ordering of indices only; it makes no reference to @bach@.
The two kinds of children are distinguished only by how @bach@
treats them.
*)

Definition bidx (x:BOrd) : Type := (bsmall x + bbig x * Ord)%type.

Definition bchild (x:BOrd) (i:bidx x) : BOrd :=
  match i with
  | inl a => bsmallSz x a
  | inr (c, ξ) => bbigSz x c ξ
  end.

Fixpoint blt (x y:BOrd) {struct x} : Prop :=
  match x, y with
  | bnode A g C h, bnode B g' D h' =>
    exists j:(B + D*Ord)%type, forall i:(A + C*Ord)%type,
      blt (match i with inl a => g a | inr (c, ξ) => h c ξ end)
          (match j with inl b => g' b | inr (d, ζ) => h' d ζ end)
  end.

Definition ble (x y:BOrd) : Prop :=
  match x with
  | bnode A g C h =>
    forall i:(A + C*Ord)%type, blt (match i with inl a => g a | inr (c, ξ) => h c ξ end) y
  end.

Definition beq (x y:BOrd) : Prop := ble x y /\ ble y x.

Lemma blt_unfold x y : blt x y = exists j:bidx y, ble x (bchild y j).
Proof.
  destruct x; destruct y; reflexivity.
Qed.

Lemma ble_unfold x y : ble x y = forall i:bidx x, blt (bchild x i) y.
Proof.
  destruct x; reflexivity.
Qed.

Global Opaque blt ble.

Lemma BOrd_child_ind (P:BOrd -> Prop) :
  (forall x, (forall i:bidx x, P (bchild x i)) -> P x) ->
  forall x, P x.
Proof.
  intros H.
  induction x as [A g Hg C h Hh].
  apply H. intros [a|[c ξ]]; simpl; auto.
Qed.

Lemma blt_le : forall b a, blt a b -> ble a b.
Proof.
  induction b as [b Hind] using BOrd_child_ind.
  intros a Ha.
  rewrite blt_unfold in Ha.
  destruct Ha as [j Hj].
  rewrite ble_unfold in *.
  intro i.
  rewrite blt_unfold.
  exists j. apply Hind. auto.
Qed.

Lemma ble_refl x : ble x x.
Proof.
  induction x as [x Hind] using BOrd_child_ind.
  rewrite ble_unfold; intro i.
  rewrite blt_unfold.
  exists i. apply Hind.
Qed.

Lemma bindex_lt (x:BOrd) (i:bidx x) : blt (bchild x i) x.
Proof.
  rewrite blt_unfold.
  exists i. apply ble_refl.
Qed.

Lemma bindex_le (x:BOrd) (i:bidx x) : ble (bchild x i) x.
Proof.
  apply blt_le. apply bindex_lt.
Qed.

Lemma ble_trans a b c : ble a b -> ble b c -> ble a c.
Proof.
  revert b c.
  induction a as [a Hind] using BOrd_child_ind.
  intros b c Hab Hbc.
  rewrite ble_unfold; intro ai.
  rewrite ble_unfold in Hab. specialize (Hab ai).
  rewrite blt_unfold in Hab. destruct Hab as [bi Hab].
  rewrite ble_unfold in Hbc. specialize (Hbc bi).
  rewrite blt_unfold in Hbc. destruct Hbc as [ci Hbc].
  rewrite blt_unfold. exists ci.
  apply (Hind ai (bchild b bi) (bchild c ci)); auto.
Qed.

Lemma ble_lt_trans a b c : ble a b -> blt b c -> blt a c.
Proof.
  intros Hab Hbc.
  rewrite blt_unfold in Hbc.
  destruct Hbc as [ci Hbc].
  rewrite blt_unfold. exists ci.
  apply (ble_trans a b (bchild c ci)); auto.
Qed.

Lemma blt_le_trans a b c : blt a b -> ble b c -> blt a c.
Proof.
  intros Hab Hbc.
  rewrite blt_unfold in Hab.
  destruct Hab as [bi Hab].
  rewrite ble_unfold in Hbc.
  specialize (Hbc bi).
  apply (ble_lt_trans a (bchild b bi) c); auto.
Qed.

Lemma blt_trans a b c : blt a b -> blt b c -> blt a c.
Proof.
  intros. eapply blt_le_trans; eauto using blt_le.
Qed.

Lemma blt_acc : forall x y, ble y x -> Acc blt y.
Proof.
  induction x as [x Hind] using BOrd_child_ind; intros z Hz.
  constructor. intros y Hy.
  assert (Hyx : blt y x) by (apply blt_le_trans with z; auto).
  rewrite blt_unfold in Hyx.
  destruct Hyx as [i ?].
  apply (Hind i). auto.
Qed.

Theorem blt_wf : well_founded blt.
Proof.
  intro a. apply blt_acc with a. apply ble_refl.
Qed.

Corollary blt_irreflexive : forall x, blt x x -> False.
Proof.
  induction x as [x Hind] using (well_founded_ind blt_wf).
  intro H. exact (Hind x H H).
Qed.

Global Instance ble_preorder : PreOrder ble.
Proof.
  split; [ exact ble_refl | exact ble_trans ].
Qed.

Global Instance blt_transitive : Transitive blt := blt_trans.

Global Instance beq_equivalence : Equivalence beq.
Proof.
  unfold beq; split.
  - intro x; split; apply ble_refl.
  - intros x y [??]; split; auto.
  - intros x y z [??] [??]; split; eapply ble_trans; eauto.
Qed.

Section bachmann.
  Variable f : Ord -> Ord.

  Fixpoint bach (β:BOrd) : Ord -> Ord :=
    fix inner (y:Ord) : Ord :=
      match β, y with
      | bnode A g C h, ord X k =>
        f (ord X k) ⊔
        supOrd (fun a => fixOrd (bach (g a)) (ord X (fun x => inner (k x)))) ⊔
        supOrd (fun c => fixOrd (fun ξ => bach (h c ξ) 0) (ord X (fun x => inner (k x))))
      end.

  Lemma bach_unroll A g C h (y:Ord) :
    bach (bnode A g C h) y =
      f y ⊔
      supOrd (fun a => fixOrd (bach (g a)) (limOrd (fun x => bach (bnode A g C h) (y x)))) ⊔
      supOrd (fun c => fixOrd (fun ξ => bach (h c ξ) 0)
                              (limOrd (fun x => bach (bnode A g C h) (y x)))).
  Proof.
    destruct y; reflexivity.
  Qed.

  (** The first slice of the "canonical tree" invariant: along every
      Ω-family, the diagonal ξ ↦ φ_{α[ξ]}(0) is monotone.  This fails
      for arbitrary trees, since φ is not monotone in its index. *)
  Fixpoint bmono (β:BOrd) : Prop :=
    match β with
    | bnode A g C h =>
      (forall a, bmono (g a)) /\
      (forall c ξ, bmono (h c ξ)) /\
      (forall c ξ ξ', ξ ≤ ξ' -> bach (h c ξ) 0 ≤ bach (h c ξ') 0)
    end.

  Hypothesis Hf : forall x y, x ≤ y -> f x ≤ f y.

  Lemma bach_monotone β : bmono β -> forall y z, y ≤ z -> bach β y ≤ bach β z.
  Proof.
    induction β as [A g Hg C h Hh].
    intros [Hm1 [Hm2 Hm3]] y z; revert y.
    induction z as [Z k Hz].
    intros [Y m] Hyz.
    assert (Hstart : limOrd (fun i => bach (bnode A g C h) (m i)) ≤
                     limOrd (fun j => bach (bnode A g C h) (k j))).
    { apply limit_least; intro i.
      rewrite ord_le_unfold in Hyz.
      generalize (Hyz i); intro Hi.
      rewrite ord_lt_unfold in Hi.
      destruct Hi as [j Hj].
      apply ord_le_lt_trans with (bach (bnode A g C h) (k j)).
      - apply Hz; auto.
      - rewrite ord_lt_unfold. exists j. simpl. reflexivity. }
    rewrite (bach_unroll A g C h (ord Y m)).
    rewrite (bach_unroll A g C h (ord Z k)).
    apply lub_least; [ eapply ord_le_trans; [ | apply lub_le1 ]; auto
                     | eapply ord_le_trans; [ | apply lub_le2 ] ].
    apply lub_least; [ eapply ord_le_trans; [ | apply lub_le1 ]
                     | eapply ord_le_trans; [ | apply lub_le2 ] ].
    - apply sup_ord_le_morphism; intro a.
      apply fixOrd_monotone; auto.
    - apply sup_ord_le_morphism; intro c.
      apply fixOrd_monotone; auto.
  Qed.

End bachmann.

Global Opaque bach.

(** ** Index tree constructions *)

Definition bzero : BOrd := bnode False (False_rect _) False (False_rect _).

Definition bsucc (x:BOrd) : BOrd := bnode unit (fun _ => x) False (False_rect _).

Definition blub (x y:BOrd) : BOrd :=
  match x, y with
  | bnode A g C h, bnode B g' D h' =>
    bnode (A+B) (fun ab => match ab with inl a => g a | inr b => g' b end)
          (C+D) (fun cd => match cd with inl c => h c | inr d => h' d end)
  end.

Definition bsup {I:Type} (F:I -> BOrd) : BOrd :=
  bnode (sigT (fun i => bsmall (F i))) (fun p => bsmallSz (F (projT1 p)) (projT2 p))
        (sigT (fun i => bbig (F i)))   (fun p => bbigSz (F (projT1 p)) (projT2 p)).

(** A single Ω-family as a node. *)
Definition blimΩ (g:Ord -> BOrd) : BOrd := bnode False (False_rect _) unit (fun _ => g).

(** Ordinary ordinals embed as trees with only small branching. *)
Fixpoint embed (x:Ord) : BOrd :=
  match x with
  | ord A g => bnode A (fun a => embed (g a)) False (False_rect _)
  end.

(** Ω is the node with a single Ω-family, Ω[ξ] = ξ. *)
Definition bOmega : BOrd := blimΩ embed.

(** The arithmetic operations follow @addOrd@, @mulOrd@ and @expOrd@,
    with the additional rule that an Ω-family of the right operand is
    mapped pointwise.  This is where Bachmann's canonical fundamental
    sequences come from: e.g., (β + Ω)[ξ] = β + ξ, (β·Ω)[ξ] = β·ξ and
    Ω^(β+1)[ξ] = Ω^β·ξ arise from the definitions rather than being
    stipulated. *)
Fixpoint badd (x y:BOrd) {struct y} : BOrd :=
  match y with
  | bnode B g D h =>
    blub x (bnode B (fun b => badd x (g b)) D (fun d ξ => badd x (h d ξ)))
  end.

Fixpoint bmul (x y:BOrd) {struct y} : BOrd :=
  match y with
  | bnode B g D h =>
    blub (bsup (fun b => badd (bmul x (g b)) x))
         (bnode False (False_rect _) D (fun d ξ => bmul x (h d ξ)))
  end.

Fixpoint bexpΩ (y:BOrd) : BOrd :=
  match y with
  | bnode B g D h =>
    blub (bsucc bzero)
         (blub (bsup (fun b => bmul (bexpΩ (g b)) bOmega))
               (bnode False (False_rect _) D (fun d ξ => bexpΩ (h d ξ))))
  end.

(** The canonical fundamental sequences hold by computation. *)
Example badd_Ω_fs A g C h ξ :
  bbigSz (badd (bnode A g C h) bOmega) (inr tt) ξ = badd (bnode A g C h) (embed ξ).
Proof. reflexivity. Qed.

Example bmul_Ω_fs x ξ :
  bbigSz (bmul x bOmega) (inr tt) ξ = bmul x (embed ξ).
Proof. reflexivity. Qed.

Example bexpΩ_succ_fs y ξ :
  bbigSz (bexpΩ (bsucc y)) (inr (inl (existT _ tt (inr tt)))) ξ = bmul (bexpΩ y) (embed ξ).
Proof. reflexivity. Qed.

(** ε_{Ω+1}, with fundamental sequence Ω+1, Ω^(Ω+1), Ω^Ω^(Ω+1), ... *)
Fixpoint btower (n:nat) : BOrd :=
  match n with
  | O => bsucc bOmega
  | S n' => bexpΩ (btower n')
  end.

Definition bεΩ1 : BOrd := bnode nat btower False (False_rect _).

(** The Bachmann–Howard ordinal. *)
Definition BHO : Ord := bach powOmega bεΩ1 0.

(** ** The constructions, with respect to the index ordering *)

Lemma bzero_least x : ble bzero x.
Proof.
  rewrite ble_unfold; intros [[]|[[] _]].
Qed.

Lemma bsucc_lt x : blt x (bsucc x).
Proof.
  apply (bindex_lt (bsucc x) (inl tt)).
Qed.

Lemma bsucc_least x y : blt x y -> ble (bsucc x) y.
Proof.
  intro H. rewrite ble_unfold; intros [[]|[[] _]]; exact H.
Qed.

Lemma blub_le1 x y : ble x (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h'].
  rewrite ble_unfold; intros [a|[c ξ]]; rewrite blt_unfold.
  - exists (inl (inl a)). apply ble_refl.
  - exists (inr (inl c, ξ)). apply ble_refl.
Qed.

Lemma blub_le2 x y : ble y (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h'].
  rewrite ble_unfold; intros [b|[d ξ]]; rewrite blt_unfold.
  - exists (inl (inr b)). apply ble_refl.
  - exists (inr (inr d, ξ)). apply ble_refl.
Qed.

Lemma blub_least x y z : ble x z -> ble y z -> ble (blub x y) z.
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h'].
  rewrite !ble_unfold; intros Hx Hy.
  intros [[a|b]|[[c|d] ξ]].
  - exact (Hx (inl a)).
  - exact (Hy (inl b)).
  - exact (Hx (inr (c, ξ))).
  - exact (Hy (inr (d, ξ))).
Qed.

Lemma bsup_le {I:Type} (F:I -> BOrd) i : ble (F i) (bsup F).
Proof.
  rewrite ble_unfold; intros [a|[c ξ]]; rewrite blt_unfold.
  - exists (inl (existT _ i a)). apply ble_refl.
  - exists (inr (existT _ i c, ξ)). apply ble_refl.
Qed.

Lemma bsup_least {I:Type} (F:I -> BOrd) z : (forall i, ble (F i) z) -> ble (bsup F) z.
Proof.
  intro H. rewrite ble_unfold.
  intros [[i a]|[[i c] ξ]]; specialize (H i); rewrite ble_unfold in H.
  - exact (H (inl a)).
  - exact (H (inr (c, ξ))).
Qed.

(** @embed@ is an order embedding. *)
Lemma embed_order : forall x y,
  (x ≤ y <-> ble (embed x) (embed y)) /\ (x < y <-> blt (embed x) (embed y)).
Proof.
  induction x as [A f Hx].
  assert (Hle : forall y, ord A f ≤ y <-> ble (embed (ord A f)) (embed y)).
  { intro y. rewrite ord_le_unfold, ble_unfold. split.
    - intros H [a|[[] _]]. apply (proj1 (proj2 (Hx a y))). apply H.
    - intros H a. apply (proj2 (proj2 (Hx a y))). apply (H (inl a)). }
  intro y; split; [ apply Hle | ].
  destruct y as [B g].
  rewrite ord_lt_unfold, blt_unfold. split.
  - intros [b Hb]. exists (inl b).
    change (ble (embed (ord A f)) (embed (g b))).
    apply Hle; auto.
  - intros [[b|[[] _]] Hb]. exists b. apply Hle. apply Hb.
Qed.

Theorem embed_le x y : x ≤ y <-> ble (embed x) (embed y).
Proof. apply embed_order. Qed.

Theorem embed_lt x y : x < y <-> blt (embed x) (embed y).
Proof. apply embed_order. Qed.

(** Ω lies strictly above every embedded ordinal, and is the least
    such index. *)
Lemma embed_lt_Ω ξ : blt (embed ξ) bOmega.
Proof.
  apply (bindex_lt bOmega (inr (tt, ξ))).
Qed.

Lemma Ω_not_le_embed ξ : ~ ble bOmega (embed ξ).
Proof.
  intro H.
  apply (blt_irreflexive (embed ξ)).
  apply blt_le_trans with bOmega; auto using embed_lt_Ω.
Qed.

Lemma Ω_least z : (forall ξ, blt (embed ξ) z) -> ble bOmega z.
Proof.
  intro H. rewrite ble_unfold; intros [[]|[[] ξ]]. apply H.
Qed.

Lemma badd_le_l x y : ble x (badd x y).
Proof.
  destruct y; apply blub_le1.
Qed.

Lemma badd_zero x : beq (badd x bzero) x.
Proof.
  split.
  - apply blub_least; [ reflexivity | ].
    rewrite ble_unfold; intros [[]|[[] _]].
  - apply badd_le_l.
Qed.

(** ** Monotonicity of the arithmetic

Addition is monotone in both arguments, and strictly monotone in its
right argument, for arbitrary index trees.  Multiplication and
exponentiation are more delicate, because they map Ω-families
pointwise while treating small children as successor steps.  This is
only sensible if every Ω-family behaves like a fundamental sequence,
i.e., has no largest member.  For example, if @y'@ has a single
Ω-family that is constant at @t@, then @y'@ denotes @t+1@ but
@bmul x y'@ denotes only @x·t + 1@, which is below @bmul x (bsucc t)@
whenever x > 1.  We therefore introduce the hereditary invariant
@bunb@ stating that every Ω-family is unbounded in itself.
*)

Lemma blub_le_iff x y z : ble (blub x y) z <-> ble x z /\ ble y z.
Proof.
  split.
  - intro H; split.
    + apply ble_trans with (blub x y); [ apply blub_le1 | exact H ].
    + apply ble_trans with (blub x y); [ apply blub_le2 | exact H ].
  - intros [??]; apply blub_least; auto.
Qed.

Lemma bsup_le_iff {I:Type} (F:I -> BOrd) z : ble (bsup F) z <-> forall i, ble (F i) z.
Proof.
  split.
  - intros H i; apply ble_trans with (bsup F); [ apply bsup_le | exact H ].
  - apply bsup_least.
Qed.

Lemma bsucc_le_iff x z : ble (bsucc x) z <-> blt x z.
Proof.
  split.
  - intro H; apply blt_le_trans with (bsucc x); [ apply bsucc_lt | exact H ].
  - apply bsucc_least.
Qed.

(** *** Addition *)

Definition baddR (x y:BOrd) : BOrd :=
  bnode (bsmall y) (fun b => badd x (bsmallSz y b))
        (bbig y) (fun d ξ => badd x (bbigSz y d ξ)).

Lemma badd_eq x y : badd x y = blub x (baddR x y).
Proof.
  destruct y; reflexivity.
Qed.

Lemma baddR_child x y i : bchild (baddR x y) i = badd x (bchild y i).
Proof.
  destruct i as [b|[d ξ]]; reflexivity.
Qed.

Lemma badd_le_iff x y z :
  ble (badd x y) z <-> ble x z /\ forall i:bidx y, blt (badd x (bchild y i)) z.
Proof.
  rewrite (badd_eq x y), blub_le_iff, (ble_unfold (baddR x y)).
  split; intros [H1 H2]; split; auto; intro i.
  - rewrite <- baddR_child; apply H2.
  - rewrite baddR_child; apply H2.
Qed.

Lemma badd_child_lt x y i : blt (badd x (bchild y i)) (badd x y).
Proof.
  rewrite (badd_eq x y), <- baddR_child.
  eapply blt_le_trans; [ apply bindex_lt | apply blub_le2 ].
Qed.

Lemma badd_mono_r x : forall y y', ble y y' -> ble (badd x y) (badd x y').
Proof.
  intro y.
  induction y as [y Hind] using BOrd_child_ind; intros y' H.
  apply badd_le_iff; split; [ apply badd_le_l | ].
  intro i.
  rewrite ble_unfold in H. specialize (H i).
  rewrite blt_unfold in H. destruct H as [j Hj].
  eapply ble_lt_trans; [ apply (Hind i _ Hj) | apply badd_child_lt ].
Qed.

Lemma badd_lt_r x y y' : blt y y' -> blt (badd x y) (badd x y').
Proof.
  rewrite blt_unfold; intros [j Hj].
  eapply ble_lt_trans; [ apply badd_mono_r, Hj | apply badd_child_lt ].
Qed.

Lemma badd_mono_l y : forall x x', ble x x' -> ble (badd x y) (badd x' y).
Proof.
  induction y as [y Hind] using BOrd_child_ind; intros x x' H.
  apply badd_le_iff; split.
  - eapply ble_trans; [ apply H | apply badd_le_l ].
  - intro i.
    eapply ble_lt_trans; [ apply Hind, H | apply badd_child_lt ].
Qed.

Lemma badd_le_r x y : ble y (badd x y).
Proof.
  induction y as [y Hind] using BOrd_child_ind.
  rewrite ble_unfold; intro i.
  eapply ble_lt_trans; [ apply Hind | apply badd_child_lt ].
Qed.

Lemma badd_lt_pos z x : blt bzero x -> blt z (badd z x).
Proof.
  rewrite blt_unfold; intros [j _].
  eapply ble_lt_trans; [ apply badd_le_l | apply (badd_child_lt z x j) ].
Qed.

(** *** Multiplication *)

Definition bmulS (x y:BOrd) : BOrd :=
  bsup (fun a:bsmall y => badd (bmul x (bsmallSz y a)) x).

Definition bmulB (x y:BOrd) : BOrd :=
  bnode False (False_rect _) (bbig y) (fun d ξ => bmul x (bbigSz y d ξ)).

Lemma bmul_eq x y : bmul x y = blub (bmulS x y) (bmulB x y).
Proof.
  destruct y; reflexivity.
Qed.

Lemma bmul_le_iff x y z :
  ble (bmul x y) z <->
  (forall a, ble (badd (bmul x (bsmallSz y a)) x) z) /\
  (forall d ξ, blt (bmul x (bbigSz y d ξ)) z).
Proof.
  rewrite (bmul_eq x y), blub_le_iff.
  unfold bmulS; rewrite bsup_le_iff.
  rewrite (ble_unfold (bmulB x y)).
  split; intros [H1 H2]; split; auto.
  - intros d ξ; exact (H2 (inr (d, ξ))).
  - intros [[]|[d ξ]]; exact (H2 d ξ).
Qed.

Lemma bmul_small_le x y a : ble (badd (bmul x (bsmallSz y a)) x) (bmul x y).
Proof.
  rewrite (bmul_eq x y).
  eapply ble_trans; [ | apply blub_le1 ].
  apply (bsup_le (fun a0 => badd (bmul x (bsmallSz y a0)) x) a).
Qed.

Lemma bmul_big_lt x y d ξ : blt (bmul x (bbigSz y d ξ)) (bmul x y).
Proof.
  rewrite (bmul_eq x y).
  eapply blt_le_trans; [ apply (bindex_lt (bmulB x y) (inr (d, ξ))) | apply blub_le2 ].
Qed.

Lemma bmul_mono_l y : forall x x', ble x x' -> ble (bmul x y) (bmul x' y).
Proof.
  induction y as [y Hind] using BOrd_child_ind; intros x x' H.
  apply bmul_le_iff; split.
  - intro a.
    eapply ble_trans; [ | apply bmul_small_le ].
    eapply ble_trans.
    + apply badd_mono_l. apply (Hind (inl a)). exact H.
    + apply badd_mono_r. exact H.
  - intros d ξ.
    eapply ble_lt_trans; [ apply (Hind (inr (d, ξ))), H | apply bmul_big_lt ].
Qed.

(** Every Ω-family is unbounded in itself, hereditarily. *)
Fixpoint bunb (x:BOrd) : Prop :=
  match x with
  | bnode A g C h =>
    (forall a, bunb (g a)) /\
    (forall c ξ, bunb (h c ξ)) /\
    (forall c ξ, exists ξ', blt (h c ξ) (h c ξ'))
  end.

Lemma bunb_child x i : bunb x -> bunb (bchild x i).
Proof.
  destruct x; destruct i as [a|[c ξ]]; simpl; intuition.
Qed.

Lemma bunb_fam x d ξ : bunb x -> exists ξ', blt (bbigSz x d ξ) (bbigSz x d ξ').
Proof.
  destruct x; simpl; intuition.
Qed.

Lemma bmul_mono_aux x : blt bzero x ->
  forall t', bunb t' -> forall t,
    (blt t t' -> ble (badd (bmul x t) x) (bmul x t')) /\
    (ble t t' -> ble (bmul x t) (bmul x t')).
Proof.
  intros Hx t'.
  induction t' as [t' Hind] using BOrd_child_ind; intros Hu.
  assert (HK : forall t, blt t t' -> ble (badd (bmul x t) x) (bmul x t')).
  { intros t Ht.
    rewrite blt_unfold in Ht. destruct Ht as [[a|[d ζ]] Hj].
    - eapply ble_trans; [ | apply (bmul_small_le x t' a) ].
      apply badd_mono_l.
      apply (proj2 (Hind (inl a) (bunb_child t' (inl a) Hu) t)).
      exact Hj.
    - destruct (bunb_fam t' d ζ Hu) as [ζ' Hζ].
      assert (Ht : blt t (bbigSz t' d ζ')) by (eapply ble_lt_trans; [ exact Hj | exact Hζ ]).
      eapply ble_trans.
      + apply (proj1 (Hind (inr (d, ζ')) (bunb_child t' (inr (d, ζ')) Hu) t)). exact Ht.
      + apply blt_le, bmul_big_lt. }
  intro t; split; [ apply HK | intro Ht ].
  rewrite ble_unfold in Ht.
  apply bmul_le_iff; split.
  - intro a. apply HK. apply (Ht (inl a)).
  - intros d ξ.
    eapply blt_le_trans; [ apply badd_lt_pos; exact Hx | ].
    apply HK. apply (Ht (inr (d, ξ))).
Qed.

Lemma bmul_mono_r x y y' :
  blt bzero x -> bunb y' -> ble y y' -> ble (bmul x y) (bmul x y').
Proof.
  intros Hx Hu. apply (bmul_mono_aux x Hx y' Hu y).
Qed.

Lemma bmul_lt_r x y y' :
  blt bzero x -> bunb y' -> blt y y' -> blt (bmul x y) (bmul x y').
Proof.
  intros Hx Hu H.
  eapply blt_le_trans; [ apply badd_lt_pos; exact Hx | ].
  apply (bmul_mono_aux x Hx y' Hu y); auto.
Qed.

(** z < z·Ω, without any hypotheses: z ≤ z·1 < z·Ω. *)
Lemma bmul_Ω_gt z : blt z (bmul z bOmega).
Proof.
  eapply ble_lt_trans; [ | apply (bmul_big_lt z bOmega tt (succOrd zeroOrd)) ].
  eapply ble_trans; [ | apply (bmul_small_le z (embed (succOrd zeroOrd)) tt) ].
  apply badd_le_r.
Qed.

(** *** Exponentiation *)

Definition bexpS (y:BOrd) : BOrd :=
  bsup (fun a:bsmall y => bmul (bexpΩ (bsmallSz y a)) bOmega).

Definition bexpB (y:BOrd) : BOrd :=
  bnode False (False_rect _) (bbig y) (fun d ξ => bexpΩ (bbigSz y d ξ)).

Lemma bexpΩ_eq y : bexpΩ y = blub (bsucc bzero) (blub (bexpS y) (bexpB y)).
Proof.
  destruct y; reflexivity.
Qed.

Lemma bexpΩ_le_iff y z :
  ble (bexpΩ y) z <->
  blt bzero z /\
  (forall a, ble (bmul (bexpΩ (bsmallSz y a)) bOmega) z) /\
  (forall d ξ, blt (bexpΩ (bbigSz y d ξ)) z).
Proof.
  rewrite (bexpΩ_eq y), !blub_le_iff, bsucc_le_iff.
  unfold bexpS; rewrite bsup_le_iff.
  rewrite (ble_unfold (bexpB y)).
  split; intros [H0 [H1 H2]]; split; auto; split; auto.
  - intros d ξ; exact (H2 (inr (d, ξ))).
  - intros [[]|[d ξ]]; exact (H2 d ξ).
Qed.

Lemma bexpΩ_pos y : blt bzero (bexpΩ y).
Proof.
  rewrite (bexpΩ_eq y).
  eapply blt_le_trans; [ apply bsucc_lt | apply blub_le1 ].
Qed.

Lemma bexpΩ_small_le y a : ble (bmul (bexpΩ (bsmallSz y a)) bOmega) (bexpΩ y).
Proof.
  rewrite (bexpΩ_eq y).
  eapply ble_trans; [ | apply blub_le2 ].
  eapply ble_trans; [ | apply blub_le1 ].
  apply (bsup_le (fun a0 => bmul (bexpΩ (bsmallSz y a0)) bOmega) a).
Qed.

Lemma bexpΩ_big_lt y d ξ : blt (bexpΩ (bbigSz y d ξ)) (bexpΩ y).
Proof.
  rewrite (bexpΩ_eq y).
  eapply blt_le_trans; [ | apply blub_le2 ].
  eapply blt_le_trans; [ apply (bindex_lt (bexpB y) (inr (d, ξ))) | apply blub_le2 ].
Qed.

Lemma bexpΩ_mono_aux :
  forall t', bunb t' -> forall t,
    (blt t t' -> ble (bmul (bexpΩ t) bOmega) (bexpΩ t')) /\
    (ble t t' -> ble (bexpΩ t) (bexpΩ t')).
Proof.
  intro t'.
  induction t' as [t' Hind] using BOrd_child_ind; intros Hu.
  assert (HK : forall t, blt t t' -> ble (bmul (bexpΩ t) bOmega) (bexpΩ t')).
  { intros t Ht.
    rewrite blt_unfold in Ht. destruct Ht as [[a|[d ζ]] Hj].
    - eapply ble_trans; [ | apply (bexpΩ_small_le t' a) ].
      apply bmul_mono_l.
      apply (proj2 (Hind (inl a) (bunb_child t' (inl a) Hu) t)).
      exact Hj.
    - destruct (bunb_fam t' d ζ Hu) as [ζ' Hζ].
      assert (Ht : blt t (bbigSz t' d ζ')) by (eapply ble_lt_trans; [ exact Hj | exact Hζ ]).
      eapply ble_trans.
      + apply (proj1 (Hind (inr (d, ζ')) (bunb_child t' (inr (d, ζ')) Hu) t)). exact Ht.
      + apply blt_le, bexpΩ_big_lt. }
  intro t; split; [ apply HK | intro Ht ].
  rewrite ble_unfold in Ht.
  apply bexpΩ_le_iff; split; [ apply bexpΩ_pos | split ].
  - intro a. apply HK. apply (Ht (inl a)).
  - intros d ξ.
    eapply blt_le_trans; [ apply bmul_Ω_gt | ].
    apply HK. apply (Ht (inr (d, ξ))).
Qed.

Lemma bexpΩ_mono y y' : bunb y' -> ble y y' -> ble (bexpΩ y) (bexpΩ y').
Proof.
  intros Hu. apply (bexpΩ_mono_aux y' Hu y).
Qed.

Lemma bexpΩ_lt y y' : bunb y' -> blt y y' -> blt (bexpΩ y) (bexpΩ y').
Proof.
  intros Hu H.
  eapply blt_le_trans; [ apply bmul_Ω_gt | ].
  apply (bexpΩ_mono_aux y' Hu y); auto.
Qed.

(** *** The invariant is satisfied by the canonical trees *)

Lemma bunb_blub x y : bunb x -> bunb y -> bunb (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [H1 [H2 H3]] [H1' [H2' H3']].
  split; [ | split ].
  - intros [a|b]; auto.
  - intros [c|d] ξ; auto.
  - intros [c|d] ξ; [ apply H3 | apply H3' ].
Qed.

Lemma bunb_bsup {I:Type} (F:I -> BOrd) : (forall i, bunb (F i)) -> bunb (bsup F).
Proof.
  intro H; simpl.
  split; [ | split ].
  - intros [i a]. apply (bunb_child (F i) (inl a)); auto.
  - intros [i c] ξ. apply (bunb_child (F i) (inr (c, ξ))); auto.
  - intros [i c] ξ. apply bunb_fam; auto.
Qed.

Lemma bunb_bzero : bunb bzero.
Proof.
  simpl; intuition.
Qed.

Lemma bunb_bsucc x : bunb x -> bunb (bsucc x).
Proof.
  simpl; intuition.
Qed.

Lemma bunb_embed ξ : bunb (embed ξ).
Proof.
  induction ξ as [A f Hf]; simpl; intuition.
Qed.

Lemma bunb_Ω : bunb bOmega.
Proof.
  simpl; split; [ intros [] | split ].
  - intros _ ξ; apply bunb_embed.
  - intros _ ξ. exists (succOrd ξ). apply embed_lt, succ_lt.
Qed.

Lemma bunb_badd x y : bunb x -> bunb y -> bunb (badd x y).
Proof.
  intro Hx.
  induction y as [y Hind] using BOrd_child_ind; intro Hy.
  rewrite (badd_eq x y).
  apply bunb_blub; auto.
  unfold baddR; simpl.
  split; [ | split ].
  - intro a. apply (Hind (inl a)). apply (bunb_child y (inl a)); auto.
  - intros d ξ. apply (Hind (inr (d, ξ))). apply (bunb_child y (inr (d, ξ))); auto.
  - intros d ξ.
    destruct (bunb_fam y d ξ Hy) as [ξ' Hξ].
    exists ξ'. apply badd_lt_r; auto.
Qed.

Lemma bunb_bmul x y : blt bzero x -> bunb x -> bunb y -> bunb (bmul x y).
Proof.
  intros Hx0 Hx.
  induction y as [y Hind] using BOrd_child_ind; intro Hy.
  rewrite (bmul_eq x y).
  apply bunb_blub.
  - apply bunb_bsup; intro a.
    apply bunb_badd; auto.
    apply (Hind (inl a)). apply (bunb_child y (inl a)); auto.
  - unfold bmulB; simpl.
    split; [ intros [] | split ].
    + intros d ξ. apply (Hind (inr (d, ξ))). apply (bunb_child y (inr (d, ξ))); auto.
    + intros d ξ.
      destruct (bunb_fam y d ξ Hy) as [ξ' Hξ].
      exists ξ'. apply bmul_lt_r; auto.
      apply (bunb_child y (inr (d, ξ'))); auto.
Qed.

Lemma bunb_bexpΩ y : bunb y -> bunb (bexpΩ y).
Proof.
  induction y as [y Hind] using BOrd_child_ind; intro Hy.
  rewrite (bexpΩ_eq y).
  apply bunb_blub; [ apply bunb_bsucc, bunb_bzero | apply bunb_blub ].
  - apply bunb_bsup; intro a.
    apply bunb_bmul; auto using bexpΩ_pos, bunb_Ω.
    apply (Hind (inl a)). apply (bunb_child y (inl a)); auto.
  - unfold bexpB; simpl.
    split; [ intros [] | split ].
    + intros d ξ. apply (Hind (inr (d, ξ))). apply (bunb_child y (inr (d, ξ))); auto.
    + intros d ξ.
      destruct (bunb_fam y d ξ Hy) as [ξ' Hξ].
      exists ξ'. apply bexpΩ_lt; auto.
      apply (bunb_child y (inr (d, ξ'))); auto.
Qed.

Lemma bunb_btower n : bunb (btower n).
Proof.
  induction n.
  - change (bunb (bsucc bOmega)). apply bunb_bsucc, bunb_Ω.
  - change (bunb (bexpΩ (btower n))). apply bunb_bexpΩ; auto.
Qed.

Lemma bunb_bεΩ1 : bunb bεΩ1.
Proof.
  simpl; split; [ apply bunb_btower | split; intros [] ].
Qed.

(** ** Auxiliary facts about limits and fixpoints *)

Lemma lim_eq_mor A (F G:A -> Ord) :
  (forall a, F a ≈ G a) -> limOrd F ≈ limOrd G.
Proof.
  intro H; split; rewrite ord_le_unfold; simpl; intro a;
    rewrite ord_lt_unfold; simpl; exists a; apply H.
Qed.

Lemma lim_le_mor A (F G:A -> Ord) :
  (forall a, F a ≤ G a) -> limOrd F ≤ limOrd G.
Proof.
  intro H; rewrite ord_le_unfold; simpl; intro a;
    rewrite ord_lt_unfold; simpl; exists a; apply H.
Qed.

Lemma lub_sup_False z (F:False -> Ord) : z ⊔ supOrd F ≈ z.
Proof.
  split.
  - apply lub_least; [ reflexivity | apply sup_least; intros [] ].
  - apply lub_le1.
Qed.

Lemma fixOrd_eq_func F G a b :
  (forall x, F x ≈ G x) ->
  (forall x y, x ≤ y -> G x ≤ G y) ->
  a ≈ b ->
  fixOrd F a ≈ fixOrd G b.
Proof.
  intros HFG HG Hab.
  unfold fixOrd.
  apply sup_ord_eq_morphism; intro n.
  induction n; simpl; auto.
  rewrite (HFG (iter_f F a n)).
  split; apply HG; apply IHn.
Qed.

Lemma fixOrd_eq_func_complete F G a b :
  (forall x, complete x -> F x ≈ G x) ->
  (forall x y, x ≤ y -> F x ≤ F y) ->
  (forall x y, x ≤ y -> G x ≤ G y) ->
  (forall x, complete x -> complete (G x)) ->
  a ≈ b -> complete b ->
  fixOrd F a ≈ fixOrd G b.
Proof.
  intros HFG HF HG HGc Hab Hb.
  assert (Hiter : forall n, iter_f F a n ≈ iter_f G b n /\ complete (iter_f G b n)).
  { induction n as [|n [IH1 IH2]]; simpl; auto.
    split; auto.
    transitivity (F (iter_f G b n)).
    - destruct IH1; split; apply HF; auto.
    - apply HFG; auto. }
  unfold fixOrd.
  apply sup_ord_eq_morphism; intro n.
  apply Hiter.
Qed.

Lemma bach_unroll' f x (y:Ord) :
  bach f x y =
    f y ⊔
    supOrd (fun a:bsmall x => fixOrd (bach f (bsmallSz x a)) (limOrd (fun j => bach f x (y j)))) ⊔
    supOrd (fun c:bbig x => fixOrd (fun ξ => bach f (bbigSz x c ξ) 0)
                                   (limOrd (fun j => bach f x (y j)))).
Proof.
  destruct x. apply bach_unroll.
Qed.

(** ** Agreement with the Veblen hierarchy below Ω *)

Theorem bach_embed f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall β y, bach f (embed β) y ≈ veblen f β y.
Proof.
  induction β as [A g Hβ].
  induction y as [Y h Hy].
  change (embed (ord A g)) with (bnode A (fun a => embed (g a)) False (False_rect _)).
  rewrite bach_unroll.
  rewrite veblen_unroll.
  apply ord_lub_eq_mor; [ reflexivity | ].
  rewrite lub_sup_False.
  apply sup_ord_eq_morphism; intro a.
  apply fixOrd_eq_func.
  - intro x; apply Hβ.
  - apply veblen_monotone; auto.
  - apply lim_eq_mor; intro i; apply Hy.
Qed.

Lemma bmono_embed f (Hf : forall x y, x ≤ y -> f x ≤ f y) : forall β, bmono f (embed β).
Proof.
  induction β as [A g Hβ]; simpl.
  intuition.
Qed.

Lemma bmono_Ω f (Hf : forall x y, x ≤ y -> f x ≤ f y) : bmono f bOmega.
Proof.
  simpl; intuition.
  - apply bmono_embed; auto.
  - rewrite (bach_embed f Hf ξ 0).
    rewrite (bach_embed f Hf ξ' 0).
    apply veblen_monotone_first; auto.
Qed.

Lemma bmono_blub f x y : bmono f x -> bmono f y -> bmono f (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  intros [H1 [H2 H3]] [H1' [H2' H3']].
  split; [ | split ].
  - intros [a|b]; auto.
  - intros [c|d] ξ; auto.
  - intros [c|d]; [ apply H3 | apply H3' ].
Qed.

Lemma bmono_badd_embed f α : bmono f α -> forall ξ, bmono f (badd α (embed ξ)).
Proof.
  intros Hα ξ.
  induction ξ as [X k Hk].
  rewrite (badd_eq α (embed (ord X k))).
  apply bmono_blub; auto.
  unfold baddR; simpl.
  split; [ intro b; apply Hk | split; intros [] ].
Qed.

Lemma bach_embed0_mono :
  forall x y, x ≤ y -> bach powOmega (embed x) 0 ≤ bach powOmega (embed y) 0.
Proof.
  intros x y H.
  rewrite (bach_embed _ powOmega_monotone x 0), (bach_embed _ powOmega_monotone y 0).
  apply veblen_monotone_first; auto.
  apply powOmega_monotone.
Qed.

(** ** Monotonicity in the index, for the family-respecting order

φ is not monotone with respect to the index ordering @ble@: Γ₀+1 < Ω,
but φ_{Γ₀+1}(0) > Γ₀ = φ_Ω(0).  It is, however, monotone with respect
to the following stricter, structural order, which matches small
children to small children and Ω-families to Ω-families *pointwise*,
at the same argument ξ.  This is the order under which Bachmann's
fundamental sequences are "compared as sequences".
*)
Fixpoint bsub (x y:BOrd) {struct x} : Prop :=
  match x, y with
  | bnode A g C h, bnode B g' D h' =>
    (forall a, exists b, bsub (g a) (g' b)) /\
    (forall c, exists d, forall ξ, bsub (h c ξ) (h' d ξ))
  end.

Lemma bsub_refl x : bsub x x.
Proof.
  induction x as [A g Hg C h Hh]; simpl.
  split; [ intro a; exists a; auto | intro c; exists c; auto ].
Qed.

Lemma bsub_blub_l x y : bsub x (blub x y).
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl.
  split.
  - intro a; exists (inl a); apply bsub_refl.
  - intro c; exists (inl c); intro ξ; apply bsub_refl.
Qed.

Lemma bsub_blub_empty x y :
  (bsmall y -> False) -> (bbig y -> False) -> bsub (blub x y) x.
Proof.
  destruct x as [A g C h]; destruct y as [B g' D h']; simpl; intros HB HD.
  split.
  - intros [a|b]; [ exists a; apply bsub_refl | elim (HB b) ].
  - intros [c|d]; [ exists c; intro ξ; apply bsub_refl | elim (HD d) ].
Qed.

Theorem bach_mono_index f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall x y, bsub x y -> bmono f y -> forall z, bach f x z ≤ bach f y z.
Proof.
  induction x as [A g Hg C h Hh].
  intros [B g' D h'] Hsub Hy.
  destruct Hsub as [Hs1 Hs2].
  destruct Hy as [Hm1 [Hm2 Hm3]].
  induction z as [Z k Hz].
  assert (Hstart : limOrd (fun j => bach f (bnode A g C h) (ord Z k j)) ≤
                   limOrd (fun j => bach f (bnode B g' D h') (ord Z k j))).
  { apply lim_le_mor; intro j; apply Hz. }
  rewrite (bach_unroll f A g C h (ord Z k)), (bach_unroll f B g' D h' (ord Z k)).
  apply lub_least; [ apply lub_le1 | ].
  eapply ord_le_trans; [ | apply lub_le2 ].
  apply lub_least.
  - apply sup_least; intro a.
    destruct (Hs1 a) as [b Hb].
    transitivity (fixOrd (bach f (g' b)) (limOrd (fun j => bach f (bnode B g' D h') (ord Z k j)))).
    + transitivity (fixOrd (bach f (g' b)) (limOrd (fun j => bach f (bnode A g C h) (ord Z k j)))).
      * apply fixOrd_monotone_func.
        { intro x; apply Hg; auto. }
        apply bach_monotone; auto.
      * apply fixOrd_monotone; auto.
        apply bach_monotone; auto.
    + eapply ord_le_trans; [ | apply lub_le1 ].
      apply (sup_le _ (fun b0 => fixOrd (bach f (g' b0))
                                        (limOrd (fun j => bach f (bnode B g' D h') (ord Z k j)))) b).
  - apply sup_least; intro c.
    destruct (Hs2 c) as [d Hd].
    transitivity (fixOrd (fun ξ => bach f (h' d ξ) 0)
                         (limOrd (fun j => bach f (bnode B g' D h') (ord Z k j)))).
    + transitivity (fixOrd (fun ξ => bach f (h' d ξ) 0)
                           (limOrd (fun j => bach f (bnode A g C h) (ord Z k j)))).
      * apply fixOrd_monotone_func.
        { intro ξ; apply Hh; auto. }
        apply Hm3.
      * apply fixOrd_monotone; auto.
    + eapply ord_le_trans; [ | apply lub_le2 ].
      apply (sup_le _ (fun d0 => fixOrd (fun ξ => bach f (h' d0 ξ) 0)
                                        (limOrd (fun j => bach f (bnode B g' D h') (ord Z k j)))) d).
Qed.

Lemma bach_le_badd_embed f (Hf : forall x y, x ≤ y -> f x ≤ f y) α ξ :
  bmono f α -> forall y, bach f α y ≤ bach f (badd α (embed ξ)) y.
Proof.
  intros Hα y.
  apply bach_mono_index; auto.
  - rewrite (badd_eq α (embed ξ)). apply bsub_blub_l.
  - apply bmono_badd_embed; auto.
Qed.

(** ** General step theorems

A node's value is @f y@ joined with, for each of its components, the
least fixpoint above a common starting point of the function that
component contributes: @bach@ of a small child, or the diagonal of an
Ω-family.  The invariant @BRep f T G@ records that @bach f T@ agrees
with a normal function G on complete arguments, and that every
component of T fixes the values of G.  The step theorems below
propagate this invariant through the canonical constructions.
*)

Definition bcomp f (T:BOrd) (k:(bsmall T + bbig T)%type) : Ord -> Ord :=
  match k with
  | inl a => bach f (bsmallSz T a)
  | inr c => fun ξ => bach f (bbigSz T c ξ) 0
  end.

Lemma bach_comp_le f T (y:Ord) k :
  fixOrd (bcomp f T k) (limOrd (fun j => bach f T (y j))) ≤ bach f T y.
Proof.
  rewrite (bach_unroll' f T y).
  eapply ord_le_trans; [ | apply lub_le2 ].
  destruct k as [a|c].
  - eapply ord_le_trans; [ | apply lub_le1 ].
    apply (sup_le _ (fun a0 => fixOrd (bach f (bsmallSz T a0)) (limOrd (fun j => bach f T (y j)))) a).
  - eapply ord_le_trans; [ | apply lub_le2 ].
    apply (sup_le _ (fun c0 => fixOrd (fun ξ => bach f (bbigSz T c0 ξ) 0)
                                      (limOrd (fun j => bach f T (y j)))) c).
Qed.

Lemma bach_le_comp f T (y z:Ord) :
  f y ≤ z ->
  (forall k, fixOrd (bcomp f T k) (limOrd (fun j => bach f T (y j))) ≤ z) ->
  bach f T y ≤ z.
Proof.
  intros H1 H2.
  rewrite (bach_unroll' f T y).
  apply lub_least; auto.
  apply lub_least; apply sup_least.
  - intro a; apply (H2 (inl a)).
  - intro c; apply (H2 (inr c)).
Qed.

Lemma f_le_bach f T (y:Ord) : f y ≤ bach f T y.
Proof.
  rewrite (bach_unroll' f T y). apply lub_le1.
Qed.

Lemma bmono_bcomp f (Hf : forall x y, x ≤ y -> f x ≤ f y) T :
  bmono f T -> forall k x y, x ≤ y -> bcomp f T k x ≤ bcomp f T k y.
Proof.
  destruct T as [A g C h]; intros [H1 [H2 H3]] [a|c] x y Hxy; simpl.
  - apply bach_monotone; auto.
  - apply H3; auto.
Qed.

Definition BRep f (T:BOrd) (G:Ord -> Ord) : Prop :=
  normal_function G /\
  (forall y, complete y -> bach f T y ≈ G y) /\
  (forall k y, complete y -> bcomp f T k (G y) ≤ G y).

(** *** The enumeration step

If one distinguished component agrees with a normal G, and every
component fixes the values of @enum_fixpoints G@, then the node
enumerates the fixpoints of G.  The successor and Ω-limit steps are
instances. *)

Theorem bach_enum_step f T G (k0:(bsmall T + bbig T)%type) :
  normal_function G ->
  (forall k x y, x ≤ y -> bcomp f T k x ≤ bcomp f T k y) ->
  (forall x, complete x -> bcomp f T k0 x ≈ G x) ->
  (forall x, complete x -> f x ≤ G x) ->
  (forall k y, complete y -> bcomp f T k (enum_fixpoints G y) ≤ enum_fixpoints G y) ->
  BRep f T (enum_fixpoints G).
Proof.
  intros HG Hmono H0 Hf Hcl.
  assert (HE : normal_function (enum_fixpoints G)) by (apply enum_fixpoints_normal; auto).
  split; [ exact HE | split; [ | exact Hcl ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f T (ord Y h j)) ≈
               limOrd (fun j => enum_fixpoints G (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => enum_fixpoints G (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (G (ord Y h)); auto.
      transitivity (G (enum_fixpoints G (ord Y h))).
      * apply normal_monotone; auto. apply normal_inflationary; auto.
      * apply (proj2 (enum_are_fixpoints G HG (ord Y h) Hyc)).
    + intro k.
      apply fixOrd_least; [ apply Hmono | | apply Hcl; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply enum_fixpoints_increasing; [ apply normal_monotone; auto | ].
      apply (index_lt (ord Y h) j).
  - eapply ord_le_trans; [ | apply (bach_comp_le f T (ord Y h) k0) ].
    change (fixOrd G (limOrd (fun j => enum_fixpoints G (h j))) ≤
            fixOrd (bcomp f T k0) (limOrd (fun j => bach f T (ord Y h j)))).
    apply (proj2 (fixOrd_eq_func_complete (bcomp f T k0) G _ _ H0 (Hmono k0)
                    (normal_monotone G HG) (normal_complete G HG) Hs Hsc)).
Qed.

(** *** The Ω-limit step *)

Theorem bach_Ωlim_step f H G :
  normal_function G ->
  (forall ξ ξ', ξ ≤ ξ' -> bach f (H ξ) 0 ≤ bach f (H ξ') 0) ->
  (forall x, complete x -> bach f (H x) 0 ≈ G x) ->
  (forall x, complete x -> f x ≤ G x) ->
  BRep f (blimΩ H) (enum_fixpoints G).
Proof.
  intros HG Hmono HD Hf.
  refine (bach_enum_step f (blimΩ H) G (inr tt) HG _ _ Hf _).
  - intros [[]|[]] x y Hxy. apply Hmono; auto.
  - intros x Hx. apply HD; auto.
  - intros [[]|[]] y Hy.
    assert (Hv : complete (enum_fixpoints G y)).
    { apply normal_complete; auto. apply enum_fixpoints_normal; auto. }
    transitivity (G (enum_fixpoints G y)).
    + apply (proj1 (HD _ Hv)).
    + apply (proj2 (enum_are_fixpoints G HG y Hy)).
Qed.

(** *** The successor step, for the canonical successor α+1 *)

Lemma bmono_badd_zero f α : bmono f α -> bmono f (badd α bzero).
Proof.
  intro H.
  rewrite (badd_eq α bzero).
  apply bmono_blub; auto.
  simpl; split; [ intros [] | split; intros [] ].
Qed.

Lemma bmono_badd_one f α : bmono f α -> bmono f (badd α (bsucc bzero)).
Proof.
  intro H.
  rewrite (badd_eq α (bsucc bzero)).
  apply bmono_blub; auto.
  simpl; split; [ intros _; apply bmono_badd_zero; auto | split; intros [] ].
Qed.

Lemma bach_badd_zero f (Hf : forall x y, x ≤ y -> f x ≤ f y) α :
  bmono f α -> forall y, bach f (badd α bzero) y ≈ bach f α y.
Proof.
  intros Hα y; split.
  - apply (bach_mono_index f Hf (badd α bzero) α); auto.
    rewrite (badd_eq α bzero).
    apply bsub_blub_empty; intros [].
  - apply (bach_mono_index f Hf α (badd α bzero)).
    + rewrite (badd_eq α bzero). apply bsub_blub_l.
    + apply bmono_badd_zero; auto.
Qed.

Theorem bach_succ_step f (Hf : forall x y, x ≤ y -> f x ≤ f y) α G :
  bmono f α -> BRep f α G -> BRep f (badd α (bsucc bzero)) (enum_fixpoints G).
Proof.
  intros Hα [HG [Hrep Hcl]].
  assert (Hα0 : forall y, bach f (badd α bzero) y ≈ bach f α y) by (apply bach_badd_zero; auto).
  assert (HT : bmono f (badd α (bsucc bzero))) by (apply bmono_badd_one; auto).
  destruct α as [A g C h].
  refine (bach_enum_step f (badd (bnode A g C h) (bsucc bzero)) G (inl (inr tt)) HG _ _ _ _).
  - apply bmono_bcomp; auto.
  - intros x Hx.
    change (bach f (badd (bnode A g C h) bzero) x ≈ G x).
    transitivity (bach f (bnode A g C h) x); [ apply Hα0 | apply Hrep; auto ].
  - intros x Hx.
    transitivity (bach f (bnode A g C h) x); [ apply f_le_bach | apply (proj1 (Hrep x Hx)) ].
  - intros k y Hy.
    assert (Hv : complete (enum_fixpoints G y)).
    { apply normal_complete; auto. apply enum_fixpoints_normal; auto. }
    assert (Hfix := enum_are_fixpoints G HG y Hy).
    destruct k as [[a|[]]|[c|[]]].
    + change (bach f (g a) (enum_fixpoints G y) ≤ enum_fixpoints G y).
      transitivity (bach f (g a) (G (enum_fixpoints G y))).
      { apply bach_monotone; auto. apply (proj1 Hα a). apply (proj1 Hfix). }
      transitivity (G (enum_fixpoints G y)); [ apply (Hcl (inl a)); auto | apply (proj2 Hfix) ].
    + change (bach f (badd (bnode A g C h) bzero) (enum_fixpoints G y) ≤ enum_fixpoints G y).
      transitivity (bach f (bnode A g C h) (enum_fixpoints G y)); [ apply (proj1 (Hα0 _)) | ].
      transitivity (G (enum_fixpoints G y)); [ apply (proj1 (Hrep _ Hv)) | apply (proj2 Hfix) ].
    + change (bach f (h c (enum_fixpoints G y)) 0 ≤ enum_fixpoints G y).
      transitivity (bach f (h c (G (enum_fixpoints G y))) 0).
      { apply (proj2 (proj2 Hα)). apply (proj1 Hfix). }
      transitivity (G (enum_fixpoints G y)); [ apply (Hcl (inr c)); auto | apply (proj2 Hfix) ].
Qed.

(** *** The Veblen step

Adding an ordinary ordinal ξ to an index α builds the Veblen hierarchy
over φ_α: φ_{α+ξ} = @veblen φ_α ξ@.  This single statement covers
zero, successor and (small) limit ξ uniformly, just as @veblen@ does.
The components inherited from α fix every value of @veblen G ξ@,
because such a value is either a value of G (when ξ has no children)
or a fixpoint of G (when it does); completeness of ξ makes this case
split constructive. *)

Lemma veblen_value_cases G : normal_function G ->
  forall ξ y, complete ξ -> complete y ->
    veblen G ξ y ≈ G y \/ veblen G ξ y ≈ G (veblen G ξ y).
Proof.
  intros HG [X k] y Hξ Hy.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [[[x0]|Hn] _]].
  - right. split.
    + apply normal_inflationary; auto.
      apply veblen_complete; auto. apply normal_complete; auto.
    + apply veblen_fixpoint_zero; auto.
      rewrite ord_lt_unfold. exists x0. apply zero_least.
  - left. rewrite veblen_unroll. split.
    + apply lub_least; [ reflexivity | ].
      apply sup_least; intro i. elim (Hn (inhabits i)).
    + apply lub_le1.
Qed.

Lemma veblen_comp_closure f α G :
  BRep f α G ->
  (forall k x y, x ≤ y -> bcomp f α k x ≤ bcomp f α k y) ->
  forall ξ y, complete ξ -> complete y ->
  forall k, bcomp f α k (veblen G ξ y) ≤ veblen G ξ y.
Proof.
  intros [HG [_ Hcl]] Hmono ξ y Hξ Hy k.
  assert (Hvc : complete (veblen G ξ y)).
  { apply veblen_complete; auto. apply normal_complete; auto. }
  destruct (veblen_value_cases G HG ξ y Hξ Hy) as [H|H].
  - transitivity (bcomp f α k (G y)); [ apply Hmono, (proj1 H) | ].
    transitivity (G y); [ apply Hcl; auto | apply (proj2 H) ].
  - transitivity (bcomp f α k (G (veblen G ξ y))); [ apply Hmono, (proj1 H) | ].
    transitivity (G (veblen G ξ y)); [ apply Hcl; auto | apply (proj2 H) ].
Qed.

Theorem bach_veblen_step f (Hf : forall x y, x ≤ y -> f x ≤ f y) α G :
  bmono f α -> BRep f α G ->
  forall ξ, complete ξ -> BRep f (badd α (embed ξ)) (veblen G ξ).
Proof.
  intros Hα HR.
  assert (HR' := HR). destruct HR' as [HG [Hrep Hcl]].
  assert (Hmα := bmono_bcomp f Hf α Hα).
  destruct α as [A g C h].
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [_ Hkc]].
  assert (HT : bmono f (badd (bnode A g C h) (embed (ord X k)))) by (apply bmono_badd_embed; auto).
  assert (HV : normal_function (veblen G (ord X k))) by (apply veblen_normal; auto).
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (badd (bnode A g C h) (embed (ord X k))) kk (veblen G (ord X k) y)
             ≤ veblen G (ord X k) y).
  { intros kk y Hy.
    assert (Hvc : complete (veblen G (ord X k) y)) by (apply normal_complete; auto).
    destruct kk as [[a|i]|[c|[]]].
    - change (bcomp f (bnode A g C h) (inl a) (veblen G (ord X k) y) ≤ veblen G (ord X k) y).
      apply veblen_comp_closure; auto.
    - change (bach f (badd (bnode A g C h) (embed (k i))) (veblen G (ord X k) y)
              ≤ veblen G (ord X k) y).
      transitivity (veblen G (k i) (veblen G (ord X k) y)).
      + apply (proj1 (proj1 (proj2 (Hk i (Hkc i))) _ Hvc)).
      + apply (proj1 (veblen_fixpoints G HG (k i) (ord X k) y (Hkc i) Hξ Hy
                                       (index_lt (ord X k) i))).
    - change (bcomp f (bnode A g C h) (inr c) (veblen G (ord X k) y) ≤ veblen G (ord X k) y).
      apply veblen_comp_closure; auto. }
  split; [ exact HV | split; [ | exact Hcomp ] ].
  induction y as [Y hh Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (badd (bnode A g C h) (embed (ord X k))) (ord Y hh j)) ≈
               limOrd (fun j => veblen G (ord X k) (ord Y hh j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => veblen G (ord X k) (ord Y hh j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (bach f (bnode A g C h) (ord Y hh)); [ apply f_le_bach | ].
      transitivity (G (ord Y hh)); [ apply (proj1 (Hrep _ Hyc)) | ].
      rewrite veblen_unroll. apply lub_le1.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hf _ HT) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply veblen_increasing; auto.
      apply (index_lt (ord Y hh) j).
  - rewrite (veblen_unroll G (ord X k) (ord Y hh)).
    apply lub_least.
    + transitivity (bach f (bnode A g C h) (ord Y hh)); [ apply (proj2 (Hrep _ Hyc)) | ].
      apply bach_le_badd_embed; auto.
    + apply sup_least; intro i.
      eapply ord_le_trans;
        [ | apply (bach_comp_le f (badd (bnode A g C h) (embed (ord X k))) (ord Y hh) (inl (inr i))) ].
      assert (HVi : normal_function (veblen G (k i))) by (apply veblen_normal; auto).
      apply (proj2 (fixOrd_eq_func_complete
                      (bcomp f (badd (bnode A g C h) (embed (ord X k))) (inl (inr i)))
                      (veblen G (k i)) _ _
                      (proj1 (proj2 (Hk i (Hkc i))))
                      (bmono_bcomp f Hf _ HT (inl (inr i)))
                      (normal_monotone _ HVi) (normal_complete _ HVi) Hs Hsc)).
Qed.

(** *** The +Ω step

Adding Ω to an index α diagonalizes the Veblen hierarchy over φ_α:
the new Ω-family is ξ ↦ α+ξ, whose diagonal is ξ ↦ φ_{α+ξ}(0) =
@veblen G ξ 0@ by the Veblen step.  So φ_{α+Ω} enumerates the
fixpoints of that diagonal, generalizing Γ (the case α = 0). *)

Lemma bsub_badd_embed α : forall ξ ξ', ξ ≤ ξ' ->
  bsub (badd α (embed ξ)) (badd α (embed ξ')).
Proof.
  destruct α as [A g C h].
  induction ξ as [X k Hk]; intros [X' k'] H.
  rewrite (badd_eq _ (embed (ord X k))), (badd_eq _ (embed (ord X' k'))).
  simpl; split.
  - intros [a|i].
    + exists (inl a). apply bsub_refl.
    + destruct (ord_le_subord _ _ H i) as [j Hj].
      exists (inr j). apply Hk. exact Hj.
  - intros [c|[]].
    exists (inl c). intro ξ0. apply bsub_refl.
Qed.

Lemma badd_embed_diag_mono f (Hf : forall x y, x ≤ y -> f x ≤ f y) α :
  bmono f α ->
  forall ξ ξ', ξ ≤ ξ' -> bach f (badd α (embed ξ)) 0 ≤ bach f (badd α (embed ξ')) 0.
Proof.
  intros Hα ξ ξ' H.
  apply bach_mono_index; auto.
  - apply bsub_badd_embed; auto.
  - apply bmono_badd_embed; auto.
Qed.

Lemma bmono_badd_Ω f (Hf : forall x y, x ≤ y -> f x ≤ f y) α :
  bmono f α -> bmono f (badd α bOmega).
Proof.
  intro Hα.
  rewrite (badd_eq α bOmega).
  apply bmono_blub; auto.
  unfold baddR; simpl.
  split; [ intros [] | split ].
  - intros _ ξ. apply bmono_badd_embed; auto.
  - intros _ ξ ξ' H. apply badd_embed_diag_mono; auto.
Qed.

Theorem bach_plusΩ_step f (Hf : forall x y, x ≤ y -> f x ≤ f y) α G :
  bmono f α -> BRep f α G ->
  BRep f (badd α bOmega) (enum_fixpoints (fun ξ => veblen G ξ 0)).
Proof.
  intros Hα HR.
  assert (HR' := HR). destruct HR' as [HG [Hrep Hcl]].
  assert (HN : normal_function (fun ξ => veblen G ξ 0)) by (apply veblen_first_normal; auto).
  assert (HT : bmono f (badd α bOmega)) by (apply bmono_badd_Ω; auto).
  assert (Hmα := bmono_bcomp f Hf α Hα).
  assert (Hplus : forall ξ, complete ξ -> BRep f (badd α (embed ξ)) (veblen G ξ)).
  { intros; apply bach_veblen_step; auto. }
  assert (Hcα := veblen_comp_closure f α G HR Hmα).
  destruct α as [A g C h].
  refine (bach_enum_step f (badd (bnode A g C h) bOmega) _ (inr (inr tt)) HN
                         (bmono_bcomp f Hf _ HT) _ _ _).
  - intros x Hx.
    change (bach f (badd (bnode A g C h) (embed x)) 0 ≈ veblen G x 0).
    apply (proj1 (proj2 (Hplus x Hx))). apply zero_complete.
  - intros x Hx.
    transitivity (G x).
    { transitivity (bach f (bnode A g C h) x); [ apply f_le_bach | apply (proj1 (Hrep x Hx)) ]. }
    transitivity (G (x + 0)).
    { apply normal_monotone; [ exact HG | apply (proj2 (addOrd_zero_r x)) ]. }
    apply veblen_fax; auto using zero_complete.
  - intros kk y Hy.
    assert (Hv : complete (enum_fixpoints (fun ξ => veblen G ξ 0) y)).
    { apply normal_complete; [ apply enum_fixpoints_normal; auto | auto ]. }
    assert (Hfix := enum_are_fixpoints _ HN y Hy).
    destruct kk as [[a|[]]|[c|[]]].
    + change (bcomp f (bnode A g C h) (inl a) (enum_fixpoints (fun ξ => veblen G ξ 0) y)
              ≤ enum_fixpoints (fun ξ => veblen G ξ 0) y).
      transitivity (bcomp f (bnode A g C h) (inl a)
                          (veblen G (enum_fixpoints (fun ξ => veblen G ξ 0) y) 0)).
      { apply Hmα, (proj1 Hfix). }
      transitivity (veblen G (enum_fixpoints (fun ξ => veblen G ξ 0) y) 0); [ | apply (proj2 Hfix) ].
      apply Hcα; auto using zero_complete.
    + change (bcomp f (bnode A g C h) (inr c) (enum_fixpoints (fun ξ => veblen G ξ 0) y)
              ≤ enum_fixpoints (fun ξ => veblen G ξ 0) y).
      transitivity (bcomp f (bnode A g C h) (inr c)
                          (veblen G (enum_fixpoints (fun ξ => veblen G ξ 0) y) 0)).
      { apply Hmα, (proj1 Hfix). }
      transitivity (veblen G (enum_fixpoints (fun ξ => veblen G ξ 0) y) 0); [ | apply (proj2 Hfix) ].
      apply Hcα; auto using zero_complete.
    + change (bach f (badd (bnode A g C h) (embed (enum_fixpoints (fun ξ => veblen G ξ 0) y))) 0
              ≤ enum_fixpoints (fun ξ => veblen G ξ 0) y).
      transitivity (veblen G (enum_fixpoints (fun ξ => veblen G ξ 0) y) 0); [ | apply (proj2 Hfix) ].
      apply (proj1 (proj1 (proj2 (Hplus _ Hv)) 0 zero_complete)).
Qed.

(** *** The base case: φ_0 = f *)

Lemma bach_bzero f (y:Ord) : bach f bzero y ≈ f y.
Proof.
  rewrite bach_unroll'. split.
  - apply lub_least; [ reflexivity | ].
    apply lub_least; apply sup_least; intros [].
  - apply lub_le1.
Qed.

Lemma bmono_bzero f : bmono f bzero.
Proof.
  simpl; split; [ intros [] | split; intros [] ].
Qed.

Theorem bach_zero_rep f : normal_function f -> BRep f bzero f.
Proof.
  intro Hf.
  split; [ exact Hf | split ].
  - intros y _; apply bach_bzero.
  - intros [[]|[]].
Qed.

(** ** Calibrations, as corollaries of the step theorems *)

Lemma powOmega_le_veblen0 x : complete x -> powOmega x ≤ veblen powOmega x 0.
Proof.
  intro Hx.
  transitivity (powOmega (x + 0)).
  - apply powOmega_monotone, (proj2 (addOrd_zero_r x)).
  - apply veblen_fax; auto using powOmega_normal, zero_complete.
Qed.

(** φ_Ω enumerates the strongly critical ordinals: φ_Ω(0) = Γ₀. *)
Theorem bach_Ω_rep : BRep powOmega bOmega Γ.
Proof.
  apply bach_Ωlim_step.
  - apply veblen_first_normal, powOmega_normal.
  - apply bach_embed0_mono.
  - intros x _; apply bach_embed, powOmega_monotone.
  - apply powOmega_le_veblen0.
Qed.

Corollary bach_Ω_Γ : forall y, complete y -> bach powOmega bOmega y ≈ Γ y.
Proof. apply bach_Ω_rep. Qed.

(** φ_{Ω+ξ} is the Veblen hierarchy over Γ. *)
Theorem bach_Ω_plus_rep ξ : complete ξ -> BRep powOmega (badd bOmega (embed ξ)) (veblen Γ ξ).
Proof.
  apply bach_veblen_step; auto using powOmega_monotone, bach_Ω_rep.
  apply bmono_Ω, powOmega_monotone.
Qed.

Corollary bach_Ω_plus : forall ξ, complete ξ -> forall y, complete y ->
  bach powOmega (badd bOmega (embed ξ)) y ≈ veblen Γ ξ y.
Proof.
  intros ξ Hξ. apply (bach_Ω_plus_rep ξ Hξ).
Qed.

Theorem bach_Ω1_rep : BRep powOmega (badd bOmega (bsucc bzero)) (enum_fixpoints Γ).
Proof.
  apply bach_succ_step.
  - apply powOmega_monotone.
  - apply bmono_Ω, powOmega_monotone.
  - apply bach_Ω_rep.
Qed.

(** *** φ_{Ω·2} enumerates the fixpoints of ξ ↦ φ_{Ω+ξ}(0) *)

Definition bOmega2 : BOrd := badd bOmega bOmega.

Lemma bmono_Ω2 f (Hf : forall x y, x ≤ y -> f x ≤ f y) : bmono f bOmega2.
Proof.
  apply bmono_badd_Ω, bmono_Ω; auto.
Qed.

Definition Γ2 : Ord -> Ord := enum_fixpoints (fun ξ => veblen Γ ξ 0).

Theorem bach_Ω2_rep : BRep powOmega bOmega2 Γ2.
Proof.
  apply bach_plusΩ_step.
  - apply powOmega_monotone.
  - apply bmono_Ω, powOmega_monotone.
  - apply bach_Ω_rep.
Qed.

Corollary bach_Ω2 : forall y, complete y -> bach powOmega bOmega2 y ≈ Γ2 y.
Proof. apply bach_Ω2_rep. Qed.

(** *** φ_{Ω·n} is the n-fold iterated Γ construction *)

Fixpoint bOmegaMul (n:nat) : BOrd :=
  match n with
  | O => bzero
  | S n' => badd (bOmegaMul n') bOmega
  end.

Fixpoint Γiter (f:Ord -> Ord) (n:nat) : Ord -> Ord :=
  match n with
  | O => f
  | S n' => enum_fixpoints (fun ξ => veblen (Γiter f n') ξ 0)
  end.

Theorem bach_Ωmul_rep f : normal_function f ->
  forall n, bmono f (bOmegaMul n) /\ BRep f (bOmegaMul n) (Γiter f n).
Proof.
  intros Hf n.
  assert (Hm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction n as [|n [IH1 IH2]]; simpl.
  - split; [ apply bmono_bzero | apply bach_zero_rep; auto ].
  - split; [ apply bmono_badd_Ω; auto | apply bach_plusΩ_step; auto ].
Qed.

(** In particular φ_{0+Ω} is Γ, definitionally on the right. *)
Example bach_Ωmul1_Γ : forall y, complete y -> bach powOmega (bOmegaMul 1) y ≈ Γ y.
Proof.
  apply (proj2 (bach_Ωmul_rep powOmega powOmega_normal 1)).
Qed.

(** ** Multiples of Ω: φ_{Ω·ξ} is ternary Veblen

The tree @bmul bOmega (embed ξ)@ merges, via @bsup@, the children of
the trees Ω·ξ_i + Ω.  Its components are therefore the components of
each Ω·ξ_i together with each diagonal ζ ↦ φ_{Ω·ξ_i+ζ}(0).  We show
that it represents the third column of Schütte's Klammersymbols,
@schutte_column f 2 ξ@, i.e., the ternary Veblen function φ(ξ,0,·),
for all complete ξ (including limits), and deduce that φ_{Ω²}
enumerates the fixpoints of ξ ↦ φ(ξ,0,0).
*)

Lemma bmono_small f x : bmono f x -> forall a, bmono f (bsmallSz x a).
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_big f x : bmono f x -> forall c ξ, bmono f (bbigSz x c ξ).
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_diag f x : bmono f x ->
  forall c ξ ξ', ξ ≤ ξ' -> bach f (bbigSz x c ξ) 0 ≤ bach f (bbigSz x c ξ') 0.
Proof. destruct x; simpl; intuition. Qed.

Lemma bmono_bsup f {I:Type} (F:I -> BOrd) : (forall i, bmono f (F i)) -> bmono f (bsup F).
Proof.
  intro H; simpl.
  split; [ | split ].
  - intros [i a]. apply bmono_small; auto.
  - intros [i c] ξ. apply bmono_big; auto.
  - intros [i c] ξ ξ' Hξ. apply bmono_diag; auto.
Qed.

Lemma bmono_bmulΩ f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall ξ, bmono f (bmul bOmega (embed ξ)).
Proof.
  induction ξ as [X k Hk].
  rewrite (bmul_eq bOmega (embed (ord X k))).
  apply bmono_blub.
  - unfold bmulS. apply bmono_bsup. intro a.
    apply bmono_badd_Ω; auto. apply (Hk a).
  - unfold bmulB; simpl. split; [ intros [] | split; intros [] ].
Qed.

Lemma bsub_small x y : bsub x y -> forall a, exists b, bsub (bsmallSz x a) (bsmallSz y b).
Proof. destruct x; destruct y; simpl; intuition. Qed.

Lemma bsub_big x y : bsub x y ->
  forall c, exists d, forall ξ, bsub (bbigSz x c ξ) (bbigSz y d ξ).
Proof. destruct x; destruct y; simpl; intuition. Qed.

Lemma bsub_bsup {I J:Type} (F:I -> BOrd) (F':J -> BOrd) :
  (forall i, exists j, bsub (F i) (F' j)) -> bsub (bsup F) (bsup F').
Proof.
  intro H; simpl; split.
  - intros [i a].
    destruct (H i) as [j Hj].
    destruct (bsub_small _ _ Hj a) as [b Hb].
    exists (existT _ j b). exact Hb.
  - intros [i c].
    destruct (H i) as [j Hj].
    destruct (bsub_big _ _ Hj c) as [d Hd].
    exists (existT _ j d). exact Hd.
Qed.

Lemma bsub_blub x x' y y' : bsub x x' -> bsub y y' -> bsub (blub x y) (blub x' y').
Proof.
  destruct x as [A g C h]; destruct x' as [A' g' C' h'];
    destruct y as [B k D l]; destruct y' as [B' k' D' l']; simpl.
  intros [Hx1 Hx2] [Hy1 Hy2]; split.
  - intros [a|b].
    + destruct (Hx1 a) as [a' Ha]. exists (inl a'). exact Ha.
    + destruct (Hy1 b) as [b' Hb]. exists (inr b'). exact Hb.
  - intros [c|d].
    + destruct (Hx2 c) as [c' Hc]. exists (inl c'). exact Hc.
    + destruct (Hy2 d) as [d' Hd]. exists (inr d'). exact Hd.
Qed.

Lemma bsub_badd_embed_l x x' : bsub x x' -> forall ζ, bsub (badd x (embed ζ)) (badd x' (embed ζ)).
Proof.
  intros H ζ.
  induction ζ as [Z m Hm].
  rewrite (badd_eq x (embed (ord Z m))), (badd_eq x' (embed (ord Z m))).
  apply bsub_blub; auto.
  unfold baddR; simpl; split.
  - intro b. exists b. apply Hm.
  - intros [].
Qed.

Lemma bsub_badd_Ω_l x x' : bsub x x' -> bsub (badd x bOmega) (badd x' bOmega).
Proof.
  intro H.
  rewrite (badd_eq x bOmega), (badd_eq x' bOmega).
  apply bsub_blub; auto.
  unfold baddR; simpl; split.
  - intros [].
  - intros _. exists tt. intro ζ. apply bsub_badd_embed_l; auto.
Qed.

Lemma bsub_bmulΩ : forall ξ ξ', ξ ≤ ξ' ->
  bsub (bmul bOmega (embed ξ)) (bmul bOmega (embed ξ')).
Proof.
  induction ξ as [X k Hk]; intros [X' k'] H.
  rewrite (bmul_eq _ (embed (ord X k))), (bmul_eq _ (embed (ord X' k'))).
  apply bsub_blub.
  - unfold bmulS. apply bsub_bsup. intro a.
    destruct (ord_le_subord _ _ H a) as [b Hb].
    exists b. apply bsub_badd_Ω_l. apply Hk. exact Hb.
  - unfold bmulB; simpl; split; intros [].
Qed.

(** Classification of the components of α+Ω and of Ω·ξ. *)
Lemma bcomp_badd_Ω_forall f T (P:(Ord -> Ord) -> Prop) :
  (forall k, P (bcomp f T k)) ->
  P (fun ζ => bach f (badd T (embed ζ)) 0) ->
  forall k, P (bcomp f (badd T bOmega) k).
Proof.
  destruct T as [A g C h].
  intros H1 H2 [[a|[]]|[c|[]]].
  - apply (H1 (inl a)).
  - apply (H1 (inr c)).
  - apply H2.
Qed.

Lemma badd_Ω_diag f T :
  exists k, bcomp f (badd T bOmega) k = (fun ζ => bach f (badd T (embed ζ)) 0).
Proof.
  destruct T. exists (inr (inr tt)). reflexivity.
Qed.

Lemma bcomp_bmulΩ_forall f X (k:X -> Ord) (P:(Ord -> Ord) -> Prop) :
  (forall b kk, P (bcomp f (badd (bmul bOmega (embed (k b))) bOmega) kk)) ->
  forall kk, P (bcomp f (bmul bOmega (embed (ord X k))) kk).
Proof.
  intro H.
  intros [[[b a]|[]]|[[b c]|[]]].
  - apply (H b (inl a)).
  - apply (H b (inr c)).
Qed.

Lemma bach_bmulΩ_diag_le f X (k:X -> Ord) (y:Ord) b :
  fixOrd (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
         (limOrd (fun j => bach f (bmul bOmega (embed (ord X k))) (y j)))
  ≤ bach f (bmul bOmega (embed (ord X k))) y.
Proof.
  destruct (badd_Ω_diag f (bmul bOmega (embed (k b)))) as [kk Hkk].
  rewrite <- Hkk.
  destruct kk as [a|c].
  - exact (bach_comp_le f (bmul bOmega (embed (ord X k))) y (inl (inl (existT _ b a)))).
  - exact (bach_comp_le f (bmul bOmega (embed (ord X k))) y (inr (inl (existT _ b c)))).
Qed.

Definition S2 (f:Ord -> Ord) (ξ:Ord) : Ord -> Ord := schutte_column f (succOrd 1) ξ.

Lemma complete_1 : complete 1.
Proof. apply succ_complete, zero_complete. Qed.

Lemma complete_2 : complete (succOrd 1).
Proof. apply succ_complete, complete_1. Qed.

Lemma lt_0_2 : 0 < succOrd 1.
Proof. rewrite ord_lt_unfold. exists tt. apply zero_least. Qed.

Theorem bach_Ωtimes_rep f (Hf : normal_function f) :
  forall ξ, complete ξ -> BRep f (bmul bOmega (embed ξ)) (S2 f ξ).
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [_ Hkc]].
  assert (HS : normal_function (S2 f (ord X k))).
  { apply schutte_column_normal; auto using complete_2. }
  assert (HSk : forall b, normal_function (S2 f (k b))).
  { intro b. apply schutte_column_normal; auto using complete_2. }
  assert (HT : bmono f (bmul bOmega (embed (ord X k)))) by (apply bmono_bmulΩ; auto).
  assert (HTk : forall b, bmono f (bmul bOmega (embed (k b)))) by (intro; apply bmono_bmulΩ; auto).
  assert (Hplus : forall b ζ, complete ζ ->
             BRep f (badd (bmul bOmega (embed (k b))) (embed ζ)) (veblen (S2 f (k b)) ζ)).
  { intros b ζ Hζ. apply bach_veblen_step; auto. }
  assert (Hdiag : forall b x, complete x ->
             bach f (badd (bmul bOmega (embed (k b))) (embed x)) 0 ≈
             schutte_column (S2 f (k b)) 1 x 0).
  { intros b x Hx.
    transitivity (veblen (S2 f (k b)) x 0).
    - apply (Hplus b x Hx); apply zero_complete.
    - symmetry. apply schutte_column_veblen; auto using zero_complete. }
  (* every component fixes the values of S2 ξ *)
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (bmul bOmega (embed (ord X k))) kk (S2 f (ord X k) y) ≤ S2 f (ord X k) y).
  { intros kk y Hy.
    assert (Hv : complete (S2 f (ord X k) y)) by (apply normal_complete; auto).
    apply (bcomp_bmulΩ_forall f X k (fun g => g (S2 f (ord X k) y) ≤ S2 f (ord X k) y)).
    intro b.
    assert (Hfix0 : S2 f (k b) (S2 f (ord X k) y) ≤ S2 f (ord X k) y).
    { transitivity (schutte_column (S2 f (k b)) 0 (S2 f (ord X k) y) 0).
      - rewrite schutte_column0. apply normal_monotone; auto. apply addOrd_le1.
      - apply schutte_column_fixpoint; auto using complete_2, zero_complete, lt_0_2.
        apply (index_lt (ord X k) b). }
    apply (bcomp_badd_Ω_forall f (bmul bOmega (embed (k b)))
             (fun g => g (S2 f (ord X k) y) ≤ S2 f (ord X k) y)).
    - intro kk'.
      transitivity (bcomp f (bmul bOmega (embed (k b))) kk' (S2 f (k b) (S2 f (ord X k) y))).
      { apply bmono_bcomp; auto. apply normal_inflationary; auto. }
      transitivity (S2 f (k b) (S2 f (ord X k) y)); auto.
      apply (Hk b (Hkc b)); auto.
    - transitivity (schutte_column (S2 f (k b)) 1 (S2 f (ord X k) y) 0).
      + apply (proj1 (Hdiag b _ Hv)).
      + apply schutte_column_fixpoint; auto using complete_2, complete_1, succ_lt.
        apply (index_lt (ord X k) b). }
  split; [ exact HS | split; [ | exact Hcomp ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (bmul bOmega (embed (ord X k))) (ord Y h j)) ≈
               limOrd (fun j => S2 f (ord X k) (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => S2 f (ord X k) (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (f (ord X k + ord Y h)).
      * apply Hfm, addOrd_le2.
      * apply schutte_column_le_f; auto.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hfm _ HT) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply normal_increasing; auto.
      apply (index_lt (ord Y h) j).
  - eapply ord_le_trans;
      [ apply (proj1 (schutte_column_succ f 1 (ord X k) (ord Y h) Hf complete_1 Hξ Hyc)) | ].
    apply lub_least; [ apply f_le_bach | ].
    apply sup_least; intro b.
    eapply ord_le_trans; [ | apply (bach_bmulΩ_diag_le f X k (ord Y h) b) ].
    assert (HN1 : normal_function (fun δ => schutte_column (S2 f (k b)) 1 δ 0)).
    { apply schutte_column_normal_arg; auto using complete_1. }
    apply (proj2 (fixOrd_eq_func_complete
                    (fun ζ => bach f (badd (bmul bOmega (embed (k b))) (embed ζ)) 0)
                    (fun δ => schutte_column (S2 f (k b)) 1 δ 0) _ _
                    (Hdiag b)
                    (badd_embed_diag_mono f Hfm _ (HTk b))
                    (normal_monotone _ HN1) (normal_complete _ HN1) Hs Hsc)).
Qed.

(** φ_{Ω²} enumerates the fixpoints of ξ ↦ φ(ξ,0,0). *)
Definition bOmegaSq : BOrd := bmul bOmega bOmega.

Theorem bach_Ωsq_rep f (Hf : normal_function f) :
  BRep f bOmegaSq (enum_fixpoints (fun ξ => S2 f ξ 0)).
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HN : normal_function (fun ξ => S2 f ξ 0)).
  { apply schutte_column_normal_arg; auto using complete_2. }
  refine (bach_enum_step f bOmegaSq _ (inr (inr tt)) HN _ _ _ _).
  - intros [[[[] ?]|[]]|[[[] ?]|[]]] x y Hxy.
    apply bach_mono_index; auto.
    + apply bsub_bmulΩ; auto.
    + apply bmono_bmulΩ; auto.
  - intros x Hx. apply (bach_Ωtimes_rep f Hf x Hx); apply zero_complete.
  - intros x Hx.
    transitivity (f (x + 0)); [ apply Hfm, (proj2 (addOrd_zero_r x)) | ].
    apply schutte_column_le_f; auto.
  - intros [[[[] ?]|[]]|[[[] ?]|[]]] y Hy.
    assert (Hv : complete (enum_fixpoints (fun ξ => S2 f ξ 0) y)).
    { apply normal_complete; [ apply enum_fixpoints_normal; auto | auto ]. }
    change (bach f (bmul bOmega (embed (enum_fixpoints (fun ξ => S2 f ξ 0) y))) 0
            ≤ enum_fixpoints (fun ξ => S2 f ξ 0) y).
    transitivity (S2 f (enum_fixpoints (fun ξ => S2 f ξ 0) y) 0).
    + apply (bach_Ωtimes_rep f Hf _ Hv); apply zero_complete.
    + apply (proj2 (enum_are_fixpoints _ HN y Hy)).
Qed.

(** With base 1+x, φ_{Ω²}(0) is Ackermann's ordinal, as defined in
    @AckermannTower@. *)
Theorem bach_Ωsq_Ackermann : bach (addOrd 1) bOmegaSq 0 ≈ AckermannOrdinal.
Proof.
  assert (HN : normal_function (fun ξ => S2 (addOrd 1) ξ 0)).
  { apply schutte_column_normal_arg; auto using complete_2, onePlus_normal. }
  transitivity (enum_fixpoints (fun ξ => S2 (addOrd 1) ξ 0) 0).
  { apply (bach_Ωsq_rep (addOrd 1) onePlus_normal); apply zero_complete. }
  transitivity (fixOrd (fun ξ => S2 (addOrd 1) ξ 0) 0).
  { apply enum_fixpoints_zero; auto. }
  unfold AckermannOrdinal.
  apply fixOrd_eq_func_complete.
  - intros x Hx. apply schutte_column_2_ackermann_tower; auto using onePlus_normal, zero_complete.
  - apply normal_monotone; auto.
  - intros x y Hxy. apply ackermann_tower_monotone; auto with ord.
  - apply normal_complete, ackermann_tower_normal_first, onePlus_normal.
  - reflexivity.
  - apply zero_complete.
Qed.

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

(** ** Ω-multiples over an arbitrary base

Generalizing @bach_Ωtimes_rep@: if β represents G, then β + Ω·ξ
represents the second Schütte column over G.  The components of
β + Ω·ξ are those of β, those of each β + Ω·ξ_i, and the diagonals
ζ ↦ φ_{β+(Ω·ξ_i+ζ)}(0); the last are identified, via associativity,
with the Veblen step over β + Ω·ξ_i. *)

Lemma fixOrd_ext_eq F F' a : (forall x, F x = F' x) -> fixOrd F a ≈ fixOrd F' a.
Proof.
  intro H.
  assert (Hiter : forall n, iter_f F a n = iter_f F' a n).
  { induction n; simpl; auto. rewrite IHn. apply H. }
  unfold fixOrd. apply sup_ord_eq_morphism; intro n.
  rewrite Hiter. reflexivity.
Qed.

Lemma badd_Ω_big T : exists c, forall ζ, bbigSz (badd T bOmega) c ζ = badd T (embed ζ).
Proof.
  destruct T. exists (inr tt). intro; reflexivity.
Qed.

Lemma S2_fix0 G (HG : normal_function G) a ξ y :
  complete a -> complete ξ -> complete y -> a < ξ ->
  S2 G a (S2 G ξ y) ≤ S2 G ξ y.
Proof.
  intros Ha Hξ Hy Haξ.
  transitivity (schutte_column (S2 G a) 0 (S2 G ξ y) 0).
  - rewrite schutte_column0.
    apply normal_monotone; [ apply schutte_column_normal; auto using complete_2 | ].
    apply addOrd_le1.
  - apply schutte_column_fixpoint; auto using complete_2, zero_complete, lt_0_2.
Qed.

Lemma S2_value_cases G (HG : normal_function G) ξ y :
  complete ξ -> complete y ->
  S2 G ξ y ≈ G y \/ S2 G ξ y ≈ G (S2 G ξ y).
Proof.
  intros Hξ Hy.
  destruct ξ as [X k].
  assert (Hξ' := Hξ). destruct Hξ' as [_ [[[x0]|Hn] Hkc]].
  - right.
    assert (Hv : complete (S2 G (ord X k) y)).
    { apply normal_complete; [ apply schutte_column_normal; auto using complete_2 | auto ]. }
    split.
    + apply normal_inflationary; auto.
    + transitivity (G (k x0 + S2 G (ord X k) y)).
      { apply normal_monotone; auto. apply addOrd_le2. }
      transitivity (S2 G (k x0) (S2 G (ord X k) y)).
      { apply schutte_column_le_f. apply normal_monotone; auto. }
      apply S2_fix0; auto. apply (index_lt (ord X k) x0).
  - left. split.
    + eapply ord_le_trans;
        [ apply (proj1 (schutte_column_succ G 1 (ord X k) y HG complete_1 Hξ Hy)) | ].
      apply lub_least; [ reflexivity | ].
      apply sup_least; intro i. elim (Hn (inhabits i)).
    + transitivity (G (ord X k + y)).
      { apply normal_monotone; auto. apply addOrd_le2. }
      apply schutte_column_le_f. apply normal_monotone; auto.
Qed.

Lemma bcomp_shift_bmulΩ_forall f β X (k:X -> Ord) (P:(Ord -> Ord) -> Prop) :
  (forall g g', (forall x, g x = g' x) -> P g -> P g') ->
  (forall kk, P (bcomp f β kk)) ->
  (forall b kk, P (bcomp f (badd β (bmul bOmega (embed (k b)))) kk)) ->
  (forall b, P (fun ζ => bach f (badd β (badd (bmul bOmega (embed (k b))) (embed ζ))) 0)) ->
  forall kk, P (bcomp f (badd β (bmul bOmega (embed (ord X k)))) kk).
Proof.
  intros Pext H1 H2 H3 [s|c].
  - destruct (badd_small_cases β (bmul bOmega (embed (ord X k))) s) as [[a Ha]|[m Hm]].
    + apply (Pext (bcomp f β (inl a))); [ | apply H1 ].
      intro x.
      change (bach f (bsmallSz β a) x =
              bach f (bsmallSz (badd β (bmul bOmega (embed (ord X k)))) s) x).
      rewrite Ha. reflexivity.
    + destruct m as [[b m']|[]].
      change (bsmallSz (badd β (bmul bOmega (embed (ord X k)))) s =
              badd β (bsmallSz (badd (bmul bOmega (embed (k b))) bOmega) m')) in Hm.
      destruct (badd_small_cases (bmul bOmega (embed (k b))) bOmega m') as [[a'' Ha'']|[[] _]].
      destruct (badd_small_r β (bmul bOmega (embed (k b))) a'') as [t Ht].
      apply (Pext (bcomp f (badd β (bmul bOmega (embed (k b)))) (inl t))); [ | apply H2 ].
      intro x.
      change (bach f (bsmallSz (badd β (bmul bOmega (embed (k b)))) t) x =
              bach f (bsmallSz (badd β (bmul bOmega (embed (ord X k)))) s) x).
      rewrite Ht, Hm, Ha''. reflexivity.
  - destruct (badd_big_cases β (bmul bOmega (embed (ord X k))) c) as [[c' Hc]|[m Hm]].
    + apply (Pext (bcomp f β (inr c'))); [ | apply H1 ].
      intro x.
      change (bach f (bbigSz β c' x) 0 =
              bach f (bbigSz (badd β (bmul bOmega (embed (ord X k)))) c x) 0).
      rewrite Hc. reflexivity.
    + destruct m as [[b m']|[]].
      assert (Hm' : forall ξ, bbigSz (badd β (bmul bOmega (embed (ord X k)))) c ξ =
                              badd β (bbigSz (badd (bmul bOmega (embed (k b))) bOmega) m' ξ))
        by exact Hm.
      destruct (badd_big_cases (bmul bOmega (embed (k b))) bOmega m') as [[e He]|[d Hd]].
      * destruct (badd_big_r β (bmul bOmega (embed (k b))) e) as [t Ht].
        apply (Pext (bcomp f (badd β (bmul bOmega (embed (k b)))) (inr t))); [ | apply H2 ].
        intro x.
        change (bach f (bbigSz (badd β (bmul bOmega (embed (k b)))) t x) 0 =
                bach f (bbigSz (badd β (bmul bOmega (embed (ord X k)))) c x) 0).
        rewrite Ht, Hm', He. reflexivity.
      * apply (Pext (fun ζ => bach f (badd β (badd (bmul bOmega (embed (k b))) (embed ζ))) 0));
          [ | apply H3 ].
        intro x.
        change (bach f (badd β (badd (bmul bOmega (embed (k b))) (embed x))) 0 =
                bach f (bbigSz (badd β (bmul bOmega (embed (ord X k)))) c x) 0).
        rewrite Hm', Hd. reflexivity.
Qed.

Theorem bach_shift_Ωtimes_rep f (Hf : forall x y, x ≤ y -> f x ≤ f y) β G :
  bfam β -> BRep f β G ->
  forall ξ, complete ξ -> BRep f (badd β (bmul bOmega (embed ξ))) (S2 G ξ).
Proof.
  intros Hβ HR.
  assert (HR' := HR). destruct HR' as [HG [Hrep Hcl]].
  assert (HGm : forall x y, x ≤ y -> G x ≤ G y) by (apply normal_monotone; auto).
  assert (Hbm : bmono f β) by (apply bfam_bmono; auto).
  assert (HMfam : forall ξ, bfam (bmul bOmega (embed ξ))).
  { intro. apply bfam_bmul; auto using bfam_Ω, bfam_embed. }
  assert (Hmono : forall ξ, bmono f (badd β (bmul bOmega (embed ξ)))).
  { intro. apply bfam_bmono; auto. apply bfam_badd; auto. }
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [_ Hkc]].
  assert (HS : normal_function (S2 G (ord X k))).
  { apply schutte_column_normal; auto using complete_2. }
  assert (HIH : forall b, BRep f (badd β (bmul bOmega (embed (k b)))) (S2 G (k b))).
  { intro b. apply Hk; auto. }
  assert (Hplus : forall b ζ, complete ζ ->
             BRep f (badd (badd β (bmul bOmega (embed (k b)))) (embed ζ)) (veblen (S2 G (k b)) ζ)).
  { intros b ζ Hζ. apply bach_veblen_step; auto. }
  assert (Hdiag : forall b x, complete x ->
             bach f (badd β (badd (bmul bOmega (embed (k b))) (embed x))) 0 ≈
             schutte_column (S2 G (k b)) 1 x 0).
  { intros b x Hx.
    transitivity (bach f (badd (badd β (bmul bOmega (embed (k b)))) (embed x)) 0).
    { apply bach_badd_assoc; auto using bfam_embed. }
    transitivity (veblen (S2 G (k b)) x 0).
    { apply (Hplus b x Hx); apply zero_complete. }
    symmetry. apply schutte_column_veblen; auto using zero_complete.
    apply schutte_column_normal; auto using complete_2. }
  assert (Hdmono : forall b x y, x ≤ y ->
             bach f (badd β (badd (bmul bOmega (embed (k b))) (embed x))) 0 ≤
             bach f (badd β (badd (bmul bOmega (embed (k b))) (embed y))) 0).
  { intros b x y Hxy. apply bach_mono_index; auto.
    - apply bsub_badd_r, bsub_badd_r, bsub_embed; auto.
    - apply bfam_bmono; auto. apply bfam_badd; auto. apply bfam_badd; auto using bfam_embed. }
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (badd β (bmul bOmega (embed (ord X k)))) kk (S2 G (ord X k) y)
             ≤ S2 G (ord X k) y).
  { intros kk y Hy.
    assert (Hv : complete (S2 G (ord X k) y)) by (apply normal_complete; auto).
    apply (bcomp_shift_bmulΩ_forall f β X k (fun g => g (S2 G (ord X k) y) ≤ S2 G (ord X k) y)).
    - intros g g' Hgg' H. rewrite <- Hgg'. exact H.
    - intro kk'.
      destruct (S2_value_cases G HG (ord X k) y Hξ Hy) as [H|H].
      + transitivity (bcomp f β kk' (G y)).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G y); [ apply Hcl; auto | apply (proj2 H) ].
      + transitivity (bcomp f β kk' (G (S2 G (ord X k) y))).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G (S2 G (ord X k) y)); [ apply Hcl; auto | apply (proj2 H) ].
    - intros b kk'.
      assert (HSb : normal_function (S2 G (k b))).
      { apply schutte_column_normal; auto using complete_2. }
      transitivity (bcomp f (badd β (bmul bOmega (embed (k b)))) kk'
                          (S2 G (k b) (S2 G (ord X k) y))).
      { apply bmono_bcomp; auto. apply normal_inflationary; auto. }
      transitivity (S2 G (k b) (S2 G (ord X k) y)).
      { apply (HIH b); auto. }
      apply S2_fix0; auto. apply (index_lt (ord X k) b).
    - intro b.
      transitivity (schutte_column (S2 G (k b)) 1 (S2 G (ord X k) y) 0).
      + apply (proj1 (Hdiag b _ Hv)).
      + apply schutte_column_fixpoint; auto using complete_2, complete_1, succ_lt.
        apply (index_lt (ord X k) b). }
  split; [ exact HS | split; [ | exact Hcomp ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (badd β (bmul bOmega (embed (ord X k)))) (ord Y h j)) ≈
               limOrd (fun j => S2 G (ord X k) (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => S2 G (ord X k) (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (G (ord Y h)).
      { transitivity (bach f β (ord Y h)); [ apply f_le_bach | apply (proj1 (Hrep _ Hyc)) ]. }
      transitivity (G (ord X k + ord Y h)); [ apply HGm, addOrd_le2 | ].
      apply schutte_column_le_f; auto.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hf _ (Hmono _)) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply normal_increasing; auto.
      apply (index_lt (ord Y h) j).
  - eapply ord_le_trans;
      [ apply (proj1 (schutte_column_succ G 1 (ord X k) (ord Y h) HG complete_1 Hξ Hyc)) | ].
    apply lub_least.
    + transitivity (bach f β (ord Y h)); [ apply (proj2 (Hrep _ Hyc)) | ].
      apply bach_mono_index; auto.
      rewrite (badd_eq β (bmul bOmega (embed (ord X k)))). apply bsub_blub_l.
    + apply sup_least; intro b.
      assert (HN1 : normal_function (fun δ => schutte_column (S2 G (k b)) 1 δ 0)).
      { apply schutte_column_normal_arg; auto using complete_1.
        apply schutte_column_normal; auto using complete_2. }
      destruct (badd_Ω_big (bmul bOmega (embed (k b)))) as [c Hc].
      destruct (badd_big_r β (bmul bOmega (embed (ord X k))) (inl (existT _ b c))) as [t Ht].
      eapply ord_le_trans;
        [ | apply (bach_comp_le f (badd β (bmul bOmega (embed (ord X k)))) (ord Y h) (inr t)) ].
      assert (Heq : forall x,
                 (fun ζ => bach f (badd β (badd (bmul bOmega (embed (k b))) (embed ζ))) 0) x =
                 bcomp f (badd β (bmul bOmega (embed (ord X k)))) (inr t) x).
      { intro x.
        change (bach f (badd β (badd (bmul bOmega (embed (k b))) (embed x))) 0 =
                bach f (bbigSz (badd β (bmul bOmega (embed (ord X k)))) t x) 0).
        rewrite (Ht x).
        change (bach f (badd β (badd (bmul bOmega (embed (k b))) (embed x))) 0 =
                bach f (badd β (bbigSz (badd (bmul bOmega (embed (k b))) bOmega) c x)) 0).
        rewrite (Hc x). reflexivity. }
      eapply ord_le_trans; [ | apply (proj1 (fixOrd_ext_eq _ _ _ Heq)) ].
      apply (proj2 (fixOrd_eq_func_complete
                      (fun ζ => bach f (badd β (badd (bmul bOmega (embed (k b))) (embed ζ))) 0)
                      (fun δ => schutte_column (S2 G (k b)) 1 δ 0) _ _
                      (Hdiag b) (Hdmono b)
                      (normal_monotone _ HN1) (normal_complete _ HN1) Hs Hsc)).
Qed.

(** ** Powers of Ω and the finite Schütte columns

We abstract the proof of @bach_shift_Ωtimes_rep@ over the multiplier.
Let Q be an index tree with no small children, such that adding any
of its Ω-family members ζ to a base β' representing G' yields Schütte
column c over G'.  Then β + Q·ξ represents column c+1 over G.  For
Q = Ω this is the Veblen step (column 1); for Q·Ω, whose single family
is ζ ↦ Q·ζ, the hypothesis is the conclusion for Q.  Iterating gives
β + Ω^(n+1)·ξ ↔ column n+2. *)

Lemma BRep_ext f (Hf : forall x y, x ≤ y -> f x ≤ f y) T G G' :
  bmono f T -> BRep f T G -> normal_function G' ->
  (forall x, complete x -> G x ≈ G' x) -> BRep f T G'.
Proof.
  intros HT [HG [Hrep Hcl]] HG' Heq.
  split; [ exact HG' | split ].
  - intros y Hy. transitivity (G y); auto.
  - intros k y Hy.
    transitivity (bcomp f T k (G y)).
    { apply bmono_bcomp; auto. apply (proj2 (Heq y Hy)). }
    transitivity (G y); [ apply Hcl; auto | apply (proj1 (Heq y Hy)) ].
Qed.

Lemma lt_0_succ c : 0 < succOrd c.
Proof. rewrite ord_lt_unfold. exists tt. apply zero_least. Qed.

Lemma Scol_fix0 G (HG : normal_function G) c a ξ y :
  complete c -> complete a -> complete ξ -> complete y -> a < ξ ->
  schutte_column G (succOrd c) a (schutte_column G (succOrd c) ξ y) ≤ schutte_column G (succOrd c) ξ y.
Proof.
  intros Hc Ha Hξ Hy Haξ.
  transitivity (schutte_column (schutte_column G (succOrd c) a) 0 (schutte_column G (succOrd c) ξ y) 0).
  - rewrite schutte_column0.
    apply normal_monotone; [ apply schutte_column_normal; auto using succ_complete | ].
    apply addOrd_le1.
  - apply schutte_column_fixpoint; auto using succ_complete, zero_complete, lt_0_succ.
Qed.

Lemma Scol_value_cases G (HG : normal_function G) c ξ y :
  complete c -> complete ξ -> complete y ->
  schutte_column G (succOrd c) ξ y ≈ G y \/
  schutte_column G (succOrd c) ξ y ≈ G (schutte_column G (succOrd c) ξ y).
Proof.
  intros Hc Hξ Hy.
  destruct ξ as [X k].
  assert (Hξ' := Hξ). destruct Hξ' as [_ [[[x0]|Hn] Hkc]].
  - right.
    assert (Hv : complete (schutte_column G (succOrd c) (ord X k) y)).
    { apply normal_complete; [ apply schutte_column_normal; auto using succ_complete | auto ]. }
    split.
    + apply normal_inflationary; auto.
    + transitivity (G (k x0 + schutte_column G (succOrd c) (ord X k) y)).
      { apply normal_monotone; auto. apply addOrd_le2. }
      transitivity (schutte_column G (succOrd c) (k x0) (schutte_column G (succOrd c) (ord X k) y)).
      { apply schutte_column_le_f. apply normal_monotone; auto. }
      apply Scol_fix0; auto. apply (index_lt (ord X k) x0).
  - left. split.
    + eapply ord_le_trans;
        [ apply (proj1 (schutte_column_succ G c (ord X k) y HG Hc Hξ Hy)) | ].
      apply lub_least; [ reflexivity | ].
      apply sup_least; intro i. elim (Hn (inhabits i)).
    + transitivity (G (ord X k + y)).
      { apply normal_monotone; auto. apply addOrd_le2. }
      apply schutte_column_le_f. apply normal_monotone; auto.
Qed.

Lemma bcomp_shift_bmul_forall f β Q X (k:X -> Ord) (P:(Ord -> Ord) -> Prop) :
  (bsmall Q -> False) ->
  (forall g g', (forall x, g x = g' x) -> P g -> P g') ->
  (forall kk, P (bcomp f β kk)) ->
  (forall b kk, P (bcomp f (badd β (bmul Q (embed (k b)))) kk)) ->
  (forall b d, P (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0)) ->
  forall kk, P (bcomp f (badd β (bmul Q (embed (ord X k)))) kk).
Proof.
  intros HQs Pext H1 H2 H3 [s|c].
  - destruct (badd_small_cases β (bmul Q (embed (ord X k))) s) as [[a Ha]|[m Hm]].
    + apply (Pext (bcomp f β (inl a))); [ | apply H1 ].
      intro x.
      change (bach f (bsmallSz β a) x =
              bach f (bsmallSz (badd β (bmul Q (embed (ord X k)))) s) x).
      rewrite Ha. reflexivity.
    + destruct m as [[b m']|[]].
      change (bsmallSz (badd β (bmul Q (embed (ord X k)))) s =
              badd β (bsmallSz (badd (bmul Q (embed (k b))) Q) m')) in Hm.
      destruct (badd_small_cases (bmul Q (embed (k b))) Q m') as [[a'' Ha'']|[b'' _]];
        [ | elim (HQs b'') ].
      destruct (badd_small_r β (bmul Q (embed (k b))) a'') as [t Ht].
      apply (Pext (bcomp f (badd β (bmul Q (embed (k b)))) (inl t))); [ | apply H2 ].
      intro x.
      change (bach f (bsmallSz (badd β (bmul Q (embed (k b)))) t) x =
              bach f (bsmallSz (badd β (bmul Q (embed (ord X k)))) s) x).
      rewrite Ht, Hm, Ha''. reflexivity.
  - destruct (badd_big_cases β (bmul Q (embed (ord X k))) c) as [[c' Hc]|[m Hm]].
    + apply (Pext (bcomp f β (inr c'))); [ | apply H1 ].
      intro x.
      change (bach f (bbigSz β c' x) 0 =
              bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
      rewrite Hc. reflexivity.
    + destruct m as [[b m']|[]].
      assert (Hm' : forall ξ, bbigSz (badd β (bmul Q (embed (ord X k)))) c ξ =
                              badd β (bbigSz (badd (bmul Q (embed (k b))) Q) m' ξ))
        by exact Hm.
      destruct (badd_big_cases (bmul Q (embed (k b))) Q m') as [[e He]|[d Hd]].
      * destruct (badd_big_r β (bmul Q (embed (k b))) e) as [t Ht].
        apply (Pext (bcomp f (badd β (bmul Q (embed (k b)))) (inr t))); [ | apply H2 ].
        intro x.
        change (bach f (bbigSz (badd β (bmul Q (embed (k b)))) t x) 0 =
                bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
        rewrite Ht, Hm', He. reflexivity.
      * apply (Pext (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0));
          [ | apply H3 ].
        intro x.
        change (bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d x))) 0 =
                bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
        rewrite Hm', Hd. reflexivity.
Qed.

(** The hypothesis on a multiplier Q: adding a family member of Q to
    a base representing G' yields column c over G'. *)
Definition QCol f (Q:BOrd) (c:Ord) : Prop :=
  forall β' G', bfam β' -> BRep f β' G' ->
    forall d ζ, complete ζ -> BRep f (badd β' (bbigSz Q d ζ)) (schutte_column G' c ζ).

Theorem bach_power_step f (Hf : forall x y, x ≤ y -> f x ≤ f y) Q c :
  complete c -> bfam Q -> (bsmall Q -> False) -> bbig Q -> QCol f Q c ->
  forall β G, bfam β -> BRep f β G ->
  forall ξ, complete ξ -> BRep f (badd β (bmul Q (embed ξ))) (schutte_column G (succOrd c) ξ).
Proof.
  intros Hc HQ HQs d0 HQc β G Hβ HR.
  assert (HR' := HR). destruct HR' as [HG [Hrep Hcl]].
  assert (HGm : forall x y, x ≤ y -> G x ≤ G y) by (apply normal_monotone; auto).
  assert (Hbm : bmono f β) by (apply bfam_bmono; auto).
  assert (Hc1 : complete (succOrd c)) by (apply succ_complete; auto).
  assert (HMfam : forall ξ, bfam (bmul Q (embed ξ))).
  { intro. apply bfam_bmul; auto using bfam_embed. }
  assert (Hmono : forall ξ, bmono f (badd β (bmul Q (embed ξ)))).
  { intro. apply bfam_bmono; auto. apply bfam_badd; auto. }
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [_ [_ Hkc]].
  assert (HS : normal_function (schutte_column G (succOrd c) (ord X k))).
  { apply schutte_column_normal; auto. }
  assert (HSk : forall b, normal_function (schutte_column G (succOrd c) (k b))).
  { intro b. apply schutte_column_normal; auto. }
  assert (HIH : forall b, BRep f (badd β (bmul Q (embed (k b)))) (schutte_column G (succOrd c) (k b))).
  { intro b. apply Hk; auto. }
  assert (Hdiag : forall b d x, complete x ->
             bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d x))) 0 ≈
             schutte_column (schutte_column G (succOrd c) (k b)) c x 0).
  { intros b d x Hx.
    transitivity (bach f (badd (badd β (bmul Q (embed (k b)))) (bbigSz Q d x)) 0).
    { apply bach_badd_assoc; auto. apply bfam_big; auto. }
    apply (HQc _ _ (bfam_badd _ _ Hβ (HMfam _)) (HIH b) d x Hx); apply zero_complete. }
  assert (Hdmono : forall b d x y, x ≤ y ->
             bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d x))) 0 ≤
             bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d y))) 0).
  { intros b d x y Hxy. apply bach_mono_index; auto.
    - apply bsub_badd_r, bsub_badd_r. apply bfam_fam; auto.
    - apply bfam_bmono; auto. apply bfam_badd; auto. apply bfam_badd; auto. apply bfam_big; auto. }
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (badd β (bmul Q (embed (ord X k)))) kk (schutte_column G (succOrd c) (ord X k) y)
             ≤ schutte_column G (succOrd c) (ord X k) y).
  { intros kk y Hy.
    assert (Hv : complete (schutte_column G (succOrd c) (ord X k) y)) by (apply normal_complete; auto).
    apply (bcomp_shift_bmul_forall f β Q X k
             (fun g => g (schutte_column G (succOrd c) (ord X k) y) ≤ schutte_column G (succOrd c) (ord X k) y));
      auto.
    - intros g g' Hgg' H. rewrite <- Hgg'. exact H.
    - intro kk'.
      destruct (Scol_value_cases G HG c (ord X k) y Hc Hξ Hy) as [H|H].
      + transitivity (bcomp f β kk' (G y)).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G y); [ apply Hcl; auto | apply (proj2 H) ].
      + transitivity (bcomp f β kk' (G (schutte_column G (succOrd c) (ord X k) y))).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G (schutte_column G (succOrd c) (ord X k) y)); [ apply Hcl; auto | apply (proj2 H) ].
    - intros b kk'.
      transitivity (bcomp f (badd β (bmul Q (embed (k b)))) kk'
                          (schutte_column G (succOrd c) (k b) (schutte_column G (succOrd c) (ord X k) y))).
      { apply bmono_bcomp; auto. apply normal_inflationary; auto. }
      transitivity (schutte_column G (succOrd c) (k b) (schutte_column G (succOrd c) (ord X k) y)).
      { apply (HIH b); auto. }
      apply Scol_fix0; auto. apply (index_lt (ord X k) b).
    - intros b d.
      transitivity (schutte_column (schutte_column G (succOrd c) (k b)) c
                                   (schutte_column G (succOrd c) (ord X k) y) 0).
      + apply (proj1 (Hdiag b d _ Hv)).
      + apply schutte_column_fixpoint; auto using zero_complete, succ_lt.
        apply (index_lt (ord X k) b). }
  split; [ exact HS | split; [ | exact Hcomp ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (badd β (bmul Q (embed (ord X k)))) (ord Y h j)) ≈
               limOrd (fun j => schutte_column G (succOrd c) (ord X k) (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => schutte_column G (succOrd c) (ord X k) (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  split.
  - apply bach_le_comp.
    + transitivity (G (ord Y h)).
      { transitivity (bach f β (ord Y h)); [ apply f_le_bach | apply (proj1 (Hrep _ Hyc)) ]. }
      transitivity (G (ord X k + ord Y h)); [ apply HGm, addOrd_le2 | ].
      apply schutte_column_le_f; auto.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hf _ (Hmono _)) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply normal_increasing; auto.
      apply (index_lt (ord Y h) j).
  - eapply ord_le_trans;
      [ apply (proj1 (schutte_column_succ G c (ord X k) (ord Y h) HG Hc Hξ Hyc)) | ].
    apply lub_least.
    + transitivity (bach f β (ord Y h)); [ apply (proj2 (Hrep _ Hyc)) | ].
      apply bach_mono_index; auto.
      rewrite (badd_eq β (bmul Q (embed (ord X k)))). apply bsub_blub_l.
    + apply sup_least; intro b.
      assert (HN1 : normal_function (fun δ => schutte_column (schutte_column G (succOrd c) (k b)) c δ 0)).
      { apply schutte_column_normal_arg; auto. }
      destruct (badd_big_r (bmul Q (embed (k b))) Q d0) as [cc Hcc].
      destruct (badd_big_r β (bmul Q (embed (ord X k))) (inl (existT _ b cc))) as [t Ht].
      eapply ord_le_trans;
        [ | apply (bach_comp_le f (badd β (bmul Q (embed (ord X k)))) (ord Y h) (inr t)) ].
      assert (Heq : forall x,
                 (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d0 ζ))) 0) x =
                 bcomp f (badd β (bmul Q (embed (ord X k)))) (inr t) x).
      { intro x.
        change (bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d0 x))) 0 =
                bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) t x) 0).
        rewrite (Ht x).
        change (bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d0 x))) 0 =
                bach f (badd β (bbigSz (badd (bmul Q (embed (k b))) Q) cc x)) 0).
        rewrite (Hcc x). reflexivity. }
      eapply ord_le_trans; [ | apply (proj1 (fixOrd_ext_eq _ _ _ Heq)) ].
      apply (proj2 (fixOrd_eq_func_complete
                      (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d0 ζ))) 0)
                      (fun δ => schutte_column (schutte_column G (succOrd c) (k b)) c δ 0) _ _
                      (Hdiag b d0) (Hdmono b d0)
                      (normal_monotone _ HN1) (normal_complete _ HN1) Hs Hsc)).
Qed.

(** Ω satisfies the hypothesis with column 1 (the Veblen step). *)
Lemma QCol_Ω f (Hf : forall x y, x ≤ y -> f x ≤ f y) : QCol f bOmega 1.
Proof.
  intros β' G' Hβ' HR d ζ Hζ.
  assert (HG' : normal_function G') by apply HR.
  apply BRep_ext with (veblen G' ζ); auto.
  - apply bfam_bmono; auto. apply bfam_badd; auto using bfam_embed.
  - apply bach_veblen_step; auto. apply bfam_bmono; auto.
  - apply schutte_column_normal; auto using complete_1.
  - intros x Hx. symmetry. apply schutte_column_veblen; auto.
Qed.

(** Ω^(n+1), as iterated products, and its column n+1. *)
Fixpoint bOmegaPow (n:nat) : BOrd :=
  match n with
  | O => bOmega
  | S n' => bmul (bOmegaPow n') bOmega
  end.

Lemma bfam_bOmegaPow n : bfam (bOmegaPow n).
Proof.
  induction n; [ apply bfam_Ω | ].
  change (bfam (bmul (bOmegaPow n) bOmega)). apply bfam_bmul; auto using bfam_Ω.
Qed.

Theorem QCol_bOmegaPow f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall n, QCol f (bOmegaPow n) (natOrdSize (S n)).
Proof.
  induction n as [|n IH].
  - apply QCol_Ω; auto.
  - intros β' G' Hβ' HR d ζ Hζ.
    destruct d as [[[] _]|[]].
    change (BRep f (badd β' (bmul (bOmegaPow n) (embed ζ)))
                 (schutte_column G' (succOrd (natOrdSize (S n))) ζ)).
    apply bach_power_step; auto using natOrdSize_complete, bfam_bOmegaPow.
    + destruct n; simpl; [ intros [] | intros [[[] _]|[]] ].
    + destruct n; simpl; [ exact tt | exact (inr tt) ].
Qed.

(** β + Ω^(n+1)·ξ represents the Schütte column n+2 over the function
    represented by β. *)
Corollary bach_Ωpow_times_rep f (Hf : forall x y, x ≤ y -> f x ≤ f y) n β G :
  bfam β -> BRep f β G -> forall ξ, complete ξ ->
  BRep f (badd β (bmul (bOmegaPow n) (embed ξ))) (schutte_column G (natOrdSize (S (S n))) ξ).
Proof.
  intros Hβ HR ξ Hξ.
  apply (QCol_bOmegaPow f Hf (S n) β G Hβ HR (inr tt) ξ Hξ).
Qed.

(** ** The Small Veblen Ordinal *)

Lemma bsub_badd_zero_l1 y : bsub (badd bzero y) y.
Proof.
  induction y as [B g Hg D h Hh].
  apply bsub_intro.
  - intro s.
    destruct (badd_small_cases bzero (bnode B g D h) s) as [[[] _]|[b Hb]].
    rewrite Hb. exists b. apply Hg.
  - intro c.
    destruct (badd_big_cases bzero (bnode B g D h) c) as [[[] _]|[d Hd]].
    exists d. intro ξ. rewrite Hd. apply Hh.
Qed.

Lemma bsub_badd_zero_l2 y : bsub y (badd bzero y).
Proof.
  induction y as [B g Hg D h Hh].
  apply bsub_intro.
  - intro b.
    destruct (badd_small_r bzero (bnode B g D h) b) as [t Ht].
    exists t. rewrite Ht. apply Hg.
  - intro d.
    destruct (badd_big_r bzero (bnode B g D h) d) as [t Ht].
    exists t. intro ξ. rewrite Ht. apply Hh.
Qed.

Lemma bach_badd_zero_l f (Hf : forall x y, x ≤ y -> f x ≤ f y) y :
  bfam y -> forall z, bach f (badd bzero y) z ≈ bach f y z.
Proof.
  intro Hy.
  apply bach_bsub_eq; auto using bsub_badd_zero_l1, bsub_badd_zero_l2.
  apply bfam_badd; auto using bfam_bzero.
Qed.

(** Ω^ω, presented with one Ω-family per finite power: ζ ↦ ζ, and
    ζ ↦ Ω^(m+1)·ζ for each m. *)
Definition bSVO : BOrd :=
  bnode False (False_rect _) (option nat)
        (fun o ζ => match o with
                    | None => embed ζ
                    | Some m => bmul (bOmegaPow m) (embed ζ)
                    end).

Definition svo_col (o:option nat) : nat :=
  match o with
  | None => 1%nat
  | Some m => S (S m)
  end.

Lemma bfam_bSVO : bfam bSVO.
Proof.
  simpl. split; [ intros [] | split ].
  - intros [m|] ξ; simpl.
    + apply bfam_bmul; auto using bfam_bOmegaPow, bfam_embed.
    + apply bfam_embed.
  - intros [m|] ξ ξ' H; simpl.
    + apply bsub_bmul_r, bsub_embed; auto.
    + apply bsub_embed; auto.
Qed.

Theorem bach_SVO f (Hf : normal_function f) : bach f bSVO 0 ≈ schutte_column f ω 1 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HD : forall n, normal_function (fun δ => schutte_column f (natOrdSize n) δ 0)).
  { intro. apply schutte_column_normal_arg; auto using natOrdSize_complete. }
  assert (Hdiag : forall o x, complete x ->
             bach f (bbigSz bSVO o x) 0 ≈ schutte_column f (natOrdSize (svo_col o)) x 0).
  { intros [m|] x Hx.
    - change (bach f (bmul (bOmegaPow m) (embed x)) 0 ≈
              schutte_column f (natOrdSize (S (S m))) x 0).
      transitivity (bach f (badd bzero (bmul (bOmegaPow m) (embed x))) 0).
      + symmetry. apply bach_badd_zero_l; auto.
        apply bfam_bmul; auto using bfam_bOmegaPow, bfam_embed.
      + apply (bach_Ωpow_times_rep f Hfm m bzero f bfam_bzero (bach_zero_rep f Hf) x Hx).
        apply zero_complete.
    - change (bach f (embed x) 0 ≈ schutte_column f 1 x 0).
      transitivity (veblen f x 0); [ apply bach_embed; auto | ].
      symmetry. apply schutte_column_veblen; auto using zero_complete. }
  assert (Hdmono : forall o x y, x ≤ y -> bach f (bbigSz bSVO o x) 0 ≤ bach f (bbigSz bSVO o y) 0).
  { intros o x y H. apply bach_mono_index; auto.
    - apply (bfam_fam bSVO bfam_bSVO o x y H).
    - apply bfam_bmono; auto. apply bfam_big, bfam_bSVO. }
  assert (Harg0 : forall x, schutte_column f ω 0 x ≈ f x).
  { intro. apply schutte_column_arg0; auto. }
  assert (HN0 : normal_function (schutte_column f ω 0)).
  { apply schutte_column_normal; auto using omega_complete, zero_complete. }
  assert (Hcol : forall b δ, schutte_column (schutte_column f ω 0) b δ 0 ≈ schutte_column f b δ 0).
  { intros b δ. split.
    - apply schutte_column_monotone_func;
        [ apply normal_monotone; auto | exact Hfm | intro a; apply (proj1 (Harg0 a)) | reflexivity | reflexivity ].
    - apply schutte_column_monotone_func;
        [ exact Hfm | apply normal_monotone; auto | intro a; apply (proj2 (Harg0 a)) | reflexivity | reflexivity ]. }
  assert (HN1 : normal_function (schutte_column f ω 1)).
  { apply schutte_column_normal; auto using omega_complete, complete_1. }
  assert (Hs : limOrd (fun j:ordCarrier 0 => bach f bSVO (0 j)) ≈
               limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i))).
  { apply lim_eq_mor; intros []. }
  assert (Hsc : complete (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))).
  { apply lim_normal_complete; auto using zero_complete. }
  (* W n: the least fixpoint of column n's diagonal above the start *)
  assert (HW1 : forall o,
             fixOrd (fun ξ => bach f (bbigSz bSVO o ξ) 0) (limOrd (fun j:ordCarrier 0 => bach f bSVO (0 j)))
             ≈ fixOrd (fun δ => schutte_column f (natOrdSize (svo_col o)) δ 0)
                      (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))).
  { intro o. apply fixOrd_eq_func_complete; auto.
    - apply normal_monotone, HD.
    - apply normal_complete, HD. }
  assert (HWB : forall o,
             fixOrd (fun δ => schutte_column f (natOrdSize (svo_col o)) δ 0)
                    (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))
             ≤ bach f bSVO 0).
  { intro o. eapply ord_le_trans; [ apply (proj2 (HW1 o)) | ].
    apply (bach_comp_le f bSVO 0 (inr o)). }
  assert (HWle : forall n,
             fixOrd (fun δ => schutte_column f (natOrdSize n) δ 0)
                    (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))
             ≤ schutte_column f ω 1 0).
  { intro n.
    rewrite (schutte_column_unroll f ω 1 0).
    eapply ord_le_trans; [ | apply lub_le2 ].
    eapply ord_le_trans; [ | apply (sup_le _ _ n) ].
    eapply ord_le_trans; [ | apply (sup_le _ _ tt) ].
    apply (proj2 (fixOrd_eq_func _ _ _ _ (Hcol (natOrdSize n)) (normal_monotone _ (HD n))
                    (reflexivity _))). }
  (* the column-1 fixpoint dominates column 0 and f(1) *)
  assert (HW1c : complete (fixOrd (fun δ => schutte_column f 1 δ 0)
                                  (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i))))).
  { apply normal_fix_complete; auto.
    - apply normal_inflationary, (HD 1%nat).
    - apply normal_monotone, (HD 1%nat).
    - apply normal_complete, (HD 1%nat). }
  assert (HW1fix := normal_fixpoint _ (HD 1%nat) _ Hsc).
  simpl natOrdSize in HW1fix.
  assert (Hcol1 : forall z, complete z -> f z ≤ schutte_column f 1 z 0).
  { intros z Hz. transitivity (f (z + 0)).
    - apply Hfm, (proj2 (addOrd_zero_r z)).
    - apply schutte_column_le_f; auto. }
  split.
  - rewrite bach_unroll'.
    apply lub_least.
    { transitivity (f (1 + 0)); [ apply Hfm, zero_least | apply schutte_column_le_f; auto ]. }
    apply lub_least; apply sup_least; [ intros [] | intro o ].
    eapply ord_le_trans; [ apply (proj1 (HW1 o)) | apply HWle ].
  - rewrite (schutte_column_unroll f ω 1 0).
    apply lub_least.
    + eapply ord_le_trans; [ | apply (HWB None) ].
      change (f (1 + 0) ≤ fixOrd (fun δ => schutte_column f 1 δ 0)
                                 (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))).
      eapply ord_le_trans; [ | apply (proj2 HW1fix) ].
      eapply ord_le_trans; [ | apply Hcol1; auto ].
      apply Hfm.
      transitivity (1:Ord); [ apply (proj1 (addOrd_zero_r 1)) | ].
      apply succ_least.
      eapply ord_lt_le_trans; [ | apply (proj2 HW1fix) ].
      eapply ord_lt_le_trans; [ | apply Hcol1; auto ].
      apply normal_nonzero; auto.
    + apply sup_least; intro n. apply sup_least; intros [].
      eapply ord_le_trans;
        [ apply (proj1 (fixOrd_eq_func _ _ _ _ (Hcol (natOrdSize n)) (normal_monotone _ (HD n))
                          (reflexivity _))) | ].
      destruct n as [|[|m]].
      * eapply ord_le_trans; [ | apply (HWB None) ].
        apply fixOrd_least; [ apply normal_monotone, (HD 0%nat) | apply fixOrd_above | ].
        change (schutte_column f 0
                  (fixOrd (fun δ => schutte_column f 1 δ 0)
                          (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))) 0
                ≤ fixOrd (fun δ => schutte_column f 1 δ 0)
                         (limOrd (fun i:ordCarrier 0 => schutte_column f ω 1 (0 i)))).
        rewrite schutte_column0.
        eapply ord_le_trans; [ | apply (proj2 HW1fix) ].
        apply schutte_column_le_f; auto.
      * apply (HWB None).
      * apply (HWB (Some m)).
Qed.

Corollary bach_SVO_SmallVeblen : bach powOmega bSVO 0 ≈ SmallVeblenOrdinal.
Proof.
  exact (bach_SVO powOmega powOmega_normal).
Qed.

(** ** Arbitrary powers of Ω: the full Schütte column

We now treat all exponents uniformly.  @bPow ζ@ is Ω^ζ, defined by
recursion on the tree ζ: a node with the small child 0 and, for each
child ζ_i of ζ, the Ω-family ξ ↦ Ω^(ζ_i)·ξ.  The children of the
Schütte column 1+ζ are exactly 0 and the 1+ζ_i, matching these
components one for one, so β + Ω^ζ·ξ represents column 1+ζ over β,
for zero, successor and limit ζ alike.

Because the column may be a limit, we cannot use @schutte_column_succ@
and must absorb the base term G(ξ+y) of the general unrolling.  When
ξ has children this uses continuity of G over the directed family of
column-0 fixpoints, each of which lies above ξ. *)

Fixpoint bPow (ζ:Ord) : BOrd :=
  match ζ with
  | ord Z m => bnode unit (fun _ => bzero) Z (fun i ξ => bmul (bPow (m i)) (embed ξ))
  end.

Lemma bfam_bPow : forall ζ, bfam (bPow ζ).
Proof.
  induction ζ as [Z m Hm]; simpl.
  split; [ intros _; apply bfam_bzero | split ].
  - intros i ξ. apply bfam_bmul; auto using bfam_embed.
  - intros i ξ ξ' H. apply bsub_bmul_r, bsub_embed; auto.
Qed.

Lemma bcomp_shift_bmul_forall' f β Q X (k:X -> Ord) (P:(Ord -> Ord) -> Prop) :
  (forall g g', (forall x, g x = g' x) -> P g -> P g') ->
  (forall kk, P (bcomp f β kk)) ->
  (forall b kk, P (bcomp f (badd β (bmul Q (embed (k b)))) kk)) ->
  (forall b q, P (bach f (badd β (badd (bmul Q (embed (k b))) (bsmallSz Q q))))) ->
  (forall b d, P (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0)) ->
  forall kk, P (bcomp f (badd β (bmul Q (embed (ord X k)))) kk).
Proof.
  intros Pext H1 H2 H3 H4 [s|c].
  - destruct (badd_small_cases β (bmul Q (embed (ord X k))) s) as [[a Ha]|[mm Hm]].
    + apply (Pext (bcomp f β (inl a))); [ | apply H1 ].
      intro x.
      change (bach f (bsmallSz β a) x =
              bach f (bsmallSz (badd β (bmul Q (embed (ord X k)))) s) x).
      rewrite Ha. reflexivity.
    + destruct mm as [[b m']|[]].
      change (bsmallSz (badd β (bmul Q (embed (ord X k)))) s =
              badd β (bsmallSz (badd (bmul Q (embed (k b))) Q) m')) in Hm.
      destruct (badd_small_cases (bmul Q (embed (k b))) Q m') as [[a'' Ha'']|[q Hq]].
      * destruct (badd_small_r β (bmul Q (embed (k b))) a'') as [t Ht].
        apply (Pext (bcomp f (badd β (bmul Q (embed (k b)))) (inl t))); [ | apply H2 ].
        intro x.
        change (bach f (bsmallSz (badd β (bmul Q (embed (k b)))) t) x =
                bach f (bsmallSz (badd β (bmul Q (embed (ord X k)))) s) x).
        rewrite Ht, Hm, Ha''. reflexivity.
      * apply (Pext (bach f (badd β (badd (bmul Q (embed (k b))) (bsmallSz Q q))))); [ | apply H3 ].
        intro x.
        change (bach f (badd β (badd (bmul Q (embed (k b))) (bsmallSz Q q))) x =
                bach f (bsmallSz (badd β (bmul Q (embed (ord X k)))) s) x).
        rewrite Hm, Hq. reflexivity.
  - destruct (badd_big_cases β (bmul Q (embed (ord X k))) c) as [[c' Hc]|[mm Hm]].
    + apply (Pext (bcomp f β (inr c'))); [ | apply H1 ].
      intro x.
      change (bach f (bbigSz β c' x) 0 =
              bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
      rewrite Hc. reflexivity.
    + destruct mm as [[b m']|[]].
      assert (Hm' : forall ξ, bbigSz (badd β (bmul Q (embed (ord X k)))) c ξ =
                              badd β (bbigSz (badd (bmul Q (embed (k b))) Q) m' ξ))
        by exact Hm.
      destruct (badd_big_cases (bmul Q (embed (k b))) Q m') as [[e He]|[d Hd]].
      * destruct (badd_big_r β (bmul Q (embed (k b))) e) as [t Ht].
        apply (Pext (bcomp f (badd β (bmul Q (embed (k b)))) (inr t))); [ | apply H2 ].
        intro x.
        change (bach f (bbigSz (badd β (bmul Q (embed (k b)))) t x) 0 =
                bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
        rewrite Ht, Hm', He. reflexivity.
      * apply (Pext (fun ζ => bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d ζ))) 0));
          [ | apply H4 ].
        intro x.
        change (bach f (badd β (badd (bmul Q (embed (k b))) (bbigSz Q d x))) 0 =
                bach f (bbigSz (badd β (bmul Q (embed (ord X k)))) c x) 0).
        rewrite Hm', Hd. reflexivity.
Qed.

Lemma Scol_fix0' G (HG : normal_function G) C a ξ y :
  complete C -> 0 < C -> complete a -> complete ξ -> complete y -> a < ξ ->
  schutte_column G C a (schutte_column G C ξ y) ≤ schutte_column G C ξ y.
Proof.
  intros HC HC0 Ha Hξ Hy Haξ.
  transitivity (schutte_column (schutte_column G C a) 0 (schutte_column G C ξ y) 0).
  - rewrite schutte_column0.
    apply normal_monotone; [ apply schutte_column_normal; auto | ].
    apply addOrd_le1.
  - apply schutte_column_fixpoint; auto using zero_complete.
Qed.

Lemma Scol_value_cases' G (HG : normal_function G) C ξ y :
  complete C -> 0 < C -> complete ξ -> complete y ->
  schutte_column G C ξ y ≈ G y \/ schutte_column G C ξ y ≈ G (schutte_column G C ξ y).
Proof.
  intros HC HC0 Hξ Hy.
  assert (HGm : forall x y, x ≤ y -> G x ≤ G y) by (apply normal_monotone; auto).
  destruct ξ as [X k].
  assert (Hξ' := Hξ). destruct Hξ' as [_ [[[x0]|Hn] Hkc]].
  - right.
    assert (Hv : complete (schutte_column G C (ord X k) y)).
    { apply normal_complete; [ apply schutte_column_normal; auto | auto ]. }
    split.
    + apply normal_inflationary; auto.
    + transitivity (G (k x0 + schutte_column G C (ord X k) y)).
      { apply HGm. apply addOrd_le2. }
      transitivity (schutte_column G C (k x0) (schutte_column G C (ord X k) y)).
      { apply schutte_column_le_f; auto. }
      apply Scol_fix0'; auto. apply (index_lt (ord X k) x0).
  - left.
    assert (Hξy : ord X k + y ≈ y).
    { split; [ | apply addOrd_le2 ].
      transitivity (0 + y); [ | apply (proj1 (addOrd_zero_l y)) ].
      apply addOrd_monotone; [ | reflexivity ].
      rewrite ord_le_unfold. intro a. elim (Hn (inhabits a)). }
    split.
    + rewrite schutte_column_unroll.
      apply lub_least; [ apply HGm, (proj1 Hξy) | ].
      apply sup_least; intro b. apply sup_least; intro a. elim (Hn (inhabits a)).
    + transitivity (G (ord X k + y)); [ apply HGm, (proj2 Hξy) | ].
      apply schutte_column_le_f; auto.
Qed.

Theorem bach_bPow_rep f (Hf : forall x y, x ≤ y -> f x ≤ f y) :
  forall ζ, complete ζ -> forall β G, bfam β -> BRep f β G ->
  forall ξ, complete ξ -> BRep f (badd β (bmul (bPow ζ) (embed ξ))) (schutte_column G (1 + ζ) ξ).
Proof.
  induction ζ as [Z m Hm]; intros Hζ β G Hβ HR.
  assert (Hζ' := Hζ). destruct Hζ' as [_ [_ Hmc]].
  assert (HC : complete (1 + ord Z m)) by (apply onePlus_complete; auto).
  assert (HC0 : 0 < 1 + ord Z m) by apply onePlus_nonzero.
  assert (HR' := HR). destruct HR' as [HG [Hrep Hcl]].
  assert (HGm : forall x y, x ≤ y -> G x ≤ G y) by (apply normal_monotone; auto).
  assert (Hbm : bmono f β) by (apply bfam_bmono; auto).
  assert (HMfam : forall ξ, bfam (bmul (bPow (ord Z m)) (embed ξ))).
  { intro. apply bfam_bmul; auto using bfam_bPow, bfam_embed. }
  assert (HTfam : forall ξ, bfam (badd β (bmul (bPow (ord Z m)) (embed ξ)))).
  { intro. apply bfam_badd; auto. }
  assert (Hmono : forall ξ, bmono f (badd β (bmul (bPow (ord Z m)) (embed ξ)))).
  { intro. apply bfam_bmono; auto. }
  induction ξ as [X k Hk]; intro Hξ.
  assert (Hξ' := Hξ). destruct Hξ' as [Hdirξ [Hinhξ Hkc]].
  assert (HS : normal_function (schutte_column G (1 + ord Z m) (ord X k))).
  { apply schutte_column_normal; auto. }
  assert (HSk : forall b, normal_function (schutte_column G (1 + ord Z m) (k b))).
  { intro b. apply schutte_column_normal; auto. }
  assert (HIH : forall b, BRep f (badd β (bmul (bPow (ord Z m)) (embed (k b))))
                               (schutte_column G (1 + ord Z m) (k b))).
  { intro b. apply Hk; auto. }
  (* the small component 0 of Ω^ζ, shifted *)
  assert (Hsm : forall b x, complete x ->
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) bzero)) x ≈
             schutte_column (schutte_column G (1 + ord Z m) (k b)) 0 x 0).
  { intros b x Hx.
    transitivity (bach f (badd (badd β (bmul (bPow (ord Z m)) (embed (k b)))) bzero) x).
    { apply bach_badd_assoc; auto using bfam_bzero, bfam_bPow. }
    transitivity (bach f (badd β (bmul (bPow (ord Z m)) (embed (k b)))) x).
    { apply bach_badd_zero; auto. }
    transitivity (schutte_column G (1 + ord Z m) (k b) x); [ apply (HIH b); auto | ].
    rewrite schutte_column0.
    split; apply normal_monotone; auto.
    - apply (proj2 (addOrd_zero_r x)).
    - apply (proj1 (addOrd_zero_r x)). }
  assert (Hsm_mono : forall b x y, x ≤ y ->
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) bzero)) x ≤
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) bzero)) y).
  { intros b x y Hxy. apply bach_monotone; auto.
    apply bfam_bmono; auto. apply bfam_badd; auto. apply bfam_badd; auto using bfam_bzero. }
  (* the Ω-family components ξ' ↦ Ω^(ζ_i)·ξ', shifted *)
  assert (Hfm : forall b i x, complete x ->
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) (bmul (bPow (m i)) (embed x)))) 0 ≈
             schutte_column (schutte_column G (1 + ord Z m) (k b)) (1 + m i) x 0).
  { intros b i x Hx.
    transitivity (bach f (badd (badd β (bmul (bPow (ord Z m)) (embed (k b))))
                               (bmul (bPow (m i)) (embed x))) 0).
    { apply bach_badd_assoc; auto. apply bfam_bmul; auto using bfam_bPow, bfam_embed. }
    apply (Hm i (Hmc i) _ _ (HTfam (k b)) (HIH b) x Hx). apply zero_complete. }
  assert (Hfm_mono : forall b i x y, x ≤ y ->
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) (bmul (bPow (m i)) (embed x)))) 0 ≤
             bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) (bmul (bPow (m i)) (embed y)))) 0).
  { intros b i x y Hxy. apply bach_mono_index; auto.
    - apply bsub_badd_r, bsub_badd_r, bsub_bmul_r, bsub_embed; auto.
    - apply bfam_bmono; auto. apply bfam_badd; auto. apply bfam_badd; auto.
      apply bfam_bmul; auto using bfam_bPow, bfam_embed. }
  assert (Hcomp : forall kk y, complete y ->
             bcomp f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) kk
                   (schutte_column G (1 + ord Z m) (ord X k) y)
             ≤ schutte_column G (1 + ord Z m) (ord X k) y).
  { intros kk y Hy.
    assert (Hv : complete (schutte_column G (1 + ord Z m) (ord X k) y)) by (apply normal_complete; auto).
    apply (bcomp_shift_bmul_forall' f β (bPow (ord Z m)) X k
             (fun g => g (schutte_column G (1 + ord Z m) (ord X k) y)
                       ≤ schutte_column G (1 + ord Z m) (ord X k) y)).
    - intros g g' Hgg' H. rewrite <- Hgg'. exact H.
    - intro kk'.
      destruct (Scol_value_cases' G HG (1 + ord Z m) (ord X k) y HC HC0 Hξ Hy) as [H|H].
      + transitivity (bcomp f β kk' (G y)).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G y); [ apply Hcl; auto | apply (proj2 H) ].
      + transitivity (bcomp f β kk' (G (schutte_column G (1 + ord Z m) (ord X k) y))).
        { apply bmono_bcomp; auto. apply (proj1 H). }
        transitivity (G (schutte_column G (1 + ord Z m) (ord X k) y)); [ apply Hcl; auto | apply (proj2 H) ].
    - intros b kk'.
      transitivity (bcomp f (badd β (bmul (bPow (ord Z m)) (embed (k b)))) kk'
                          (schutte_column G (1 + ord Z m) (k b) (schutte_column G (1 + ord Z m) (ord X k) y))).
      { apply bmono_bcomp; auto. apply normal_inflationary; auto. }
      transitivity (schutte_column G (1 + ord Z m) (k b) (schutte_column G (1 + ord Z m) (ord X k) y)).
      { apply (HIH b); auto. }
      apply Scol_fix0'; auto. apply (index_lt (ord X k) b).
    - intros b [].
      change (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b))) bzero))
                   (schutte_column G (1 + ord Z m) (ord X k) y)
              ≤ schutte_column G (1 + ord Z m) (ord X k) y).
      transitivity (schutte_column (schutte_column G (1 + ord Z m) (k b)) 0
                                   (schutte_column G (1 + ord Z m) (ord X k) y) 0).
      + apply (proj1 (Hsm b _ Hv)).
      + apply schutte_column_fixpoint; auto using zero_complete.
        apply (index_lt (ord X k) b).
    - intros b d.
      change ((fun ζ' => bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k b)))
                                              (bmul (bPow (m d)) (embed ζ')))) 0)
                (schutte_column G (1 + ord Z m) (ord X k) y)
              ≤ schutte_column G (1 + ord Z m) (ord X k) y).
      transitivity (schutte_column (schutte_column G (1 + ord Z m) (k b)) (1 + m d)
                                   (schutte_column G (1 + ord Z m) (ord X k) y) 0).
      + apply (proj1 (Hfm b d _ Hv)).
      + apply schutte_column_fixpoint; auto using onePlus_complete.
        * apply (index_lt (1 + ord Z m) (inr (existT _ d tt))).
        * apply (index_lt (ord X k) b). }
  split; [ exact HS | split; [ | exact Hcomp ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  assert (Hs : limOrd (fun j => bach f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (ord Y h j)) ≈
               limOrd (fun j => schutte_column G (1 + ord Z m) (ord X k) (ord Y h j))).
  { apply lim_eq_mor; intro j; apply Hy; auto. }
  assert (Hsc : complete (limOrd (fun j => schutte_column G (1 + ord Z m) (ord X k) (ord Y h j)))).
  { apply lim_normal_complete; auto. }
  (* the column-0 terms are below φ_T(y) *)
  assert (Hcol0 : forall a,
             fixOrd (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 δ 0)
                    (limOrd (fun j => schutte_column G (1 + ord Z m) (ord X k) (ord Y h j)))
             ≤ bach f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (ord Y h)).
  { intro a.
    assert (HN0 : normal_function (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 δ 0)).
    { apply schutte_column_normal_arg; auto using zero_complete. }
    destruct (badd_small_r (bmul (bPow (ord Z m)) (embed (k a))) (bPow (ord Z m)) tt) as [cc Hcc].
    destruct (badd_small_r β (bmul (bPow (ord Z m)) (embed (ord X k))) (inl (existT _ a cc))) as [t Ht].
    eapply ord_le_trans;
      [ | apply (bach_comp_le f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (ord Y h) (inl t)) ].
    assert (Heq : forall x,
               bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a))) bzero)) x =
               bcomp f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (inl t) x).
    { intro x.
      change (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a))) bzero)) x =
              bach f (bsmallSz (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) t) x).
      rewrite Ht.
      change (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a))) bzero)) x =
              bach f (badd β (bsmallSz (badd (bmul (bPow (ord Z m)) (embed (k a))) (bPow (ord Z m))) cc)) x).
      rewrite Hcc. reflexivity. }
    eapply ord_le_trans; [ | apply (proj1 (fixOrd_ext_eq _ _ _ Heq)) ].
    apply (proj2 (fixOrd_eq_func_complete
                    (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a))) bzero)))
                    (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 δ 0) _ _
                    (Hsm a) (Hsm_mono a)
                    (normal_monotone _ HN0) (normal_complete _ HN0) Hs Hsc)). }
  split.
  - apply bach_le_comp.
    + transitivity (G (ord Y h)).
      { transitivity (bach f β (ord Y h)); [ apply f_le_bach | apply (proj1 (Hrep _ Hyc)) ]. }
      transitivity (G (ord X k + ord Y h)); [ apply HGm, addOrd_le2 | ].
      apply schutte_column_le_f; auto.
    + intro kk.
      apply fixOrd_least; [ apply (bmono_bcomp f Hf _ (Hmono _)) | | apply Hcomp; auto ].
      eapply ord_le_trans; [ apply (proj1 Hs) | ].
      apply limit_least; intro j.
      apply normal_increasing; auto.
      apply (index_lt (ord Y h) j).
  - rewrite (schutte_column_unroll G (1 + ord Z m) (ord X k) (ord Y h)).
    apply lub_least.
    + (* the base term G(ξ+y) *)
      destruct Hinhξ as [[x0]|Hn].
      * set (W := fun a => fixOrd (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 δ 0)
                                  (limOrd (fun j => schutte_column G (1 + ord Z m) (ord X k) (ord Y h j)))).
        assert (HN0 : forall a, normal_function
                         (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 δ 0)).
        { intro a. apply schutte_column_normal_arg; auto using zero_complete. }
        assert (HWc : forall a, complete (W a)).
        { intro a. unfold W. apply normal_fix_complete; auto.
          - apply normal_inflationary, HN0.
          - apply normal_monotone, HN0.
          - apply normal_complete, HN0. }
        assert (HWbig : forall a, G (k a + W a) ≤ W a).
        { intro a.
          transitivity (G (k a + (W a + 0))).
          { apply HGm, addOrd_monotone; [ reflexivity | apply (proj2 (addOrd_zero_r _)) ]. }
          transitivity (schutte_column G (1 + ord Z m) (k a) (W a + 0)).
          { apply schutte_column_le_f; auto. }
          transitivity (schutte_column (schutte_column G (1 + ord Z m) (k a)) 0 (W a) 0).
          { apply (proj2 (schutte_column0 _ _ _)). }
          unfold W. apply (proj2 (normal_fixpoint _ (HN0 a) _ Hsc)). }
        assert (HWpos : forall a, 0 < W a).
        { intro a. eapply ord_lt_le_trans; [ | apply HWbig ]. apply normal_nonzero; auto. }
        assert (HkW : forall a, k a < W a).
        { intro a.
          eapply ord_le_lt_trans; [ apply (proj2 (addOrd_zero_r (k a))) | ].
          eapply ord_lt_le_trans; [ apply addOrd_increasing, HWpos | ].
          eapply ord_le_trans; [ | apply HWbig ].
          apply normal_inflationary; auto. apply addOrd_complete; auto. }
        assert (HGW : forall a, G (W a) ≤ W a).
        { intro a. eapply ord_le_trans; [ | apply HWbig ]. apply HGm, addOrd_le2. }
        assert (HWdir : directed X W).
        { intros a1 a2. destruct (Hdirξ a1 a2) as [a' [H1 H2]].
          exists a'.
          assert (HWmono : forall a, k a ≤ k a' -> W a ≤ W a').
          { intros a Ha. unfold W.
            apply fixOrd_monotone_func; [ | apply normal_monotone, HN0 ].
            intro δ. apply schutte_column_monotone_func; auto.
            - apply normal_monotone, HSk.
            - apply normal_monotone, HSk.
            - intro x. apply schutte_column_monotone; auto. reflexivity.
            - reflexivity.
            - reflexivity. }
          split; apply HWmono; auto. }
        assert (HξyZ : ord X k + ord Y h ≤ supOrd W).
        { rewrite addOrd_unfold. apply lub_least.
          - rewrite ord_le_unfold. intro a.
            eapply ord_lt_le_trans; [ apply HkW | apply (sup_le _ W a) ].
          - apply sup_least; intro j. apply succ_least.
            eapply ord_le_lt_trans; [ apply normal_inflationary; [ exact HG | apply addOrd_complete; auto ] | ].
            eapply ord_le_lt_trans;
              [ apply (schutte_column_le_f (1 + ord Z m) (ord X k) (ord Y h j) G HGm) | ].
            eapply ord_lt_le_trans; [ | apply (sup_le _ W x0) ].
            eapply ord_lt_le_trans; [ | apply fixOrd_above ].
            rewrite ord_lt_unfold. exists j. reflexivity. }
        transitivity (G (supOrd W)); [ apply HGm; auto | ].
        transitivity (supOrd W).
        { eapply ord_le_trans; [ apply (normal_continuous G HG X W x0 HWdir HWc) | ].
          apply sup_ord_le_morphism. intro a. apply HGW. }
        apply sup_least; intro a. apply Hcol0.
      * assert (Hξy : ord X k + ord Y h ≤ ord Y h).
        { transitivity (0 + ord Y h); [ | apply (proj1 (addOrd_zero_l _)) ].
          apply addOrd_monotone; [ | reflexivity ].
          rewrite ord_le_unfold. intro a. elim (Hn (inhabits a)). }
        transitivity (G (ord Y h)); [ apply HGm; auto | ].
        transitivity (bach f β (ord Y h)); [ apply (proj2 (Hrep _ Hyc)) | ].
        apply bach_mono_index; auto.
        rewrite (badd_eq β (bmul (bPow (ord Z m)) (embed (ord X k)))). apply bsub_blub_l.
    + apply sup_least; intros [[]|[d []]]; apply sup_least; intro a.
      * apply Hcol0.
      * assert (HNd : normal_function
                        (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) (1 + m d) δ 0)).
        { apply schutte_column_normal_arg; auto using onePlus_complete. }
        destruct (badd_big_r (bmul (bPow (ord Z m)) (embed (k a))) (bPow (ord Z m)) d) as [cc Hcc].
        destruct (badd_big_r β (bmul (bPow (ord Z m)) (embed (ord X k))) (inl (existT _ a cc))) as [t Ht].
        eapply ord_le_trans;
          [ | apply (bach_comp_le f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (ord Y h) (inr t)) ].
        assert (Heq : forall x,
                   (fun ζ' => bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a)))
                                                    (bmul (bPow (m d)) (embed ζ')))) 0) x =
                   bcomp f (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) (inr t) x).
        { intro x.
          change (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a)))
                                       (bmul (bPow (m d)) (embed x)))) 0 =
                  bach f (bbigSz (badd β (bmul (bPow (ord Z m)) (embed (ord X k)))) t x) 0).
          rewrite (Ht x).
          change (bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a)))
                                       (bmul (bPow (m d)) (embed x)))) 0 =
                  bach f (badd β (bbigSz (badd (bmul (bPow (ord Z m)) (embed (k a))) (bPow (ord Z m))) cc x)) 0).
          rewrite (Hcc x). reflexivity. }
        eapply ord_le_trans; [ | apply (proj1 (fixOrd_ext_eq _ _ _ Heq)) ].
        apply (proj2 (fixOrd_eq_func_complete
                        (fun ζ' => bach f (badd β (badd (bmul (bPow (ord Z m)) (embed (k a)))
                                                       (bmul (bPow (m d)) (embed ζ')))) 0)
                        (fun δ => schutte_column (schutte_column G (1 + ord Z m) (k a)) (1 + m d) δ 0) _ _
                        (Hfm a d) (Hfm_mono a d)
                        (normal_monotone _ HNd) (normal_complete _ HNd) Hs Hsc)).
Qed.

(** ** The Large Veblen Ordinal *)

Lemma bsub_bPow : forall ζ ζ', ζ ≤ ζ' -> bsub (bPow ζ) (bPow ζ').
Proof.
  induction ζ as [Z m Hm]; intros [Z' m'] H; simpl.
  split.
  - intros _. exists tt. exact (bsub_refl bzero).
  - intro i. destruct (ord_le_subord _ _ H i) as [j Hj].
    exists j. intro ξ. apply bsub_bmul_l. apply Hm. exact Hj.
Qed.

(** Ω^Ω, as the Ω-limit of ζ ↦ Ω^ζ·1. *)
Definition bLVO : BOrd := blimΩ (fun ζ => bmul (bPow ζ) (embed 1)).

Theorem bach_LVO f (Hf : normal_function f) :
  bach f bLVO 0 ≈ fixOrd (fun β => schutte_column f β 1 0) 0.
Proof.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HF : normal_function (fun β => schutte_column f β 1 0)) by (apply schutte_column_normalβ; auto).
  assert (HD : forall ζ, complete ζ ->
             bach f (bmul (bPow ζ) (embed 1)) 0 ≈ schutte_column f (1 + ζ) 1 0).
  { intros ζ Hζ.
    transitivity (bach f (badd bzero (bmul (bPow ζ) (embed 1))) 0).
    - symmetry. apply bach_badd_zero_l; auto.
      apply bfam_bmul; auto using bfam_bPow, bfam_embed.
    - apply (bach_bPow_rep f Hfm ζ Hζ bzero f bfam_bzero (bach_zero_rep f Hf) 1 complete_1).
      apply zero_complete. }
  assert (HDmono : forall x y, x ≤ y ->
             bach f (bmul (bPow x) (embed 1)) 0 ≤ bach f (bmul (bPow y) (embed 1)) 0).
  { intros x y Hxy. apply bach_mono_index; auto.
    - apply bsub_bmul_l, bsub_bPow; auto.
    - apply bfam_bmono; auto. apply bfam_bmul; auto using bfam_bPow, bfam_embed. }
  assert (HD'mono : forall x y, x ≤ y -> schutte_column f (1 + x) 1 0 ≤ schutte_column f (1 + y) 1 0).
  { intros x y Hxy. apply schutte_column_monotoneβ; auto.
    apply addOrd_monotone; auto. reflexivity. }
  assert (HD'c : forall x, complete x -> complete (schutte_column f (1 + x) 1 0)).
  { intros x Hx. apply normal_complete; auto using zero_complete.
    apply schutte_column_normal; auto using onePlus_complete, complete_1. }
  assert (Hs0 : limOrd (fun j:ordCarrier 0 => bach f bLVO (0 j)) ≈ 0).
  { split; [ apply limit_least; intros [] | apply zero_least ]. }
  assert (Z1 : fixOrd (fun ζ => bach f (bmul (bPow ζ) (embed 1)) 0) (limOrd (fun j:ordCarrier 0 => bach f bLVO (0 j)))
               ≈ fixOrd (fun ζ => schutte_column f (1 + ζ) 1 0) 0).
  { apply fixOrd_eq_func_complete; auto using zero_complete. }
  assert (HLc : complete (fixOrd (fun β => schutte_column f β 1 0) 0)).
  { apply normal_fix_complete; auto using zero_complete.
    - apply normal_inflationary; auto.
    - apply normal_monotone; auto.
    - apply normal_complete; auto. }
  assert (HLfix := normal_fixpoint _ HF 0 zero_complete).
  assert (Z2 : fixOrd (fun ζ => schutte_column f (1 + ζ) 1 0) 0 ≈ fixOrd (fun β => schutte_column f β 1 0) 0).
  { split.
    - apply fixOrd_least; auto using zero_least.
      transitivity (schutte_column f (fixOrd (fun β => schutte_column f β 1 0) 0) 1 0).
      + apply schutte_column_monotoneβ; auto.
        transitivity (schutte_column f (fixOrd (fun β => schutte_column f β 1 0) 0) 1 0).
        * apply (onePlus_least_normal (fun β => schutte_column f β 1 0)); auto.
        * apply (proj2 HLfix).
      + apply (proj2 HLfix).
    - apply fixOrd_monotone_func; auto.
      intro x. apply schutte_column_monotoneβ; auto. apply addOrd_le2. }
  split.
  - rewrite bach_unroll'.
    apply lub_least.
    + transitivity (schutte_column f (fixOrd (fun β => schutte_column f β 1 0) 0) 1 0);
        [ | apply (proj2 HLfix) ].
      transitivity (f (1 + 0)); [ apply Hfm, zero_least | apply schutte_column_le_f; auto ].
    + apply lub_least; apply sup_least; intros [].
      eapply ord_le_trans; [ apply (proj1 Z1) | apply (proj1 Z2) ].
  - eapply ord_le_trans; [ apply (proj2 Z2) | ].
    eapply ord_le_trans; [ apply (proj2 Z1) | ].
    apply (bach_comp_le f bLVO 0 (inr tt)).
Qed.

Corollary bach_LVO_LargeVeblen : bach powOmega bLVO 0 ≈ LargeVeblenOrdinal.
Proof.
  exact (bach_LVO powOmega powOmega_normal).
Qed.
