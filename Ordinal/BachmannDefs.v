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

** Layout of the development

 - @BachmannDefs.v@: the trees, @bach@, the order @bsub@, the
   arithmetic, and the general step theorems (this file).
 - @BachmannAssoc.v@: associativity of addition up to φ, and the
   invariant @bfam@.
 - @BachmannPower.v@: Ω^ζ·ξ for arbitrary ζ as Schütte columns; the
   canonical trees.
 - @BachmannCalibration.v@: φ against known hierarchies: Γ₀, Ackermann,
   the Small and Large Veblen Ordinals.
 - @BachmannNormal.v@: φ is normal, proved directly, up to the
   Bachmann–Howard ordinal.
 - @BachmannFacts.v@: semantic facts used by the notation system.
 - @Notation/Bachmann*.v@: the notation system (see
   @Notation/BachmannNotation.v@).
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


(** ** Inversion and monotonicity of @bsub@ for the constructions *)

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

(** ** Small constants *)

Definition S2 (f:Ord -> Ord) (ξ:Ord) : Ord -> Ord := schutte_column f (succOrd 1) ξ.

Lemma complete_1 : complete 1.
Proof. apply succ_complete, zero_complete. Qed.

Lemma complete_2 : complete (succOrd 1).
Proof. apply succ_complete, complete_1. Qed.

