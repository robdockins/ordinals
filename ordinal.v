Require Import List.
Require Import Relations.
Require Import Wf.
Require Import Wellfounded.Transitive_Closure.

Import ListNotations.
Open Scope list.

(** Ordinals, represented as Type-indexed trees
    of potentially infinite width, but finite depth.
 *)

Inductive Ord : Type :=
| ord : forall (A:Type), (A -> Ord) -> Ord.


(** We define less-than and less-equal essentially by mutual
  * recursion on the structure of ordinals.
  *)
Fixpoint ord_lt (x y:Ord) {struct x}: Prop :=
  match x, y with
  | ord A f, ord B g =>
    exists b:B, forall a:A, ord_lt (f a) (g b)
  end.

Definition ord_le (x y:Ord) : Prop :=
  match x with
  | ord A f => forall a:A, ord_lt (f a) y
  end.

(** Characteristic equation for less-than *)
Lemma ord_lt_unfold x y :
  ord_lt x y =
  match y with
  | ord B g => exists b:B, ord_le x (g b)
  end.
Proof.
  destruct x; destruct y; simpl; auto.
Qed.

(** Characteristic equation for less-equal *)
Lemma ord_le_unfold x y :
  ord_le x y =
  match x with
  | ord A f => forall a:A, ord_lt (f a) y
  end.
Proof.
  reflexivity.
Qed.

Global Opaque ord_le ord_lt.

(** Less-than implies less-equal
  *)
Lemma ord_lt_le : forall b a,
  ord_lt a b -> ord_le a b.
Proof.
  induction b. intros.
  rewrite ord_lt_unfold in H0.
  destruct H0 as [b ?].
  destruct a.
  rewrite ord_le_unfold in *.
  intros.
  specialize (H0 a).
  rewrite ord_lt_unfold.
  exists b. apply H. auto.
Qed.

(** Less-equal is a reflexive relation
  *)
Lemma ord_le_refl x : ord_le x x.
Proof.
  induction x.
  rewrite ord_le_unfold.
  intros.
  rewrite ord_lt_unfold.
  exists a. apply H.
Qed.

(** These various transitivity-releated facts need to
    be proved simultaneuously.
  *)
Lemma ord_trans :
  forall b a c,
    (ord_le a b -> ord_le b c -> ord_le a c) /\
    (ord_le a b -> ord_lt b c -> ord_lt a c) /\
    (ord_lt a b -> ord_le b c -> ord_lt a c).
Proof.
  induction b.
  intros.
  repeat split.
  - intros.
    rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    destruct a. intros.
    specialize (H0 a).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 b).
    specialize (H b (o0 a) c); intuition.
  - intros.
    rewrite ord_lt_unfold.
    rewrite ord_lt_unfold in H1.
    destruct c. destruct H1 as [b ?].
    exists b.
    rewrite ord_le_unfold in H1.
    rewrite ord_le_unfold.
    rewrite ord_le_unfold in H0.
    destruct a.
    intros a.
    specialize (H0 a).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [c ?].
    specialize (H1 c).
    specialize (H c (o1 a) (o0 b)); intuition.
  - intros.
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?].
    rewrite ord_le_unfold in H1.
    specialize (H1 b).
    destruct (H b a c); intuition.
Qed.

(** Less-equal is transitive.
  *)
Lemma ord_le_trans a b c :
    ord_le a b -> ord_le b c -> ord_le a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** Less-than is transitive *)
Lemma ord_lt_trans a b c :
    ord_lt a b -> ord_lt b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
  apply H2.
  apply ord_lt_le; auto.
Qed.

(** Less-equal preserves less-than *)
Lemma ord_lt_le_trans a b c :
  ord_lt a b -> ord_le b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

Lemma ord_le_lt_trans a b c :
  ord_le a b -> ord_lt b c -> ord_lt a c.
Proof.
  intros. destruct (ord_trans b a c); intuition.
Qed.

(** The less-than ordering on ordinals is well-founded.
  *)
Lemma ord_lt_acc : forall x y,  ord_le y x -> Acc ord_lt y.
Proof.
  induction x; intros.
  rename y into z.
  constructor. intro y.
  intros ?.
  assert (ord_lt y (ord A o)).
  { apply ord_lt_le_trans with z; auto. }

  destruct y.
  rewrite ord_lt_unfold in H2.
  destruct H2 as [b ?].
  apply (H b).
  auto.
Qed.

Lemma ord_lt_wf : well_founded ord_lt.
Proof.
  red; intros.
  apply ord_lt_acc with a.
  apply ord_le_refl.
Qed.

(*   The less-than order is irreflexive, a simple corollary of well-foundedness.
 *)
Corollary ord_lt_irreflexive : forall x, ord_lt x x -> False.
Proof.
  induction x using (well_founded_induction ord_lt_wf).
  firstorder.
Qed.

(** Ordinal operators *)
Definition zeroOrd : Ord := ord False (False_rect _).
Definition succOrd (x:Ord) : Ord := ord unit (fun _ => x).
Definition lubOrd (x y:Ord) : Ord :=
  match x, y with
  | ord A f, ord B g =>
    ord (A+B) (sum_rect _ f g)
  end.
Definition limOrd {A:Type} (f:A -> Ord) := ord A f.

(** Zero is the least ordinal.
  *)
Lemma zero_least : forall o, ord_le zeroOrd o.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. intros. elim a.
Qed.

(** Succ is a monotote operator with respetct to both lt and le, and
  * which is strictly above its argument.
  * Moreover, it is the smallest ordinal which is strictly above its
  * argument.
  *)
Lemma succ_monotone : forall a b, ord_lt a b -> ord_lt (succOrd a) (succOrd b).
Proof.
  intros.
  rewrite ord_lt_unfold. simpl.
  exists tt.
  rewrite ord_le_unfold. simpl.
  auto.
Qed.

Lemma succ_monotone' : forall a b, ord_le a b -> ord_le (succOrd a) (succOrd b).
Proof.
  intros.
  rewrite ord_le_unfold. simpl.
  intro.
  rewrite ord_lt_unfold. simpl.
  exists tt.
  auto.
Qed.

Lemma succ_lt : forall o, ord_lt o (succOrd o).
Proof.
  intros. rewrite ord_lt_unfold. simpl.
  exists tt. apply ord_le_refl.
Qed.

Lemma succ_least : forall x y, ord_lt x y -> ord_le (succOrd x) y.
Proof.
  intros.
  rewrite ord_le_unfold. simpl; auto.
Qed.

(** lub is the least upper bound of its arguments.
  *)
Lemma lub_le1 : forall x y, ord_le x (lubOrd x y).
Proof.
  intros. rewrite ord_le_unfold.
  destruct x; destruct y; simpl.
  intros.
  rewrite ord_lt_unfold.
  exists (inl a). simpl.
  apply ord_le_refl.
Qed.

Lemma lub_le2 : forall x y, ord_le y (lubOrd x y).
Proof.
  intros. rewrite ord_le_unfold.
  destruct x; destruct y; simpl.
  intros.
  rewrite ord_lt_unfold.
  exists (inr a). simpl.
  apply ord_le_refl.
Qed.

Lemma lub_least x y z :
  ord_le x z -> ord_le y z -> ord_le (lubOrd x y) z.
Proof.
  repeat rewrite ord_le_unfold.
  destruct x; destruct y; simpl; intros.
  rewrite ord_lt_unfold.
  destruct z; simpl.
  destruct a.
  - specialize (H a).
    rewrite ord_lt_unfold in H.
    destruct H as [b ?]. exists b.
    simpl. auto.
  - specialize (H0 a).
    rewrite ord_lt_unfold in H0.
    destruct H0 as [b ?].
    exists b. simpl. auto.
Qed.

(** lubOrd is a commutative, associative operator
  *)
Lemma lub_le_comm : forall x y, ord_le (lubOrd x y) (lubOrd y x).
Proof.
  intros.
  apply lub_least.
  apply lub_le2.
  apply lub_le1.
Qed.

Lemma lub_le_trans1 : forall x y z,
    ord_le (lubOrd x (lubOrd y z)) (lubOrd (lubOrd x y) z).
Proof.
  intros.
  apply lub_least.
  apply ord_le_trans with (lubOrd x y).
  apply lub_le1.
  apply lub_le1.
  apply lub_least.
  apply ord_le_trans with (lubOrd x y).
  apply lub_le2.
  apply lub_le1.
  apply lub_le2.
Qed.

Lemma sum_le_trans2 : forall x y z,
    ord_le (lubOrd (lubOrd x y) z) (lubOrd x (lubOrd y z)).
Proof.
  intros.
  apply lub_least.
  apply lub_least.
  apply lub_le1.
  apply ord_le_trans with (lubOrd y z).
  apply lub_le1.
  apply lub_le2.
  apply ord_le_trans with (lubOrd y z).
  apply lub_le2.
  apply lub_le2.
Qed.

Lemma lubOrd_monotone a b c d :
  ord_le a c -> ord_le b d -> ord_le (lubOrd a b) (lubOrd c d).
Proof.
  intros.
  apply lub_least.
  apply ord_le_trans with c; auto.
  apply lub_le1.
  apply ord_le_trans with d; auto.
  apply lub_le2.
Qed.

(**  The lub of successors is less-or-equal to the successor of the lub.
  *)
Lemma succ_lub x y :
 ord_le (lubOrd (succOrd x) (succOrd y)) (succOrd (lubOrd x y)).
Proof.
  apply lub_least.
  apply succ_monotone'.
  apply lub_le1.
  apply succ_monotone'.
  apply lub_le2.
Qed.

(** The limit ordinal is strictly above all the ordinals in
  * the collection defined by "f".  Moreover it is the smallest
  * such.
  *)
Lemma limit_lt : forall A (f:A -> Ord) i, ord_lt (f i) (limOrd f).
Proof.
  intros. rewrite ord_lt_unfold. simpl.
  exists i. apply ord_le_refl.
Qed.

Lemma limit_least : forall A (f:A -> Ord) z,
  (forall i, ord_lt (f i) z) -> ord_le (limOrd f) z.
Proof.
  intros. rewrite ord_le_unfold.
  simpl. auto.
Qed.

(** A structure of types together with ordinal measures.
  *)
Record OrdSize : Type :=
  MkOrdSize
    { ordCarrier :> Type
    ; ordSize : ordCarrier -> Ord
    }.

(*  The notation "x ◃ y" indicates that "x" has a strictly smaller ordinal measure
    than "y".  Note that "x" and "y" do not need to have the same type.
 *)
Notation "x ◃ y" := (ord_lt (ordSize _ x) (ordSize _ y)) (at level 80, no associativity).


Lemma subterm_trans : forall {A B C:OrdSize} (x:A) (y:B) (z:C),
  x ◃ y -> y ◃ z -> x ◃ z.
Proof.
  simpl; intros. eapply ord_lt_trans; eauto.
Qed.

Lemma size_discriminate : forall (A:OrdSize) (x y:A), x ◃ y -> x <> y.
Proof.
  repeat intro; subst y.
  apply (ord_lt_irreflexive _ H).
Qed.


Lemma succ_trans x y : ord_le x y -> ord_lt x (succOrd y).
Proof.
  intros.
  rewrite ord_lt_unfold.
  simpl. exists tt.
  auto.
Qed.

Lemma succ_trans' x y : ord_le x y -> ord_le x (succOrd y).
Proof.
  intros.
  apply ord_lt_le.
  apply succ_trans.
  auto.
Qed.

Lemma lub_trans1 x y z : ord_le x y -> ord_le x (lubOrd y z).
Proof.
  intros.
  apply ord_le_trans with y; auto.
  apply lub_le1.
Qed.

Lemma lub_trans2 x y z : ord_le x z -> ord_le x (lubOrd y z).
Proof.
  intros.
  apply ord_le_trans with z; auto.
  apply lub_le2.
Qed.

Hint Unfold ordSize : ord.
Hint Resolve
     limit_lt lub_le1 lub_le2
     ord_lt_trans ord_le_trans
     succ_trans
     succ_trans'
     lub_trans1 lub_trans2
     ord_lt_le ord_le_refl : ord.

(* Natural numbers have an ordinal size.
 *)
Fixpoint natOrdSize (x:nat) :=
  match x with
  | O => zeroOrd
  | S n => succOrd (natOrdSize n)
  end.

Canonical Structure NatOrdSize : OrdSize
  := MkOrdSize nat natOrdSize.


(* Lists of ordinal-sized types have an ordinal size.
 *)
Definition listOrd {A} (f:A -> Ord) : list A -> Ord :=
  fix listOrd (l:list A) : Ord :=
  match l with
  | [] => zeroOrd
  | x::xs => succOrd (lubOrd (f x) (listOrd xs))
  end.

Canonical Structure ListOrdSize (A:OrdSize) : OrdSize :=
    MkOrdSize (list A) (listOrd (ordSize A)).

(** Basic lemmas about constructors for nat and list *)
Lemma S_lt : forall x:nat, x ◃ S x.
Proof.
  simpl; auto with ord.
Qed.

Lemma head_lt : forall (A:OrdSize) (h:A) (t:list A), h ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Lemma tail_lt : forall (A:OrdSize) (h:A) (t:list A), t ◃ (h::t).
Proof.
  simpl; eauto with ord.
Qed.

Hint Resolve head_lt tail_lt : ord.

Lemma In_lt : forall (A:OrdSize) (x:A) l, In x l -> x ◃ l.
Proof.
  induction l; simpl; intuition; subst; eauto with ord.
Qed.
Hint Resolve In_lt.


(** Functions into sized types have sizes defined by nontrivial
    limit ordinals.
*)
Definition funOrd {A B:Type} (sz:B -> Ord) (f:A -> B) : Ord :=
  limOrd (fun x => sz (f x)).

Definition depOrd {A:Type} {B:A -> Type} (sz : forall a:A, B a -> Ord) (f:forall a:A, B a) : Ord :=
  limOrd (fun x => sz x (f x)).

Canonical Structure FunOrdSize (A:Type) (B:OrdSize) :=
  MkOrdSize (A -> B) (@funOrd A B (ordSize B)).

Canonical Structure DepOrdSize (A:Type) (B:A -> OrdSize) :=
  MkOrdSize (forall a:A, B a) (@depOrd A B (fun x => ordSize (B x))).

(** Functions have larger ordinal size than each of their points.
 *)
Lemma fun_lt : forall A (B:OrdSize) (f:A -> B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold funOrd.
  apply (limit_lt _ (fun x => ordSize B (f x))).
Qed.

Lemma dep_lt : forall (A:Type) (B:A->OrdSize) (f:DepOrdSize A B) i, f i ◃ f.
Proof.
  simpl; intros.
  unfold depOrd.
  apply (limit_lt _ (fun x => ordSize (B x) (f x))).
Qed.

Hint Resolve fun_lt dep_lt.

(** Let's play around with some Ltac support.

    This Ltac code is currently super first-pass, and could probably
    be improved a lot.
  *)
Ltac try_ord := try solve [ auto with ord | simpl; auto 100 with ord | simpl; eauto with ord ].

Ltac subterm_trans x :=
  apply subterm_trans with x; try_ord.

Ltac esubterm_trans :=
  eapply subterm_trans; try_ord.

Ltac ord_crush :=
  intros; apply size_discriminate;
  try_ord;
  repeat (progress esubterm_trans).

(** Some simple examples based on nats and lists *)

Goal forall x:nat, x <> S (S (S (S x))).
Proof.
  ord_crush.
Qed.

Goal forall (a b c:nat) x, x <> a::b::c::x.
Proof.
  ord_crush.
Qed.


(** An example based on even/odd numbers *)

Inductive even :=
| even0 : even
| evenS : odd -> even
with odd :=
| oddS : even -> odd.

(* Some fairly boilerplate code defining the ordinal size function,
   and registering associated canconical structures.
 *)
Fixpoint even_size (x:even) : Ord :=
  match x with
  | even0 => zeroOrd
  | evenS y => succOrd (odd_size y)
  end
with
odd_size (x:odd) : Ord :=
  match x with
  | oddS y => succOrd (even_size y)
  end.

Canonical Structure evenOrdSize :=
  MkOrdSize even even_size.
Canonical Structure oddOrdSize :=
  MkOrdSize odd odd_size.

(* Now we can crush that proof *)
Lemma even_odd_neq : forall x, x <> oddS (evenS (oddS (evenS x))).
Proof.
  ord_crush.
Qed.


(** Countably-wide rose trees *)

Inductive tree :=
| leaf : tree
| node : (nat -> tree) -> tree.

Fixpoint tree_size (t:tree) : Ord :=
  match t with
  | leaf => zeroOrd
  | node f => funOrd tree_size f
  end.

Canonical Structure treeOrdSize :=
  MkOrdSize tree tree_size.

(* Not entirely sure how to automate this proof better... *)
Goal forall x f g n m ,
    g m = x ->
    f n = node g ->
    x <> node f.
Proof.
  intros. apply size_discriminate.
  apply subterm_trans with (f n).
  rewrite H0.
  rewrite <- H.
  apply fun_lt.
  apply fun_lt.
Qed.

(** A more complicated example using mutual recursion,
    nested lists and dependent types.
 *)
Inductive asdf : nat -> Set :=
| mkAsdf : forall n, list (qwerty n) -> asdf n
with
qwerty : nat -> Set :=
| emptyQwerty : qwerty 0
| someQwerty  : forall n, qwerty n -> (forall m, asdf m) -> qwerty n.

Fixpoint asdf_size n (x:asdf n) : Ord :=
  match x with
  | mkAsdf n xs => succOrd (listOrd (qwerty_size n) xs)
  end
with qwerty_size n (x:qwerty n) : Ord :=
  match x with
  | emptyQwerty => zeroOrd
  | someQwerty n x y => lubOrd (qwerty_size n x) (depOrd asdf_size y)
  end.

Canonical Structure AsdfOrdSize n :=
  MkOrdSize (asdf n) (asdf_size n).
Canonical Structure QwertyOrdSize n :=
  MkOrdSize (qwerty n) (qwerty_size n).

Goal forall n a b c f,
  f n <> mkAsdf _ [a; b; someQwerty _ c f].
Proof.
  ord_crush.
Qed.
