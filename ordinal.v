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


(** Ordinal operators *)
Definition zeroOrd : Ord := ord False (False_rect _).
Definition succOrd (x:Ord) : Ord := ord unit (fun _ => x).
Definition sumOrd (x y:Ord) : Ord :=
  ord bool (fun b => if b then x else y).
Definition limOrd {A:Type} (f:A -> Ord) := ord A f.

(** Strict less-than ordering on ordinals *)

Definition OrdLt1  (x y:Ord) : Prop :=
  match y with
  | ord A f => exists a:A, f a = x
  end.

(* Here is an alternate definition that is less good for
   extremely subtle reasons...
Inductive OrdLt1 : Ord -> Ord -> Prop :=
| ord_lt1 : forall A f i, OrdLt1 (f i) (ord A f).
*)

Definition OrdLt : Ord -> Ord -> Prop
  := clos_trans _ OrdLt1.

(* We can construct a less-or-equal relation
   from the strict less-than relation.

   It might be useful (?)
 *)

Definition OrdLe (x y:Ord) : Prop :=
  (forall z, OrdLt y z -> OrdLt x z) /\
  (forall z, OrdLt z x -> OrdLt z y).

Lemma OrdLe_refl : forall x, OrdLe x x.
Proof.
  unfold OrdLe; intuition.
Qed.

Lemma OrdLe_trans : forall x y z, OrdLe x y -> OrdLe y z -> OrdLe x z.
Proof.
  unfold OrdLe; intuition.
Qed.

Lemma OrdLt_OrdLe : forall x y, OrdLt x y -> OrdLe x y.
Proof.
  unfold OrdLe; intros.
  split; intros.
  - apply t_trans with y; auto.
  - apply t_trans with x; auto.
Qed.

Lemma OrdLtLe_trans : forall x y z, OrdLt x y -> OrdLe y z -> OrdLt x z.
Proof.
  unfold OrdLe; intros.
  intuition.
Qed.

Lemma OrdLeLt_trans : forall x y z, OrdLe x y -> OrdLt y z -> OrdLt x z.
Proof.
  unfold OrdLe; intros.
  intuition.
Qed.


(* An interesting property to consider... can we make it true? *)
Lemma OrdLt_congruence : forall (A:Type) (f g : A -> Ord),
    (forall a, OrdLt (f a) (g a)) ->
    OrdLt (ord A f) (ord A g).
Abort.



(* The one step ordering relation is well founded.
*)
Lemma OrdLt1_wf : well_founded OrdLt1.
Proof.
  intro a. induction a. constructor.
  simpl; firstorder; subst; auto.
Qed.

(*  The transitive closure of the one-step ordering
    is also well founded.
 *)
Lemma OrdLt_wf : well_founded OrdLt.
Proof.
  apply wf_clos_trans. apply OrdLt1_wf.
Qed.

(*   The order is irreflexive, a simple corollary of well-foundedness.
 *)
Corollary OrdLt_irreflexive : forall x, OrdLt x x -> False.
Proof.
  induction x using (well_founded_induction OrdLt_wf).
  firstorder.
Qed.

(** Ordering lemmas on the operators *)

Lemma succ_lt : forall o, OrdLt o (succOrd o).
Proof.
  intros. apply t_step; simpl.
  exists tt. auto.
Qed.

Lemma limit_lt : forall A (f:A -> Ord) i, OrdLt (f i) (limOrd f).
Proof.
  intros. apply t_step; simpl; eauto.
Qed.

Lemma sum_lt1 : forall x y, OrdLt x (sumOrd x y).
Proof.
  intros. apply t_step; simpl.
  exists true; auto.
Qed.  

Lemma sum_lt2 : forall x y, OrdLt y (sumOrd x y).
Proof.
  intros. apply t_step.
  exists false; auto.
Qed.  

Lemma ord_lt_trans : forall x y z, OrdLt x y -> OrdLt y z -> OrdLt x z.
Proof.
  do 3 intro; apply t_trans.
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
Notation "x ◃ y" := (OrdLt (ordSize _ x) (ordSize _ y)) (at level 80, no associativity).


Lemma subterm_trans : forall {A B C:OrdSize} (x:A) (y:B) (z:C),
  x ◃ y -> y ◃ z -> x ◃ z.   
Proof.
  simpl; intros. eapply ord_lt_trans; eauto.
Qed.
 
Lemma size_discriminate : forall (A:OrdSize) (x y:A), x ◃ y -> x <> y.
Proof.
  repeat intro; subst y.
  apply (OrdLt_irreflexive _ H).
Qed.  

Hint Unfold ordSize : ord.
Hint Resolve succ_lt limit_lt sum_lt1 sum_lt2 ord_lt_trans: ord.

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
  | x::xs => sumOrd (f x) (listOrd xs)
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
  simpl; auto with ord.
Qed.

Lemma tail_lt : forall (A:OrdSize) (h:A) (t:list A), t ◃ (h::t).
Proof.
  simpl; auto with ord.
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
Ltac try_ord := try solve [ auto with ord | simpl; eauto with ord ].

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
  | someQwerty n x y => sumOrd (qwerty_size n x) (depOrd asdf_size y)
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
