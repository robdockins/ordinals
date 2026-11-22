From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.

Import ListNotations.
Open Scope list.

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
From Ordinal Require Import BachmannFacts.
From Ordinal Require Import Notation.SchutteMatrix.

Open Scope ord_scope.

(** * A notation system up to the Bachmann–Howard ordinal

A small notation is 0 or φ_T(y), where y is a small notation and the
index T is an Ω-Cantor normal form Ω^{e₁}·c₁ + … + Ω^{eₙ}·cₙ whose
exponents eᵢ are indices and whose coefficients cᵢ are small notations.
Indices denote canonical index trees, built from @embed@, @badd@,
@bmul@ and @bexpΩ@; φ is taken at the base 1+x.

We denote φ_T(y) by the provably normal hierarchy @bphi@, whose values
are complete; Bachmann's φ (@bach@) agrees with it on every notation
(@BS_denote_bach@).  The argument y cannot be folded into the index:
@bach f (T + ξ) 0@ is @veblen G ξ 0@, not @G ξ@. *)

Inductive BSmall : Set :=
| BZ : BSmall
| BN : BIdx -> BSmall -> BSmall
with BIdx : Set :=
| BI : list (BIdx * BSmall) -> BIdx.

Fixpoint BS_denote (x:BSmall) : Ord :=
  match x with
  | BZ => 0
  | BN T y => bphi (addOrd 1) (BI_denote T) (BS_denote y)
  end
with BI_denote (T:BIdx) : BOrd :=
  match T with
  | BI l => fold_left (fun acc p => badd acc (bmul (bexpΩ (BI_denote (fst p))) (embed (BS_denote (snd p)))))
                      l bzero
  end.

(** One summand Ω^e·c of an index. *)
Definition idx_term (p:BIdx * BSmall) : BOrd :=
  bmul (bexpΩ (BI_denote (fst p))) (embed (BS_denote (snd p))).

Definition idx_fold (acc:BOrd) (l:list (BIdx * BSmall)) : BOrd :=
  fold_left (fun acc p => badd acc (idx_term p)) l acc.

Lemma BI_denote_eq l : BI_denote (BI l) = idx_fold bzero l.
Proof. reflexivity. Qed.

Definition BNotation_induction
  (P:BSmall -> Prop) (Q:BIdx -> Prop)
  (HZ: P BZ)
  (HN: forall T y, Q T -> P y -> P (BN T y))
  (HI: forall l, each (fun p => Q (fst p) /\ P (snd p)) l -> Q (BI l)) :
  forall x, P x :=
  fix fs (x:BSmall) : P x :=
    match x as x' return P x' with
    | BZ => HZ
    | BN T y =>
        HN T y
           ((fix fi (T:BIdx) : Q T :=
               match T as T' return Q T' with
               | BI l =>
                   HI l ((fix inner (l:list (BIdx * BSmall)) : each _ l :=
                            match l as l' return each _ l' with
                            | nil => I
                            | p::ps => conj (conj (fi (fst p)) (fs (snd p))) (inner ps)
                            end) l)
               end) T)
           (fs y)
    end.

Definition BIdx_induction
  (P:BSmall -> Prop) (Q:BIdx -> Prop)
  (HZ: P BZ)
  (HN: forall T y, Q T -> P y -> P (BN T y))
  (HI: forall l, each (fun p => Q (fst p) /\ P (snd p)) l -> Q (BI l)) :
  forall T, Q T :=
  fun T =>
    match T as T' return Q T' with
    | BI l =>
        HI l ((fix inner (l:list (BIdx * BSmall)) : each _ l :=
                 match l as l' return each _ l' with
                 | nil => I
                 | p::ps =>
                     conj (conj ((fix fi (T:BIdx) : Q T :=
                                    match T as T' return Q T' with
                                    | BI l0 =>
                                        HI l0 ((fix inner0 (l0:list (BIdx * BSmall)) : each _ l0 :=
                                                  match l0 as l' return each _ l' with
                                                  | nil => I
                                                  | q::qs => conj (conj (fi (fst q))
                                                                        (BNotation_induction P Q HZ HN HI (snd q)))
                                                                  (inner0 qs)
                                                  end) l0)
                                    end) (fst p))
                                (BNotation_induction P Q HZ HN HI (snd p)))
                          (inner ps)
                 end) l)
    end.

(** ** Denotations are complete, canonical and directed *)

Definition idx_ok (T:BOrd) : Prop := bcd T /\ bsdirH T.

Lemma bcd_bzero : bcd bzero.
Proof. split; [ apply bcanon_bzero | apply bdec_bzero ]. Qed.

Lemma idx_ok_term e c : idx_ok e -> complete c -> idx_ok (bmul (bexpΩ e) (embed c)).
Proof.
  intros [He1 He2] Hc. split.
  - apply bcd_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ.
  - apply bsdirH_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ, bsdirH_embed.
    apply bsdirH_bexpΩ; auto.
Qed.

Lemma idx_ok_fold l : forall acc, idx_ok acc ->
  each (fun p => idx_ok (BI_denote (fst p)) /\ complete (BS_denote (snd p))) l ->
  idx_ok (idx_fold acc l).
Proof.
  induction l as [|[e c] l IH]; simpl; intros acc Hacc Hl; auto.
  destruct Hl as [[He Hc] Hl].
  apply IH; auto.
  destruct Hacc as [Ha1 Ha2]. destruct (idx_ok_term _ _ He Hc) as [Ht1 Ht2].
  split; [ apply bcd_badd | apply bsdirH_badd ]; auto.
Qed.

Theorem BNotation_ok :
  (forall x, complete (BS_denote x)) /\ (forall T, idx_ok (BI_denote T)).
Proof.
  set (P := fun x => complete (BS_denote x)).
  set (Q := fun T => idx_ok (BI_denote T)).
  assert (HZ : P BZ) by apply zero_complete.
  assert (HI : forall l, each (fun p => Q (fst p) /\ P (snd p)) l -> Q (BI l)).
  { intros l Hl. unfold Q. rewrite BI_denote_eq.
    apply idx_ok_fold; [ split; [ apply bcd_bzero | apply bsdirH_bzero ] | exact Hl ]. }
  assert (HN : forall T y, Q T -> P y -> P (BN T y)).
  { intros T y [HT1 HT2] Hy. unfold P; simpl.
    apply normal_complete; auto. apply bcanon_normal; auto. apply onePlus_normal. }
  split; [ exact (BNotation_induction P Q HZ HN HI) | exact (BIdx_induction P Q HZ HN HI) ].
Qed.

Lemma BS_complete x : complete (BS_denote x).
Proof. apply BNotation_ok. Qed.

Lemma BI_ok T : idx_ok (BI_denote T).
Proof. apply BNotation_ok. Qed.

Lemma BI_bfam T : bfam (BI_denote T).
Proof. apply bcanon_bfam, BI_ok. Qed.

(** For each index, ξ ↦ φ_T(ξ) is a normal function. *)
Theorem BI_normal T : normal_function (bphi (addOrd 1) (BI_denote T)).
Proof. apply bcanon_normal; [ apply onePlus_normal | apply BI_ok ]. Qed.

(** Bachmann's φ, one component at a time, agrees with the denotation. *)
Theorem BS_denote_bach T y : BS_denote (BN T y) ≈ bach (addOrd 1) (BI_denote T) (BS_denote y).
Proof.
  symmetry.
  destruct (BI_ok T) as [H1 H2].
  apply (bach_bphi_canon (addOrd 1) onePlus_normal _ H1 H2). apply BS_complete.
Qed.

Corollary BS_denote_bach0 T : BS_denote (BN T BZ) ≈ bach (addOrd 1) (BI_denote T) 0.
Proof. apply BS_denote_bach. Qed.

(** ** Basic calibrations *)

Lemma BS_denote_onePlus y : BS_denote (BN (BI []) y) ≈ 1 + BS_denote y.
Proof. apply (bphi_bzero (addOrd 1) onePlus_normal). Qed.

(** A summand with positive coefficient gives the index a component. *)
Lemma idx_term_inh e c : 0 < BS_denote c ->
  inhabited (bsmall (idx_term (e, c)) + bbig (idx_term (e, c))).
Proof.
  unfold idx_term; simpl. intro Hc.
  destruct (BS_denote c) as [X k] eqn:E.
  rewrite ord_lt_unfold in Hc. destruct Hc as [x _].
  destruct (bexpΩ_small_zero (BI_denote e)) as [t0 _].
  destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (k x))) (bexpΩ (BI_denote e)) t0) as [s _].
  destruct (bmul_small_r (bexpΩ (BI_denote e)) (embed (ord X k)) x s) as [t _].
  exact (inhabits (inl t)).
Qed.

Lemma badd_inh_l x y : inhabited (bsmall x + bbig x) -> inhabited (bsmall (badd x y) + bbig (badd x y)).
Proof.
  intros [[a|c]].
  - destruct (badd_small_l x y a) as [a' _]. exact (inhabits (inl a')).
  - destruct (badd_big_l x y c) as [c' _]. exact (inhabits (inr c')).
Qed.

Lemma badd_inh_r x y : inhabited (bsmall y + bbig y) -> inhabited (bsmall (badd x y) + bbig (badd x y)).
Proof.
  intros [[a|c]].
  - destruct (badd_small_r x y a) as [a' _]. exact (inhabits (inl a')).
  - destruct (badd_big_r x y c) as [c' _]. exact (inhabits (inr c')).
Qed.

Lemma idx_fold_inh l : forall acc, inhabited (bsmall acc + bbig acc) ->
  inhabited (bsmall (idx_fold acc l) + bbig (idx_fold acc l)).
Proof.
  induction l as [|p l IH]; simpl; intros acc H; auto.
  apply IH. apply badd_inh_l; auto.
Qed.

Lemma BI_inh e c l : 0 < BS_denote c ->
  inhabited (bsmall (BI_denote (BI ((e, c) :: l))) + bbig (BI_denote (BI ((e, c) :: l)))).
Proof.
  intro Hc. rewrite BI_denote_eq. unfold idx_fold; simpl.
  apply idx_fold_inh. apply badd_inh_r, idx_term_inh; auto.
Qed.

(** With a nonempty index of positive leading coefficient, φ_T(y) is
    infinite, i.e., absorbs 1+. *)
Lemma BS_denote_absorb e c l y : 0 < BS_denote c ->
  1 + BS_denote (BN (BI ((e, c) :: l)) y) ≈ BS_denote (BN (BI ((e, c) :: l)) y).
Proof.
  intro Hc. simpl BS_denote at 1 2.
  destruct (BI_ok (BI ((e, c) :: l))) as [[H1 H2] _].
  apply bphi_onePlus_absorb; auto using BS_complete.
  - apply (bcanon_good (addOrd 1) onePlus_normal); auto.
  - apply BI_inh; auto.
Qed.

(** The index Ω^0·ζ is the ordinal ζ. *)
Definition idx_small (s:BSmall) : BIdx := BI [(BI [], s)].

Lemma idx_small_equiv s : bequiv (BI_denote (idx_small s)) (embed (BS_denote s)).
Proof.
  unfold idx_small. rewrite BI_denote_eq. unfold idx_fold, idx_term; simpl.
  eapply bequiv_trans; [ apply bequiv_badd_zero_l | ].
  apply bequiv_one_mul.
Qed.

(** ** Embedding Schütte's Klammersymbols

A matrix with columns (β₁,α₁), …, (βₙ,αₙ) of decreasing heights
denotes @schutte_matrix (addOrd 1) _ 0@.  A column of height β = 1+ζ
corresponds to the index summand Ω^ζ·α, by @bach_bexpΩ_rep@; a column
of height 0 (necessarily the last) is the argument. *)

(** 1+ζ = s: undo a leading 1+ when there is one. *)
Definition BS_pred1 (s:BSmall) : BSmall :=
  match s with
  | BN (BI []) s' => s'
  | _ => s
  end.

Fixpoint Kl (x:VForm) : BSmall :=
  match x with
  | Z => BZ
  | N l =>
      BN (BI ((fix cols (l:list (VForm * VForm)) : list (BIdx * BSmall) :=
                 match l with
                 | [] => []
                 | (b, a) :: l' =>
                     match b with
                     | Z => cols l'
                     | _ => (idx_small (BS_pred1 (Kl b)), Kl a) :: cols l'
                     end
                 end) l))
         ((fix arg (l:list (VForm * VForm)) : BSmall :=
             match l with
             | [] => BZ
             | (b, a) :: l' =>
                 match b with
                 | Z => Kl a
                 | _ => arg l'
                 end
             end) l)
  end.

Fixpoint Kcols (l:list (VForm * VForm)) : list (BIdx * BSmall) :=
  match l with
  | [] => []
  | (b, a) :: l' =>
      match b with
      | Z => Kcols l'
      | _ => (idx_small (BS_pred1 (Kl b)), Kl a) :: Kcols l'
      end
  end.

Fixpoint Karg (l:list (VForm * VForm)) : BSmall :=
  match l with
  | [] => BZ
  | (b, a) :: l' =>
      match b with
      | Z => Kl a
      | _ => Karg l'
      end
  end.

Lemma Kl_N l : Kl (N l) = BN (BI (Kcols l)) (Karg l).
Proof.
  reflexivity.
Qed.

Lemma BS_pos T y : 0 < BS_denote (BN T y).
Proof. apply (bphi_nonzero (addOrd 1) onePlus_normal). Qed.

Lemma Kl_pos a : a <> Z -> 0 < BS_denote (Kl a).
Proof. destruct a as [|l]; [ tauto | intros _; rewrite Kl_N; apply BS_pos ]. Qed.

Lemma Kcols_head_pos l e c cs : is_sparse l -> Kcols l = (e, c) :: cs -> 0 < BS_denote c.
Proof.
  induction l as [|[b a] l IH]; simpl; [ discriminate | ].
  intros [Ha Hl]. destruct b as [|lb].
  - apply IH; auto.
  - intro E. injection E as _ <- _. apply Kl_pos; auto.
Qed.

(** The column height β is 1 + (the exponent we assign to it). *)
Lemma pred1_correct b : b <> Z -> VF_normal b -> VF_denote b ≈ BS_denote (Kl b) ->
  1 + BS_denote (BS_pred1 (Kl b)) ≈ VF_denote b.
Proof.
  destruct b as [|l]; [ tauto | ]. intros _ Hn Heq.
  rewrite Heq. rewrite Kl_N in *.
  destruct (Kcols l) as [|[e c] cs] eqn:E.
  - simpl BS_pred1. symmetry. apply BS_denote_onePlus.
  - simpl BS_pred1. apply BS_denote_absorb.
    apply (Kcols_head_pos l e c cs); auto. apply Hn.
Qed.

Lemma ord_eq_normal G : normal_function G -> forall x y, x ≈ y -> G x ≈ G y.
Proof. intros HG x y [H1 H2]; split; apply normal_monotone; auto. Qed.

Lemma schutte_matrix_ext m G G' :
  (forall a b, a ≤ b -> G a ≤ G b) -> (forall a b, a ≤ b -> G' a ≤ G' b) ->
  (forall a, G a ≈ G' a) -> schutte_matrix G m 0 ≈ schutte_matrix G' m 0.
Proof.
  intros H1 H2 H3. split; apply schutte_matrix_monotone_func; auto; intro a; apply H3.
Qed.

Lemma Kmatrix l : forall acc G,
  idx_ok acc -> BRep (addOrd 1) acc G ->
  VF_matrix_proper l -> is_sparse l ->
  each (fun p => VF_normal (fst p) /\ VF_normal (snd p)) l ->
  each (fun p => VF_denote (fst p) ≈ BS_denote (Kl (fst p)) /\
                 VF_denote (snd p) ≈ BS_denote (Kl (snd p))) l ->
  schutte_matrix G (matrix_denote l) 0 ≈ bach (addOrd 1) (idx_fold acc (Kcols l)) (BS_denote (Karg l)).
Proof.
  assert (Hm1 : forall x y, x ≤ y -> 1 + x ≤ 1 + y) by (intros; apply addOrd_monotone; auto with ord).
  induction l as [|[b a] l IH]; intros acc G Hacc HR Hp Hs Hn Heq.
  - simpl. symmetry. apply (proj1 (proj2 HR)). apply zero_complete.
  - destruct HR as [HG [Hrep Hcl]].
    simpl in Hp, Hs, Hn, Heq.
    destruct Hn as [[Hnb Hna] Hn]. destruct Heq as [[Eb Ea] Heq]. destruct Hs as [Ha Hs].
    destruct b as [|lb].
    + (* the argument column; it must be the last *)
      destruct l as [|[b2 a2] l].
      * simpl. rewrite schutte_column0.
        transitivity (G (BS_denote (Kl a))).
        { apply ord_eq_normal; auto. rewrite addOrd_zero_r. auto. }
        symmetry. apply Hrep. apply BS_complete.
      * destruct Hp as [_ [_ [Hlt _]]].
        elim (ord_lt_irreflexive 0). apply ord_le_lt_trans with (VF_denote b2); [ apply zero_least | exact Hlt ].
    + set (ζ := BS_pred1 (Kl (N lb))).
      set (ξ := Kl a).
      assert (Hζ : 1 + BS_denote ζ ≈ VF_denote (N lb)).
      { apply pred1_correct; auto. discriminate. }
      set (acc' := badd acc (idx_term (idx_small ζ, ξ))).
      assert (Hok' : idx_ok acc').
      { destruct Hacc as [Ha1 Ha2].
        destruct (idx_ok_term (BI_denote (idx_small ζ)) (BS_denote ξ) (BI_ok _) (BS_complete _)) as [Ht1 Ht2].
        split; [ apply bcd_badd | apply bsdirH_badd ]; auto. }
      assert (HR' : BRep (addOrd 1) acc' (schutte_column G (1 + BS_denote ζ) (BS_denote ξ))).
      { refine (BRep_bequiv (addOrd 1) (normal_monotone _ onePlus_normal)
                  (badd acc (bmul (bexpΩ (embed (BS_denote ζ))) (embed (BS_denote ξ)))) acc' _ _ _ _ _).
        - apply bequiv_badd; [ apply bequiv_refl | ].
          apply bequiv_bmul; [ | apply bequiv_refl ].
          apply bequiv_bexpΩ, bequiv_sym, idx_small_equiv.
        - apply bfam_badd; [ apply bcanon_bfam, Hacc | ].
          apply bfam_bmul; [ apply bfam_bexpΩ, bfam_embed | apply bfam_embed ].
        - apply bcanon_bfam, Hok'.
        - apply (bach_bexpΩ_rep (addOrd 1) (normal_monotone _ onePlus_normal) (BS_denote ζ) (BS_complete _)
                                  acc G (bcanon_bfam _ (proj1 (proj1 Hacc))));
            [ split; auto | apply BS_complete ]. }
      assert (Hl : VF_matrix_proper l).
      { destruct l as [|[b2 a2] l]; simpl; auto. apply Hp. }
      change (schutte_matrix (schutte_column G (VF_denote (N lb)) (VF_denote a)) (matrix_denote l) 0
              ≈ bach (addOrd 1) (idx_fold acc' (Kcols l)) (BS_denote (Karg l))).
      rewrite <- (IH acc' _ Hok' HR' Hl Hs Hn Heq).
      apply schutte_matrix_ext.
      * intros x y Hxy. apply schutte_column_monotone; [ apply (normal_monotone G HG) | reflexivity | exact Hxy ].
      * intros x y Hxy. apply schutte_column_monotone; [ apply (normal_monotone G HG) | reflexivity | exact Hxy ].
      * intro x. split; apply schutte_column_monotone_full;
          first [ apply (normal_monotone G HG) | reflexivity
                | apply (proj1 Hζ) | apply (proj2 Hζ) | apply (proj1 Ea) | apply (proj2 Ea) ].
Qed.

(** Every Klammersymbol in normal form denotes the same ordinal as its
    translation; in particular Bachmann's φ (at the base 1+x) computes
    the Klammersymbol, by @BS_denote_bach@. *)
Theorem Kl_correct : forall x, VF_normal x -> VF_denote x ≈ BS_denote (Kl x).
Proof.
  induction x as [|l IHl] using VForm_induction; intro Hn.
  - reflexivity.
  - rewrite Kl_N.
    destruct Hn as [Hs [Hp [Hn Hlt]]].
    assert (Heq : each (fun p => VF_denote (fst p) ≈ BS_denote (Kl (fst p)) /\
                                 VF_denote (snd p) ≈ BS_denote (Kl (snd p))) l).
    { clear -IHl Hn. induction l as [|[b a] l IH]; simpl in *; auto. intuition. }
    rewrite BS_denote_bach. rewrite BI_denote_eq.
    change (schutte_matrix (addOrd 1) (matrix_denote l) 0
            ≈ bach (addOrd 1) (idx_fold bzero (Kcols l)) (BS_denote (Karg l))).
    apply Kmatrix; auto.
    + split; [ apply bcd_bzero | apply bsdirH_bzero ].
    + apply bach_zero_rep, onePlus_normal.
Qed.

