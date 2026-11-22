From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

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
Open Scope bool_scope.
Open Scope ord_scope.

(** * A notation system up to the Bachmann–Howard ordinal

A small notation is 0 or φ_T(y), where y is a small notation and T is
an index.  An index is 0 or Ω^e·c + r, where the exponent e and the
rest r are indices and the coefficient c is a small notation; in
normal form the exponents strictly decrease, so an index is an
Ω-Cantor normal form.  Indices denote canonical index trees, built
from @embed@, @badd@, @bmul@ and @bexpΩ@; φ is taken at the base 1+x.

We denote φ_T(y) by the provably normal hierarchy @bphi@, whose values
are complete; Bachmann's φ (@bach@) agrees with it on every notation
(@BS_denote_bach@).  The argument y cannot be folded into the index:
@bach f (T + ξ) 0@ is @veblen G ξ 0@, not @G ξ@. *)

Inductive BSmall : Set :=
| BZ : BSmall
| BN : BIdx -> BSmall -> BSmall
with BIdx : Set :=
| BIZ : BIdx
| BIC : BIdx -> BSmall -> BIdx -> BIdx.

Scheme BSmall_mut := Induction for BSmall Sort Prop
with BIdx_mut := Induction for BIdx Sort Prop.
Combined Scheme BNotation_mut from BSmall_mut, BIdx_mut.

Fixpoint BS_denote (x:BSmall) : Ord :=
  match x with
  | BZ => 0
  | BN T y => bphi (addOrd 1) (BI_denote T) (BS_denote y)
  end
with BI_denote (T:BIdx) : BOrd :=
  match T with
  | BIZ => bzero
  | BIC e c r => badd (bmul (bexpΩ (BI_denote e)) (embed (BS_denote c))) (BI_denote r)
  end.

(** ** Denotations are complete, canonical and directed *)

Definition idx_ok (T:BOrd) : Prop := bcd T /\ bsdirH T.

Lemma bcd_bzero : bcd bzero.
Proof. split; [ apply bcanon_bzero | apply bdec_bzero ]. Qed.

Lemma idx_ok_bzero : idx_ok bzero.
Proof. split; [ apply bcd_bzero | apply bsdirH_bzero ]. Qed.

Lemma idx_ok_term e c : idx_ok e -> complete c -> idx_ok (bmul (bexpΩ e) (embed c)).
Proof.
  intros [He1 He2] Hc. split.
  - apply bcd_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ.
  - apply bsdirH_bmul; auto using bcd_bexpΩ, bcd_embed, bpos_bexpΩ, bsdirH_embed.
    apply bsdirH_bexpΩ; auto.
Qed.

Lemma idx_ok_badd x y : idx_ok x -> idx_ok y -> idx_ok (badd x y).
Proof. intros [H1 H2] [H3 H4]. split; [ apply bcd_badd | apply bsdirH_badd ]; auto. Qed.

Theorem BNotation_ok :
  (forall x, complete (BS_denote x)) /\ (forall T, idx_ok (BI_denote T)).
Proof.
  apply BNotation_mut; simpl.
  - apply zero_complete.
  - intros T [HT1 HT2] y Hy.
    apply normal_complete; auto. apply bcanon_normal; auto. apply onePlus_normal.
  - apply idx_ok_bzero.
  - intros e He c Hc r Hr. apply idx_ok_badd; auto. apply idx_ok_term; auto.
Qed.

Lemma BS_complete x : complete (BS_denote x).
Proof. apply BNotation_ok. Qed.

Lemma BI_ok T : idx_ok (BI_denote T).
Proof. apply BNotation_ok. Qed.

Lemma BI_bfam T : bfam (BI_denote T).
Proof. apply bcanon_bfam, BI_ok. Qed.

Lemma BI_good T : bgood (addOrd 1) (BI_denote T).
Proof.
  destruct (BI_ok T) as [[H1 H2] _].
  apply (bcanon_good (addOrd 1) onePlus_normal); auto.
Qed.

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

Lemma BS_denote_onePlus y : BS_denote (BN BIZ y) ≈ 1 + BS_denote y.
Proof. apply (bphi_bzero (addOrd 1) onePlus_normal). Qed.

Lemma BS_pos T y : 0 < BS_denote (BN T y).
Proof. apply (bphi_nonzero (addOrd 1) onePlus_normal). Qed.

Lemma badd_inh_l x y : inhabited (bsmall x + bbig x) -> inhabited (bsmall (badd x y) + bbig (badd x y)).
Proof.
  intros [[a|c]].
  - destruct (badd_small_l x y a) as [a' _]. exact (inhabits (inl a')).
  - destruct (badd_big_l x y c) as [c' _]. exact (inhabits (inr c')).
Qed.

(** A leading summand with positive coefficient gives the index a component. *)
Lemma BI_inh e c r : 0 < BS_denote c -> inhabited (bsmall (BI_denote (BIC e c r)) + bbig (BI_denote (BIC e c r))).
Proof.
  intro Hc. simpl. apply badd_inh_l.
  destruct (BS_denote c) as [X k].
  rewrite ord_lt_unfold in Hc. destruct Hc as [x _].
  destruct (bexpΩ_small_zero (BI_denote e)) as [t0 _].
  destruct (badd_small_r (bmul (bexpΩ (BI_denote e)) (embed (k x))) (bexpΩ (BI_denote e)) t0) as [s _].
  destruct (bmul_small_r (bexpΩ (BI_denote e)) (embed (ord X k)) x s) as [t _].
  exact (inhabits (inl t)).
Qed.

(** With a nonempty index of positive leading coefficient, φ_T(y) is
    infinite, i.e., absorbs 1+. *)
Lemma BS_denote_absorb e c r y : 0 < BS_denote c ->
  1 + BS_denote (BN (BIC e c r) y) ≈ BS_denote (BN (BIC e c r) y).
Proof.
  intro Hc.
  exact (bphi_onePlus_absorb (BI_denote (BIC e c r)) (BS_denote y) (BI_good _) (BI_inh e c r Hc) (BS_complete y)).
Qed.

(** ** Indices below Ω^Ω

An exponent is small when it is 0 or Ω^0·s; the index then lies below
Ω^Ω and corresponds to a list of (exponent, coefficient) pairs of
ordinals. *)

Definition exp_small (e:BIdx) : option BSmall :=
  match e with
  | BIZ => Some BZ
  | BIC BIZ s BIZ => Some s
  | _ => None
  end.

Definition exp_s (e:BIdx) : BSmall :=
  match exp_small e with Some s => s | None => BZ end.

(** The exponent Ω^0·s. *)
Definition idx_small (s:BSmall) : BIdx := BIC BIZ s BIZ.

Lemma bequiv_bzero_embed0 : bequiv bzero (embed 0).
Proof. split; apply bsub_intro; intros []. Qed.

Lemma exp_equiv e s : exp_small e = Some s -> bequiv (BI_denote e) (embed (BS_denote s)).
Proof.
  destruct e as [|[|e1 c1 r1] s0 [|e2 c2 r2]]; simpl; intro H; try discriminate.
  - injection H as <-. apply bequiv_bzero_embed0.
  - injection H as <-.
    eapply bequiv_trans; [ apply bequiv_badd_zero_r | apply bequiv_one_mul ].
Qed.

Fixpoint olist (T:BIdx) : list (Ord * Ord) :=
  match T with
  | BIZ => []
  | BIC e c r => (BS_denote (exp_s e), BS_denote c) :: olist r
  end.

Fixpoint idx_shape (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r => exp_small e <> None /\ idx_shape r
  end.

Lemma BI_osum T : idx_shape T -> bequiv (BI_denote T) (osum (olist T)).
Proof.
  induction T as [|e _ c r IH]; simpl; auto.
  - intros _. apply bequiv_refl.
  - intros [He Hr].
    apply bequiv_badd; auto.
    unfold oterm; simpl. apply bequiv_bmul; [ | apply bequiv_refl ].
    apply bequiv_bexpΩ. unfold exp_s.
    destruct (exp_small e) eqn:E; [ apply exp_equiv; auto | tauto ].
Qed.

(** ** Embedding Schütte's Klammersymbols

A matrix with columns (β₁,α₁), …, (βₙ,αₙ) of decreasing heights
denotes @schutte_matrix (addOrd 1) _ 0@.  A column of height β = 1+ζ
corresponds to the index summand Ω^ζ·α, by @bach_bexpΩ_rep@; a column
of height 0 (necessarily the last) is the argument. *)

(** 1+ζ = s: undo a leading 1+ when there is one. *)
Definition BS_pred1 (s:BSmall) : BSmall :=
  match s with
  | BN BIZ s' => s'
  | _ => s
  end.

Fixpoint Kl (x:VForm) : BSmall :=
  match x with
  | Z => BZ
  | N l =>
      BN ((fix cols (l:list (VForm * VForm)) : BIdx :=
             match l with
             | [] => BIZ
             | (b, a) :: l' =>
                 match b with
                 | Z => cols l'
                 | _ => BIC (idx_small (BS_pred1 (Kl b))) (Kl a) (cols l')
                 end
             end) l)
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

Fixpoint Kidx (l:list (VForm * VForm)) : BIdx :=
  match l with
  | [] => BIZ
  | (b, a) :: l' =>
      match b with
      | Z => Kidx l'
      | _ => BIC (idx_small (BS_pred1 (Kl b))) (Kl a) (Kidx l')
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

Lemma Kl_N l : Kl (N l) = BN (Kidx l) (Karg l).
Proof. reflexivity. Qed.

Lemma Kidx_shape l : idx_shape (Kidx l).
Proof.
  induction l as [|[b a] l IH]; simpl; auto.
  destruct b; simpl; auto. split; auto. discriminate.
Qed.

Lemma Kl_pos a : a <> Z -> 0 < BS_denote (Kl a).
Proof. destruct a as [|l]; [ tauto | intros _; rewrite Kl_N; apply BS_pos ]. Qed.

Lemma Kidx_head_pos l e c r : is_sparse l -> Kidx l = BIC e c r -> 0 < BS_denote c.
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
  destruct (Kidx l) as [|e c r] eqn:E.
  - simpl BS_pred1. symmetry. apply BS_denote_onePlus.
  - simpl BS_pred1. apply BS_denote_absorb.
    apply (Kidx_head_pos l e c r); auto. apply Hn.
Qed.

Lemma ord_eq_normal G : normal_function G -> forall x y, x ≈ y -> G x ≈ G y.
Proof. intros HG x y [H1 H2]; split; apply normal_monotone; auto. Qed.

(** Reading a proper matrix as columns (1+ζ, α) followed by an argument. *)
Lemma Kmatrix l : forall G, (forall x y, x ≤ y -> G x ≤ G y) ->
  VF_matrix_proper l -> is_sparse l ->
  each (fun p => VF_normal (fst p) /\ VF_normal (snd p)) l ->
  each (fun p => VF_denote (fst p) ≈ BS_denote (Kl (fst p)) /\
                 VF_denote (snd p) ≈ BS_denote (Kl (snd p))) l ->
  schutte_matrix G (matrix_denote l) 0 ≈ schutte_matrix G (ocols (olist (Kidx l))) (BS_denote (Karg l)).
Proof.
  induction l as [|[b a] l IH]; intros G HG Hp Hs Hn Heq; simpl; [ reflexivity | ].
  simpl in Hp, Hs, Hn, Heq.
  destruct Hn as [[Hnb Hna] Hn]. destruct Heq as [[Eb Ea] Heq]. destruct Hs as [Ha Hs].
  destruct b as [|lb].
  - destruct l as [|[b2 a2] l].
    + simpl. rewrite schutte_column0. split; apply HG; rewrite addOrd_zero_r; apply Ea.
    + destruct Hp as [_ [_ [Hlt _]]].
      elim (ord_lt_irreflexive 0). apply ord_le_lt_trans with (VF_denote b2); [ apply zero_least | exact Hlt ].
  - assert (Hζ : 1 + BS_denote (BS_pred1 (Kl (N lb))) ≈ VF_denote (N lb)).
    { apply pred1_correct; auto. discriminate. }
    assert (Hl : VF_matrix_proper l).
    { destruct l as [|[b2 a2] l]; simpl; auto. apply Hp. }
    assert (HG1 : forall x y, x ≤ y -> schutte_column G (VF_denote (N lb)) (VF_denote a) x
                                       ≤ schutte_column G (VF_denote (N lb)) (VF_denote a) y).
    { intros x y Hxy. apply schutte_column_monotone; auto with ord. }
    change (schutte_matrix (schutte_column G (VF_denote (N lb)) (VF_denote a)) (matrix_denote l) 0
            ≈ schutte_matrix (schutte_column G (1 + BS_denote (BS_pred1 (Kl (N lb)))) (BS_denote (Kl a)))
                             (ocols (olist (Kidx l))) (BS_denote (Karg l))).
    rewrite (IH _ HG1 Hl Hs Hn Heq).
    split; apply schutte_matrix_monotone_func; auto;
      try (intros x y Hxy; apply schutte_column_monotone; auto with ord);
      intro x; apply schutte_column_monotone_full; auto with ord;
      first [ apply (proj1 Hζ) | apply (proj2 Hζ) | apply (proj1 Ea) | apply (proj2 Ea) ].
Qed.

(** An index below Ω^Ω represents the Klammersymbol whose columns are
    (1+ζ, c) for its summands Ω^ζ·c. *)
Lemma BI_rep T : idx_shape T ->
  BRep (addOrd 1) (BI_denote T) (schutte_matrix (addOrd 1) (ocols (olist T))).
Proof.
  intro HT.
  assert (Hc : each (fun p => complete (fst p) /\ complete (snd p)) (olist T)).
  { clear HT. induction T as [|e _ c r IH]; simpl; auto.
    split; auto using BS_complete. }
  apply BRep_bequiv with (ofold bzero (olist T)).
  - apply normal_monotone, onePlus_normal.
  - eapply bequiv_trans; [ apply ofold_osum | ].
    eapply bequiv_trans; [ apply bequiv_badd_zero_l | ].
    apply bequiv_sym, BI_osum; auto.
  - apply bfam_ofold, bfam_bzero.
  - apply BI_bfam.
  - apply ofold_rep; auto using bfam_bzero.
    + apply normal_monotone, onePlus_normal.
    + apply bach_zero_rep, onePlus_normal.
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
    rewrite BS_denote_bach.
    change (schutte_matrix (addOrd 1) (matrix_denote l) 0
            ≈ bach (addOrd 1) (BI_denote (Kidx l)) (BS_denote (Karg l))).
    rewrite (Kmatrix l (addOrd 1)); auto.
    + symmetry. apply (BI_rep (Kidx l) (Kidx_shape l)). apply BS_complete.
    + apply normal_monotone, onePlus_normal.
Qed.

(** * Normal forms and comparison below Ω^Ω

Here every exponent is small (0 or Ω^0·s with s ≠ 0), so the indices
lie below Ω^Ω.  φ_T(y) is normal when T is a normal Ω-Cantor normal
form (exponents strictly decreasing, coefficients positive), y < φ_T(y)
(the argument is not a fixpoint), and every coefficient of T is below
φ_T(y).  Comparison is Bachmann's rule: for T < T',
φ_T(a) < φ_{T'}(b) iff a and every coefficient of T lie below
φ_{T'}(b), because then φ_{T'}(b) is a fixpoint of φ_T (@olt_zlt@). *)

Fixpoint coef_lt (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC _ c r => BS_denote c < z /\ coef_lt z r
  end.

Fixpoint coef_ge (z:Ord) (T:BIdx) : Prop :=
  match T with
  | BIZ => False
  | BIC _ c r => z ≤ BS_denote c \/ coef_ge z r
  end.

Fixpoint BS_nf (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y =>
      BI_nf T /\ BS_nf y /\ onormal (olist T) /\
      BS_denote y < BS_denote (BN T y) /\ coef_lt (BS_denote (BN T y)) T
  end
with BI_nf (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r =>
      match e with
      | BIZ => True
      | BIC BIZ s BIZ => s <> BZ /\ BS_nf s
      | _ => False
      end /\ BS_nf c /\ BI_nf r
  end.

Definition exp_nf (e:BIdx) : Prop :=
  match e with
  | BIZ => True
  | BIC BIZ s BIZ => s <> BZ /\ BS_nf s
  | _ => False
  end.

Lemma BI_nf_cons e c r : BI_nf (BIC e c r) <-> exp_nf e /\ BS_nf c /\ BI_nf r.
Proof. reflexivity. Qed.

Lemma exp_nf_small e : exp_nf e -> exp_small e <> None /\ BS_nf (exp_s e).
Proof.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl; intuition; discriminate.
Qed.

Lemma exp_nf_inj e e' : exp_nf e -> exp_nf e' -> exp_s e = exp_s e' -> e = e'.
Proof.
  intros H H' E.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; try contradiction;
    destruct e' as [|[|e1' c1' r1'] s' [|e2' c2' r2']]; try contradiction;
    unfold exp_s, exp_small in E; simpl in E, H, H'; subst; auto; intuition.
Qed.

Lemma BI_nf_shape T : BI_nf T -> idx_shape T.
Proof.
  induction T as [|e _ c r IH]; simpl; auto.
  intros [He [_ Hr]]. split; auto. apply (exp_nf_small e He).
Qed.

Lemma coef_lt_ocoef z T : coef_lt z T -> ocoef_lt z (olist T).
Proof. unfold ocoef_lt. induction T as [|e _ c r IH]; simpl; intuition. Qed.

Lemma coef_ge_lt z w T : coef_ge z T -> coef_lt w T -> z < w.
Proof.
  induction T as [|e _ c r IH]; simpl; [ tauto | ].
  intros [H|H] [H1 H2]; [ eapply ord_le_lt_trans; eauto | auto ].
Qed.

(** ** Semantic cases of the comparison *)

(** Bachmann's rule for distinct indices. *)
Lemma nest_lt T a T' b :
  BS_nf (BN T a) -> BS_nf (BN T' b) -> olt (olist T) (olist T') ->
  BS_denote a < BS_denote (BN T' b) -> coef_lt (BS_denote (BN T' b)) T ->
  BS_denote (BN T a) < BS_denote (BN T' b).
Proof.
  intros [HT [_ [Hon _]]] [HT' [_ [Hon' _]]] Hlt Ha Hc.
  set (z := BS_denote (BN T' b)) in *.
  assert (Hz : zlt z (BI_denote T) (BI_denote T')).
  { apply zlt_mono_l with (osum (olist T)); [ apply (BI_osum T (BI_nf_shape T HT)) | ].
    apply zlt_mono_r with (osum (olist T')); [ | apply (BI_osum T' (BI_nf_shape T' HT')) ].
    apply olt_zlt; auto. apply coef_lt_ocoef; auto. }
  assert (Hi : inhabited (bsmall (BI_denote T') + bbig (BI_denote T'))).
  { destruct T' as [|e' c' r']; [ inversion Hlt | ].
    apply BI_inh. apply Hon'. }
  assert (Hfix := zlt_value (addOrd 1) onePlus_normal (BI_denote T) (BI_denote T') (BS_denote b)
                    Hz (BI_good T') (BI_bfam T') Hi (BS_complete b)).
  eapply ord_lt_le_trans; [ | exact Hfix ].
  apply normal_increasing; auto using BI_normal.
  apply (BS_complete (BN T' b)).
Qed.

Lemma oeq_bequiv T T' : idx_shape T -> idx_shape T' -> oeq (olist T) (olist T') ->
  bequiv (BI_denote T) (BI_denote T').
Proof.
  intros H H' Heq.
  eapply bequiv_trans; [ apply BI_osum; auto | ].
  eapply bequiv_trans; [ apply oeq_osum, Heq | ].
  apply bequiv_sym, BI_osum; auto.
Qed.

Lemma bphi_idx_eq T T' y : idx_shape T -> idx_shape T' -> oeq (olist T) (olist T') ->
  bphi (addOrd 1) (BI_denote T) y ≈ bphi (addOrd 1) (BI_denote T') y.
Proof.
  intros H H' Heq. apply bphi_bequiv; auto using BI_bfam, oeq_bequiv.
  apply normal_monotone, onePlus_normal.
Qed.

(** ** The comparison algorithm *)

Fixpoint BS_size (x:BSmall) : nat :=
  match x with
  | BZ => 1
  | BN T y => S (BI_size T + BS_size y)
  end
with BI_size (T:BIdx) : nat :=
  match T with
  | BIZ => 1
  | BIC e c r => S (BI_size e + BS_size c + BI_size r)
  end.

Lemma exp_s_size e : (BS_size (exp_s e) <= BI_size e)%nat.
Proof.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; unfold exp_s, exp_small; simpl; lia.
Qed.

Definition isLT (o:ordering) : bool := match o with LT => true | _ => false end.

Fixpoint cmpS (n:nat) (x y:BSmall) {struct n} : ordering :=
  match n with
  | O => EQ
  | S n' =>
    match x, y with
    | BZ, BZ => EQ
    | BZ, BN _ _ => LT
    | BN _ _, BZ => GT
    | BN T a, BN T' b =>
      let fix below (T:BIdx) (z:BSmall) : bool :=
          match T with
          | BIZ => true
          | BIC _ c r => isLT (cmpS n' c z) && below r z
          end in
      match cmpI n' T T' with
      | EQ => cmpS n' a b
      | LT => if isLT (cmpS n' a y) && below T y then LT else GT
      | GT => if isLT (cmpS n' b x) && below T' x then GT else LT
      end
    end
  end
with cmpI (n:nat) (T T':BIdx) {struct n} : ordering :=
  match n with
  | O => EQ
  | S n' =>
    match T, T' with
    | BIZ, BIZ => EQ
    | BIZ, BIC _ _ _ => LT
    | BIC _ _ _, BIZ => GT
    | BIC e c r, BIC e' c' r' =>
      match cmpS n' (exp_s e) (exp_s e') with
      | LT => LT
      | GT => GT
      | EQ => match cmpS n' c c' with
              | LT => LT
              | GT => GT
              | EQ => cmpI n' r r'
              end
      end
    end
  end.

Definition coefs_below (n:nat) : BIdx -> BSmall -> bool :=
  fix below (T:BIdx) (z:BSmall) : bool :=
    match T with
    | BIZ => true
    | BIC _ c r => isLT (cmpS n c z) && below r z
    end.

Lemma cmpS_BN n T a T' b : cmpS (S n) (BN T a) (BN T' b) =
  match cmpI n T T' with
  | EQ => cmpS n a b
  | LT => if isLT (cmpS n a (BN T' b)) && coefs_below n T (BN T' b) then LT else GT
  | GT => if isLT (cmpS n b (BN T a)) && coefs_below n T' (BN T a) then GT else LT
  end.
Proof. reflexivity. Qed.

Definition cmpI_ok (o:ordering) (T T':BIdx) : Prop :=
  match o with
  | LT => olt (olist T) (olist T')
  | EQ => oeq (olist T) (olist T')
  | GT => olt (olist T') (olist T)
  end.

Lemma isLT_spec o a b : ordering_correct o a b ->
  (isLT o = true -> a < b) /\ (isLT o = false -> b ≤ a).
Proof.
  destruct o; simpl; intro H; split; intro E; try discriminate; auto.
  - apply H.
  - apply ord_lt_le; auto.
Qed.

Lemma coefs_below_spec n T y :
  (forall c, (BS_size c <= BI_size T)%nat -> BS_nf c -> ordering_correct (cmpS n c y) (BS_denote c) (BS_denote y)) ->
  BI_nf T ->
  (coefs_below n T y = true -> coef_lt (BS_denote y) T) /\
  (coefs_below n T y = false -> coef_ge (BS_denote y) T).
Proof.
  induction T as [|e _ c r IH]; simpl; intros Hc HT; [ split; auto; discriminate | ].
  destruct HT as [_ [Hcn Hr]].
  assert (Hr' : forall c0, (BS_size c0 <= BI_size r)%nat -> BS_nf c0 ->
                  ordering_correct (cmpS n c0 y) (BS_denote c0) (BS_denote y)).
  { intros; apply Hc; auto; lia. }
  destruct (isLT_spec _ _ _ (Hc c ltac:(lia) Hcn)) as [S1 S2].
  destruct (IH Hr' Hr) as [R1 R2].
  destruct (isLT (cmpS n c y)) eqn:E1; destruct (coefs_below n r y) eqn:E2; simpl;
    split; intro H; try discriminate; auto.
Qed.

Theorem cmp_correct n :
  (forall x y, (BS_size x + BS_size y < n)%nat -> BS_nf x -> BS_nf y ->
               ordering_correct (cmpS n x y) (BS_denote x) (BS_denote y)) /\
  (forall T T', (BI_size T + BI_size T' < n)%nat -> BI_nf T -> BI_nf T' -> cmpI_ok (cmpI n T T') T T').
Proof.
  induction n as [|n [IHS IHI]]; [ split; intros; lia | ].
  split.
  - intros x y Hsz Hx Hy.
    destruct x as [|T a]; destruct y as [|T' b].
    + simpl. reflexivity.
    + apply BS_pos.
    + apply BS_pos.
    + rewrite cmpS_BN. simpl in Hsz.
      assert (Hx' := Hx). assert (Hy' := Hy).
      destruct Hx' as [HT [Ha [_ [Hax Hcx]]]]. destruct Hy' as [HT' [Hb [_ [Hby Hcy]]]].
      assert (HI := IHI T T' ltac:(lia) HT HT').
      destruct (cmpI n T T') eqn:EI; simpl in HI.
      * (* T < T' *)
        destruct (isLT_spec _ _ _ (IHS a (BN T' b) ltac:(simpl; lia) Ha Hy)) as [A1 A2].
        destruct (coefs_below_spec n T (BN T' b)
                    (fun c Hc Hcn => IHS c (BN T' b) ltac:(simpl; lia) Hcn Hy) HT) as [C1 C2].
        destruct (isLT (cmpS n a (BN T' b))) eqn:E1; destruct (coefs_below n T (BN T' b)) eqn:E2; simpl.
        -- apply nest_lt; auto.
        -- apply (coef_ge_lt _ _ T); auto.
        -- apply ord_le_lt_trans with (BS_denote a); auto.
        -- apply ord_le_lt_trans with (BS_denote a); auto.
      * (* equal indices *)
        assert (Heq := bphi_idx_eq T T' (BS_denote b) (BI_nf_shape T HT) (BI_nf_shape T' HT') HI).
        assert (Hab := IHS a b ltac:(lia) Ha Hb).
        change (ordering_correct (cmpS n a b) (bphi (addOrd 1) (BI_denote T) (BS_denote a))
                                 (bphi (addOrd 1) (BI_denote T') (BS_denote b))).
        rewrite <- Heq.
        destruct (cmpS n a b); simpl in *.
        -- apply normal_increasing; auto using BI_normal, BS_complete.
        -- apply ord_eq_normal; auto using BI_normal.
        -- apply normal_increasing; auto using BI_normal, BS_complete.
      * (* T' < T *)
        destruct (isLT_spec _ _ _ (IHS b (BN T a) ltac:(simpl; lia) Hb Hx)) as [A1 A2].
        destruct (coefs_below_spec n T' (BN T a)
                    (fun c Hc Hcn => IHS c (BN T a) ltac:(simpl; lia) Hcn Hx) HT') as [C1 C2].
        destruct (isLT (cmpS n b (BN T a))) eqn:E1; destruct (coefs_below n T' (BN T a)) eqn:E2; simpl.
        -- apply nest_lt; auto.
        -- apply (coef_ge_lt _ _ T'); auto.
        -- apply ord_le_lt_trans with (BS_denote b); auto.
        -- apply ord_le_lt_trans with (BS_denote b); auto.
  - intros T T' Hsz HT HT'.
    destruct T as [|e c r]; destruct T' as [|e' c' r']; simpl.
    + constructor.
    + constructor.
    + constructor.
    + simpl in Hsz. destruct HT as [He [Hc Hr]]. destruct HT' as [He' [Hc' Hr']].
      destruct (exp_nf_small e He) as [_ Hes]. destruct (exp_nf_small e' He') as [_ Hes'].
      assert (HE := IHS (exp_s e) (exp_s e') ltac:(pose proof (exp_s_size e); pose proof (exp_s_size e'); lia) Hes Hes').
      destruct (cmpS n (exp_s e) (exp_s e')); simpl in HE.
      * apply olt_exp; auto.
      * assert (HC := IHS c c' ltac:(lia) Hc Hc').
        destruct (cmpS n c c'); simpl in HC.
        -- apply olt_coef; auto.
        -- assert (HR := IHI r r' ltac:(lia) Hr Hr').
           destruct (cmpI n r r'); simpl in HR.
           ++ apply olt_tail; auto.
           ++ apply oeq_cons; auto.
           ++ apply olt_tail; auto; symmetry; auto.
        -- apply olt_coef; auto. symmetry; auto.
      * apply olt_exp; auto.
Qed.

Definition BS_compare (x y:BSmall) : ordering := cmpS (S (BS_size x + BS_size y)) x y.

Theorem BS_compare_correct x y : BS_nf x -> BS_nf y ->
  ordering_correct (BS_compare x y) (BS_denote x) (BS_denote y).
Proof. intros Hx Hy. apply cmp_correct; auto. Qed.

Theorem BS_decide_order x y : BS_nf x -> BS_nf y ->
  {BS_denote x < BS_denote y} + {BS_denote y ≤ BS_denote x}.
Proof.
  intros Hx Hy. assert (H := BS_compare_correct x y Hx Hy).
  destruct (BS_compare x y); simpl in H; [ left; auto | right; apply H | right; apply ord_lt_le; auto ].
Defined.

(** ** Uniqueness of normal forms *)

Theorem cmp_eq n :
  (forall x y, (BS_size x + BS_size y < n)%nat -> BS_nf x -> BS_nf y -> cmpS n x y = EQ -> x = y) /\
  (forall T T', (BI_size T + BI_size T' < n)%nat -> BI_nf T -> BI_nf T' -> cmpI n T T' = EQ -> T = T').
Proof.
  induction n as [|n [IHS IHI]]; [ split; intros; lia | ].
  split.
  - intros x y Hsz Hx Hy.
    destruct x as [|T a]; destruct y as [|T' b]; [ auto | simpl; discriminate | simpl; discriminate | ].
    rewrite cmpS_BN. simpl in Hsz.
    destruct Hx as [HT [Ha _]]. destruct Hy as [HT' [Hb _]].
    destruct (cmpI n T T') eqn:EI.
    + destruct (_ && _); discriminate.
    + intro E. f_equal; [ apply IHI | apply IHS ]; auto; lia.
    + destruct (_ && _); discriminate.
  - intros T T' Hsz HT HT'.
    destruct T as [|e c r]; destruct T' as [|e' c' r']; simpl; try discriminate; auto.
    simpl in Hsz. destruct HT as [He [Hc Hr]]. destruct HT' as [He' [Hc' Hr']].
    destruct (exp_nf_small e He) as [_ Hes]. destruct (exp_nf_small e' He') as [_ Hes'].
    destruct (cmpS n (exp_s e) (exp_s e')) eqn:E1; try discriminate.
    destruct (cmpS n c c') eqn:E2; try discriminate.
    intro E3. f_equal.
    + apply exp_nf_inj; auto. apply IHS; auto.
      pose proof (exp_s_size e); pose proof (exp_s_size e'); lia.
    + apply IHS; auto; lia.
    + apply IHI; auto; lia.
Qed.

Theorem BS_nf_unique x y : BS_nf x -> BS_nf y -> BS_denote x ≈ BS_denote y -> x = y.
Proof.
  intros Hx Hy Heq.
  assert (H := BS_compare_correct x y Hx Hy).
  destruct (BS_compare x y) eqn:E; simpl in H.
  - elim (ord_lt_irreflexive (BS_denote x)).
    apply ord_lt_le_trans with (BS_denote y); [ exact H | apply Heq ].
  - apply (proj1 (cmp_eq (S (BS_size x + BS_size y)))); auto.
  - elim (ord_lt_irreflexive (BS_denote y)).
    apply ord_lt_le_trans with (BS_denote x); [ exact H | apply Heq ].
Qed.

(** * Sanity check: the fragment below Ω^Ω reaches the Large Veblen Ordinal

The notations whose exponents are all small denote exactly the values
of Schütte's Klammersymbols: @Kl@ translates Klammersymbols into the
fragment, and @Kinv@ translates back, both preserving denotation.  So
the fragment's order type is the Large Veblen Ordinal, as for
@SchutteMatrix@. *)

Fixpoint BS_frag (x:BSmall) : Prop :=
  match x with
  | BZ => True
  | BN T y => BI_frag T /\ BS_frag y
  end
with BI_frag (T:BIdx) : Prop :=
  match T with
  | BIZ => True
  | BIC e c r =>
      match e with
      | BIZ => True
      | BIC BIZ s BIZ => BS_frag s
      | _ => False
      end /\ BS_frag c /\ BI_frag r
  end.

Lemma BI_frag_shape T : BI_frag T -> idx_shape T.
Proof.
  induction T as [|e _ c r IH]; simpl; auto.
  intros [He [_ Hr]]. split; auto.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl in *; try contradiction; discriminate.
Qed.

Lemma BS_nf_frag : (forall x, BS_nf x -> BS_frag x) /\ (forall T, BI_nf T -> BI_frag T).
Proof.
  apply BNotation_mut; simpl; auto; [ intros T HT y Hy; intuition | ].
  intros e He c Hc r Hr [Hen [Hcn Hrn]]. split; auto.
  destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl in *; auto; try contradiction.
  destruct Hen as [_ Hs]. apply (He (conj I (conj Hs I))).
Qed.

Lemma frag_pred1 u : BS_frag u -> BS_frag (BS_pred1 u).
Proof. destruct u as [|[|e c r] y]; simpl; intuition. Qed.

Lemma Kidx_frag l : each (fun p => BS_frag (Kl (fst p)) /\ BS_frag (Kl (snd p))) l ->
  BI_frag (Kidx l) /\ BS_frag (Karg l).
Proof.
  induction l as [|[b a] l IH]; [ simpl; auto | ].
  intros [[Hb Ha] Hl]. destruct (IH Hl) as [H1 H2].
  destruct b as [|lb].
  - change (BI_frag (Kidx l) /\ BS_frag (Kl a)). split; auto.
  - change (BI_frag (BIC (idx_small (BS_pred1 (Kl (N lb)))) (Kl a) (Kidx l)) /\ BS_frag (Karg l)).
    split; auto.
    split; [ change (BS_frag (BS_pred1 (Kl (N lb)))); apply frag_pred1; auto | split; auto ].
Qed.

Lemma Kl_frag : forall x, BS_frag (Kl x).
Proof.
  induction x as [|l IHl] using VForm_induction; [ simpl; auto | ].
  rewrite Kl_N. apply Kidx_frag; auto.
Qed.

Fixpoint Kinv (x:BSmall) : VForm :=
  match x with
  | BZ => Z
  | BN T y => N (Kinv_cols T ++ [(Z, Kinv y)])
  end
with Kinv_cols (T:BIdx) : list (VForm * VForm) :=
  match T with
  | BIZ => []
  | BIC e c r => (Kinv_exp e, Kinv c) :: Kinv_cols r
  end
with Kinv_exp (e:BIdx) : VForm :=
  match e with
  | BIC BIZ s BIZ => N [(Z, Kinv s)]
  | _ => N []
  end.

Lemma VF_onePlus v : VF_denote (N [(Z, v)]) ≈ 1 + VF_denote v.
Proof.
  change (schutte_column (addOrd 1) 0 (VF_denote v) 0 ≈ 1 + VF_denote v).
  rewrite schutte_column0. rewrite addOrd_zero_r. reflexivity.
Qed.

Theorem Kinv_correct :
  (forall x, BS_frag x -> VF_denote (Kinv x) ≈ BS_denote x) /\
  (forall T, BI_frag T -> meq (matrix_denote (Kinv_cols T)) (ocols (olist T))).
Proof.
  apply BNotation_mut.
  - intros _. reflexivity.
  - intros T IHT y IHy [HT Hy].
    assert (HM := IHT HT).
    assert (Hv := IHy Hy).
    destruct (BI_rep T (BI_frag_shape T HT)) as [HG [Hrep _]].
    change (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T ++ [(Z, Kinv y)])) 0
            ≈ BS_denote (BN T y)).
    unfold matrix_denote. rewrite map_app. rewrite schutte_matrix_app.
    change (schutte_column (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T))) 0 (VF_denote (Kinv y)) 0
            ≈ BS_denote (BN T y)).
    transitivity (schutte_matrix (addOrd 1) (matrix_denote (Kinv_cols T)) (VF_denote (Kinv y) + 0));
      [ apply schutte_column0 | ].
    transitivity (schutte_matrix (addOrd 1) (ocols (olist T)) (VF_denote (Kinv y) + 0)).
    { apply schutte_matrix_meq; auto. apply normal_monotone, onePlus_normal. }
    transitivity (schutte_matrix (addOrd 1) (ocols (olist T)) (BS_denote y)).
    { apply ord_eq_normal; auto. rewrite addOrd_zero_r. auto. }
    rewrite BS_denote_bach. symmetry. apply Hrep, BS_complete.
  - intros _. constructor.
  - intros e IHe c IHc r IHr [He [Hc Hr]]. simpl.
    constructor; auto.
    destruct e as [|[|e1 c1 r1] s [|e2 c2 r2]]; simpl in He; try contradiction.
    + unfold exp_s, exp_small. simpl. reflexivity.
    + assert (H := IHe (conj I (conj He I))). simpl in H.
      inversion H as [|b0 a0 m0 b0' a0' m0' Hb0 Ha0 Hm0]; subst.
      unfold exp_s, exp_small. simpl Kinv_exp.
      rewrite VF_onePlus. split; apply addOrd_monotone; auto with ord; apply Ha0.
Qed.

Theorem frag_bounded x : BS_frag x -> BS_denote x < LargeVeblenOrdinal.
Proof.
  intro Hx. rewrite <- (proj1 Kinv_correct x Hx). apply VForm_bounded.
Qed.

Corollary nf_bounded x : BS_nf x -> BS_denote x < LargeVeblenOrdinal.
Proof. intro Hx. apply frag_bounded, BS_nf_frag, Hx. Qed.

Definition FragOrd : Ord := ord {x:BSmall | BS_frag x} (fun x => BS_denote (proj1_sig x)).

Theorem FragOrd_LVO : FragOrd ≈ LargeVeblenOrdinal.
Proof.
  split.
  - rewrite ord_le_unfold. intros [x Hx]. simpl. apply frag_bounded; auto.
  - rewrite ord_le_unfold. intro a.
    destruct (LVO_proper_VForm (LargeVeblenOrdinal a)) as [y [Hp Hle]].
    { apply index_lt. }
    destruct (VF_normalize_correct y Hp) as [Heq Hn].
    rewrite ord_lt_unfold.
    exists (exist _ (Kl (VF_normalize y)) (Kl_frag _)). simpl.
    rewrite Hle, <- Heq. apply Kl_correct; auto.
Qed.
