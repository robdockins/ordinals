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
From Ordinal Require Import BachmannAssoc.

Open Scope ord_scope.

(** * Arbitrary powers of Ω, and the canonical trees *)

(** ** Auxiliary lemmas for the power theorems *)

Lemma fixOrd_ext_eq F F' a : (forall x, F x = F' x) -> fixOrd F a ≈ fixOrd F' a.
Proof.
  intro H.
  assert (Hiter : forall n, iter_f F a n = iter_f F' a n).
  { induction n; simpl; auto. rewrite IHn. apply H. }
  unfold fixOrd. apply sup_ord_eq_morphism; intro n.
  rewrite Hiter. reflexivity.
Qed.

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

(** Adding to zero does not change φ. *)

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

(** ** The canonical trees

The power theorem above is stated for @bPow ζ@, which presents Ω^ζ
by recursion on ζ.  The canonical tree @bexpΩ (embed ζ)@ produced by
the tree arithmetic has the same components (the small child 0 and
the families ξ ↦ Ω^(ζ_i)·ξ), merely arranged differently, and the two
are @bsub@-equivalent; likewise Ω^ζ·1 and Ω^ζ.  We transfer the power
theorem along such equivalences, and along extensions by components
that already fix the represented values. *)

Lemma bsub_bPow : forall ζ ζ', ζ ≤ ζ' -> bsub (bPow ζ) (bPow ζ').
Proof.
  induction ζ as [Z m Hm]; intros [Z' m'] H; simpl.
  split.
  - intros []. exists tt. exact (bsub_refl bzero).
  - intro i. destruct (ord_le_subord _ _ H i) as [j Hj].
    exists j. intro ξ. apply bsub_bmul_l. apply Hm. exact Hj.
Qed.

Lemma bsub_bPow_bexpΩ : forall ζ,
  bsub (bPow ζ) (bexpΩ (embed ζ)) /\ bsub (bexpΩ (embed ζ)) (bPow ζ).
Proof.
  induction ζ as [Z m Hm]; split; apply bsub_intro.
  - intros []. exists (inl tt). exact (bsub_refl bzero).
  - intro i. exists (inr (inl (existT _ i (inr tt)))). intro ξ.
    change (bsub (bmul (bPow (m i)) (embed ξ)) (bmul (bexpΩ (embed (m i))) (embed ξ))).
    apply bsub_bmul_l, (proj1 (Hm i)).
  - intros [[]|[[i [[[] _]|[]]]|[]]].
    exists tt. exact (bsub_refl bzero).
  - intros [[]|[[i [[[] _]|[]]]|[]]].
    exists i. intro ξ.
    change (bsub (bmul (bexpΩ (embed (m i))) (embed ξ)) (bmul (bPow (m i)) (embed ξ))).
    apply bsub_bmul_l, (proj2 (Hm i)).
Qed.

Lemma bsub_badd_empty_l x y :
  (bsmall x -> False) -> (bbig x -> False) ->
  bsub (badd x y) y /\ bsub y (badd x y).
Proof.
  intros Hs Hb.
  induction y as [B g Hg D h Hh]; split; apply bsub_intro.
  - intro s.
    destruct (badd_small_cases x (bnode B g D h) s) as [[a _]|[b Hb']]; [ elim (Hs a) | ].
    rewrite Hb'. exists b. apply (Hg b).
  - intro c.
    destruct (badd_big_cases x (bnode B g D h) c) as [[c' _]|[d Hd]]; [ elim (Hb c') | ].
    exists d. intro ξ. rewrite Hd. apply (Hh d ξ).
  - intro b.
    destruct (badd_small_r x (bnode B g D h) b) as [t Ht].
    exists t. rewrite Ht. apply (Hg b).
  - intro d.
    destruct (badd_big_r x (bnode B g D h) d) as [t Ht].
    exists t. intro ξ. rewrite Ht. apply (Hh d ξ).
Qed.

(** P·1 and P are @bsub@-equivalent. *)
Lemma bsub_bmul_one P : bsub (bmul P (embed 1)) P /\ bsub P (bmul P (embed 1)).
Proof.
  assert (HZ := bsub_badd_empty_l (bmul P (embed 0)) P
                  (fun s => match s with inl (existT _ a _) => a | inr b => b end)
                  (fun c => match c with inl (existT _ a _) => a | inr b => b end)).
  destruct HZ as [HZ1 HZ2].
  split; apply bsub_intro.
  - intros [[[] s]|[]]. apply (bsub_small _ _ HZ1 s).
  - intros [[[] c]|[]]. apply (bsub_big _ _ HZ1 c).
  - intro b. destruct (bsub_small _ _ HZ2 b) as [s Hs].
    exists (inl (existT _ tt s)). exact Hs.
  - intro d. destruct (bsub_big _ _ HZ2 d) as [c Hc].
    exists (inl (existT _ tt c)). exact Hc.
Qed.

(** Transferring @BRep@ along @bsub@. *)
Lemma bcomp_bsub f (Hf : forall x y, x ≤ y -> f x ≤ f y) T T' :
  bsub T' T -> bfam T ->
  forall k', exists k, forall x, bcomp f T' k' x ≤ bcomp f T k x.
Proof.
  intros H HT [a'|c'].
  - destruct (bsub_small _ _ H a') as [a Ha].
    exists (inl a). intro x.
    change (bach f (bsmallSz T' a') x ≤ bach f (bsmallSz T a) x).
    apply bach_mono_index; auto. apply bfam_bmono; auto. apply bfam_small; auto.
  - destruct (bsub_big _ _ H c') as [c Hc].
    exists (inr c). intro x.
    change (bach f (bbigSz T' c' x) 0 ≤ bach f (bbigSz T c x) 0).
    apply bach_mono_index; auto. apply bfam_bmono; auto. apply bfam_big; auto.
Qed.

(** If T ⊑ T' and every component of T' fixes the values of G, then
    T' represents G whenever T does. *)
Lemma BRep_extend f (Hf : forall x y, x ≤ y -> f x ≤ f y) T T' G :
  bsub T T' -> bfam T' -> BRep f T G ->
  (forall k y, complete y -> bcomp f T' k (G y) ≤ G y) ->
  BRep f T' G.
Proof.
  intros HTT' HT' [HG [Hrep Hcl]] Hcl'.
  assert (HT'm : bmono f T') by (apply bfam_bmono; auto).
  split; [ exact HG | split; [ | exact Hcl' ] ].
  induction y as [Y h Hy]; intro Hyc.
  assert (Hyc' := Hyc). destruct Hyc' as [_ [_ Hhc]].
  split.
  - apply bach_le_comp.
    + transitivity (bach f T (ord Y h)); [ apply f_le_bach | apply (proj1 (Hrep _ Hyc)) ].
    + intro k.
      apply fixOrd_least; [ apply bmono_bcomp; auto | | apply Hcl'; auto ].
      apply limit_least; intro j.
      eapply ord_le_lt_trans; [ apply (proj1 (Hy j (Hhc j))) | ].
      apply normal_increasing; auto. apply (index_lt (ord Y h) j).
  - transitivity (bach f T (ord Y h)); [ apply (proj2 (Hrep _ Hyc)) | ].
    apply bach_mono_index; auto.
Qed.

Lemma BRep_bsub_equiv f (Hf : forall x y, x ≤ y -> f x ≤ f y) T T' G :
  bsub T T' -> bsub T' T -> bfam T -> bfam T' -> BRep f T G -> BRep f T' G.
Proof.
  intros H1 H2 HT HT' HR.
  apply BRep_extend with T; auto.
  intros k' y Hy.
  destruct (bcomp_bsub f Hf T T' H2 HT k') as [k Hk].
  transitivity (bcomp f T k (G y)); [ apply Hk | ].
  apply HR; auto.
Qed.

(** The power theorem for the canonical trees. *)
Theorem bach_bexpΩ_rep f (Hf : forall x y, x ≤ y -> f x ≤ f y) ζ :
  complete ζ -> forall β G, bfam β -> BRep f β G ->
  forall ξ, complete ξ ->
  BRep f (badd β (bmul (bexpΩ (embed ζ)) (embed ξ))) (schutte_column G (1 + ζ) ξ).
Proof.
  intros Hζ β G Hβ HR ξ Hξ.
  apply BRep_bsub_equiv with (badd β (bmul (bPow ζ) (embed ξ))); auto.
  - apply bsub_badd_r, bsub_bmul_l, (proj1 (bsub_bPow_bexpΩ ζ)).
  - apply bsub_badd_r, bsub_bmul_l, (proj2 (bsub_bPow_bexpΩ ζ)).
  - apply bfam_badd; auto. apply bfam_bmul; auto using bfam_bPow, bfam_embed.
  - apply bfam_badd; auto. apply bfam_bmul; auto using bfam_bexpΩ, bfam_embed.
  - apply bach_bPow_rep; auto.
Qed.

(** φ_{Ω^ζ}(0) is the Schütte column 1+ζ at coefficient 1. *)
Theorem bach_bexpΩ_zero f (Hf : normal_function f) ζ :
  complete ζ -> bach f (bexpΩ (embed ζ)) 0 ≈ schutte_column f (1 + ζ) 1 0.
Proof.
  intro Hζ.
  assert (Hfm : forall x y, x ≤ y -> f x ≤ f y) by (apply normal_monotone; auto).
  assert (HP : bfam (bexpΩ (embed ζ))) by (apply bfam_bexpΩ, bfam_embed).
  assert (HP1 : bfam (bmul (bexpΩ (embed ζ)) (embed 1))) by (apply bfam_bmul; auto using bfam_embed).
  transitivity (bach f (bmul (bexpΩ (embed ζ)) (embed 1)) 0).
  { apply bach_bsub_eq; auto; apply bsub_bmul_one. }
  transitivity (bach f (badd bzero (bmul (bexpΩ (embed ζ)) (embed 1))) 0).
  { symmetry. apply bach_badd_zero_l; auto. }
  apply (bach_bexpΩ_rep f Hfm ζ Hζ bzero f bfam_bzero (bach_zero_rep f Hf) 1 complete_1).
  apply zero_complete.
Qed.
