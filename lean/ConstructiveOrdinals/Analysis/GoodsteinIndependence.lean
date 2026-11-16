import ConstructiveOrdinals.Analysis.Cichon
import ConstructiveOrdinals.Analysis.Embedding

/-!
# Goodstein's theorem is not provable in Peano arithmetic

Port of `Ordinal/Analysis/GoodsteinIndependence.v`.

If PA proves `∀x ∃y θ(x,y)` with `θ` bounded, then embedding the proof in the
ω-logic, inverting the universal, eliminating the cuts and bounding the
witness give a fixed `α < ε₀` with a witness `y < H_α(x+1)` for every large
`x` (`PA_sigma1_bound`). Goodstein's sequence from `x` takes `H_(o(x))(3) - 3`
steps (`Cichon`), and `o(x)` can be made larger than `α` while `x` stays small
enough that `H_(o(x))(3)` exceeds `H_α(x+1) + 3` (`goodstein_diagonal`). So no
bounded `θ` whose truth at `(x,y)` implies that the sequence from `x` reaches
zero within `y` steps has `∀x ∃y θ` provable in PA (`goodstein_unprovable`).

Lean notes:

- Binary `N` is `Nat`, as in `GoodsteinSequences`; the control `S x` is
  `x + 1`.
-/

namespace ConstructiveOrdinals.GoodsteinIndependence

open Ordinal PeanoArith ATerm Form Hardy VNotation VForm OmegaLogic Embedding Cichon Goodstein

/-! ## The provable Σ₁ sentences are bounded below ε₀ -/

/-- Rocq: `Analysis.GoodsteinIndependence.otower_normal`. -/
theorem otower_normal : ∀ (k : Nat) (a : VForm), IsNormal a → IsNormal (otower k a)
  | 0, _, h => h
  | k + 1, a, h => otower_normal k (V a Z) ⟨h, trivial, trivial⟩

/-- Rocq: `Analysis.GoodsteinIndependence.W_normal`. -/
theorem W_normal (k : Nat) : IsNormal (W k) := normal_vrep e3 Z e3_normal trivial trivial k

/-- Rocq: `Analysis.GoodsteinIndependence.sat_inst2`. -/
theorem sat_inst2 (θ : Form) (x m : Nat) :
    sat ρ0 (sub1 (fsubst (up (inst1 (num x))) (fsubst (up (up (nsub (fun _ => 0)))) θ)) (num m)) ↔
      sat (scons m (scons x ρ0)) θ :=
  (sat_sub1_num ρ0 _ m).trans ((sat_fsubst _ _ _).trans ((sat_fsubst θ _ _).trans (sat_ext θ (fun j => match j with
    | 0 => rfl
    | 1 => by
      show teval (scons m ρ0) (asubst shiftSub (num x)) = x
      rw [teval_shift, teval_num]
    | _ + 2 => rfl))))

theorem max_self (n : Nat) : Nat.max n n = n := Nat.le_antisymm (max_le' (Nat.le_refl n) (Nat.le_refl n)) (Nat.le_max_left n n)

/-- Rocq: `Analysis.GoodsteinIndependence.PA_sigma1_bound`. -/
theorem PA_sigma1_bound (θ : Form) (Hprov : PA [] (all (ex θ))) (HD : isD θ = true) (HE : isD (ex θ) = false) :
    ∃ (α : VForm) (N : Nat), IsNormal α ∧ ∀ x h, N ≤ x → Hardy α (x + 1) h →
      ∃ y, y < h ∧ sat (scons y (scons x ρ0)) θ := by
  obtain ⟨k, ρ, N, hN, Hemb⟩ := embed Hprov
  refine ⟨otower ρ (W k), N, otower_normal ρ _ (W_normal k), fun x h hx Hh => ?_⟩
  have H0 := Hemb (x + 1) (fun _ => 0) (Nat.le_succ_of_le hx) (fun _ => Nat.zero_lt_succ x)
  have H1 : OD (Nat.max (x + 1) (x + 1)) ρ (W k)
      [inst true (ex (fsubst (up (up (nsub (fun _ => 0)))) θ)) x] :=
    od_inv_univ H0 (true, all (ex (fsubst (up (up (nsub (fun _ => 0)))) θ))) true _ [] rfl rfl
      (fun y hy => .inl (match y, hy with | _, .head _ => rfl)) x
  rw [max_self] at H1
  have H2 := od_elim_all ρ (x + 1) (W k) _ (od_rank H1 (Nat.le_succ ρ))
    (Nat.le_trans hN (Nat.le_succ_of_le hx))
  have HD2 : isD (fsubst (up (inst1 (num x))) (fsubst (up (up (nsub (fun _ => 0)))) θ)) = true := by
    rw [isD_fsubst_eq, isD_fsubst_eq]; exact HD
  have HE2 : isD (ex (fsubst (up (inst1 (num x))) (fsubst (up (up (nsub (fun _ => 0)))) θ))) = false := by
    show isD (fsubst (inst1 (num x)) (fsubst (up (nsub (fun _ => 0))) (ex θ))) = false
    rw [isD_fsubst_eq, isD_fsubst_eq]; exact HE
  obtain ⟨m, hm, hs⟩ := od_witness H2 HD2 HE2 Hh
  exact ⟨m, hm, (sat_inst2 θ x m).1 hs⟩

/-! ## Slow growth below fast growth -/

/-- Rocq: `Analysis.GoodsteinIndependence.vval`. -/
def vval (b : Nat) : VForm → Nat
  | Z => 0
  | V e x => b ^ vval b e + vval b x

/-- Rocq: `Analysis.GoodsteinIndependence.vval_vrep`. -/
theorem vval_vrep (b : Nat) (e x : VForm) : ∀ k : Nat, vval b (vrep k e x) = k * b ^ vval b e + vval b x
  | 0 => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | k + 1 => by
    show b ^ vval b e + vval b (vrep k e x) = _
    rw [vval_vrep b e x k, Nat.succ_mul, Nat.add_comm (k * _) (b ^ _), Nat.add_assoc]

/-- Rocq: `Analysis.GoodsteinIndependence.vval_Pn`. -/
theorem vval_Pn {b n : Nat} {a a' : VForm} (hb : 1 ≤ b) (hbn : b ≤ n) (h : Pn n a a') :
    vval b a ≤ vval b a' + 1 := by
  induction h with
  | one => exact Nat.le_refl _
  | tail e x y _ ih =>
    show b ^ vval b e + vval b x ≤ b ^ vval b e + vval b y + 1
    rw [Nat.add_assoc]; exact Nat.add_le_add_left ih _
  | exp e e' y _ _ ih1 ih2 =>
    show b ^ vval b e + 0 ≤ vval b (vrep (n - 1) e' y) + 1
    rw [vval_vrep, Nat.add_zero]
    have ih2' : b ^ vval b e' ≤ vval b y + 1 := ih2
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_one_add_one (Nat.ne_of_gt (Nat.lt_of_lt_of_le hb hbn))).symm⟩
    subst hm
    show b ^ vval b e ≤ m * b ^ vval b e' + vval b y + 1
    calc b ^ vval b e ≤ b ^ (vval b e' + 1) := Nat.pow_le_pow_right hb ih1
      _ = b ^ vval b e' * b := Nat.pow_succ b _
      _ ≤ b ^ vval b e' * (m + 1) := Nat.mul_le_mul_left _ hbn
      _ = m * b ^ vval b e' + b ^ vval b e' := by rw [Nat.mul_succ, Nat.mul_comm]
      _ ≤ m * b ^ vval b e' + (vval b y + 1) := Nat.add_le_add_left ih2' _
      _ = m * b ^ vval b e' + vval b y + 1 := (Nat.add_assoc _ _ _).symm

/-- `H_α(n) ≥ n + G_b(α)` for `b ≤ n`. Rocq: `Analysis.GoodsteinIndependence.hardy_vval`. -/
theorem hardy_vval {b : Nat} {a : VForm} {n h : Nat} (hb : 1 ≤ b) (hbn : b ≤ n) (H : Hardy a n h) :
    n + vval b a ≤ h := by
  induction H with
  | z n => exact Nat.le_refl _
  | p a a1 n h ha1 _ ih =>
    have ih' := ih (Nat.le_succ_of_le hbn)
    have hv := vval_Pn hb hbn ha1
    calc n + vval b a ≤ n + (vval b a1 + 1) := Nat.add_le_add_left hv n
      _ = n + 1 + vval b a1 := by rw [Nat.add_comm (vval b a1) 1, Nat.add_assoc]
      _ ≤ h := ih'

/-- Rocq: `Analysis.GoodsteinIndependence.VF_size_vval`. -/
theorem VF_size_vval : ∀ a : VForm, size a ≤ vval 2 a
  | Z => Nat.le_refl 0
  | V e x => by
    show size e + size x + 1 ≤ 2 ^ vval 2 e + vval 2 x
    rw [Nat.add_right_comm]
    exact Nat.add_le_add (Nat.le_trans (Nat.succ_le_succ (VF_size_vval e)) (pow2_ge _)) (VF_size_vval x)

/-! ## Hereditary base-2 notation for powers of two -/

/-- Rocq: `Analysis.GoodsteinIndependence.hbn_vval`. -/
theorem hbn_vval : ∀ h : HBN, vval 2 (hbnVf h) = hbnInterp 2 h
  | .z => rfl
  | .term e n x => by
    show vval 2 (vrep n (hbnVf e) (hbnVf x)) = 2 ^ hbnInterp 2 e * n + hbnInterp 2 x
    rw [vval_vrep, hbn_vval e, hbn_vval x, Nat.mul_comm]

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_vval`. -/
theorem ord2_vval (t : Nat) : vval 2 (ord2 t) = t := (hbn_vval _).trans (hbn_decompose_correct _ _ t)

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_pow`. -/
theorem ord2_pow (t : Nat) : ord2 (2 ^ t) = V (ord2 t) Z := by
  unfold ord2
  rw [hbn_decompose_unique 2 (plus2_base 0) (2 ^ t) (.term (hbnDecompose 2 (plus2_base 0) t) 1 .z)
    (.term (hbn_decompose_proper _ _ _) ⟨Nat.zero_lt_one, by decide⟩ .z (.z _))
    (by show 2 ^ hbnInterp 2 (hbnDecompose 2 (plus2_base 0) t) * 1 + 0 = 2 ^ t
        rw [hbn_decompose_correct, Nat.mul_one]; rfl)]
  rfl

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_pow_succ`. -/
theorem ord2_pow_succ (t : Nat) (ht : 0 < t) : ord2 (2 ^ t + 1) = V (ord2 t) (V Z Z) := by
  unfold ord2
  have hlt : HbnLt .z (hbnDecompose 2 (plus2_base 0) t) := by
    cases e : hbnDecompose 2 (plus2_base 0) t with
    | z => exact absurd (hbn_decompose_zero _ _ _ e) (Nat.ne_of_gt ht)
    | term _ _ _ => exact .z _ _ _
  rw [hbn_decompose_unique 2 (plus2_base 0) (2 ^ t + 1)
    (.term (hbnDecompose 2 (plus2_base 0) t) 1 (.term .z 1 .z))
    (.term (hbn_decompose_proper _ _ _) ⟨Nat.zero_lt_one, by decide⟩
      (.term .z ⟨Nat.zero_lt_one, by decide⟩ .z (.z _)) (.term 1 .z hlt))
    (by show 2 ^ hbnInterp 2 (hbnDecompose 2 (plus2_base 0) t) * 1 + (2 ^ 0 * 1 + 0) = 2 ^ t + 1
        rw [hbn_decompose_correct, Nat.mul_one])]
  rfl

/-- The tower `1, 2, 2^2, …`. Rocq: `Analysis.GoodsteinIndependence.tw`. -/
def tw : Nat → Nat
  | 0 => 1
  | j + 1 => 2 ^ tw j

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_tw`. -/
theorem ord2_tw : ∀ j : Nat, ord2 (tw j) = V (match j with | 0 => Z | j + 1 => ord2 (tw j)) Z
  | 0 => by
    show ord2 (2 ^ 0) = V Z Z
    rw [ord2_pow]
    show V (hbnVf (hbnDecompose 2 (plus2_base 0) 0)) Z = V Z Z
    rw [decompose_zero]; rfl
  | j + 1 => ord2_pow (tw j)

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_tw_normal`. -/
theorem ord2_tw_normal : ∀ j : Nat, IsNormal (ord2 (tw j))
  | 0 => by rw [ord2_tw]; exact ⟨trivial, trivial, trivial⟩
  | j + 1 => by rw [ord2_tw]; exact ⟨ord2_tw_normal j, trivial, trivial⟩

/-- Rocq: `Analysis.GoodsteinIndependence.tw_pos`. -/
theorem tw_pos : ∀ j : Nat, 0 < tw j
  | 0 => Nat.zero_lt_one
  | _ + 1 => Nat.pow_pos (Nat.zero_lt_succ 1)

/-- Rocq: `Analysis.GoodsteinIndependence.tw_ge`. -/
theorem tw_ge : ∀ j : Nat, j ≤ tw j
  | 0 => Nat.zero_le _
  | j + 1 => Nat.le_trans (Nat.succ_le_succ (tw_ge j)) (pow2_ge (tw j))

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_tw_lt_S`. -/
theorem ord2_tw_lt_S (j : Nat) : sz (ord2 (tw j)) < sz (ord2 (tw (j + 1))) := by
  rw [ord2_tw (j + 1)]; exact exp_shrink _

/-- Rocq: `Analysis.GoodsteinIndependence.ord2_tw_mono`. -/
theorem ord2_tw_mono {j j' : Nat} (h : j ≤ j') : sz (ord2 (tw j)) ≤ sz (ord2 (tw j')) := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (le_of_lt (ord2_tw_lt_S _))

/-- The towers are cofinal in the normal forms. Rocq: `Analysis.GoodsteinIndependence.tw_cofinal`. -/
theorem tw_cofinal : ∀ a : VForm, IsNormal a → ∃ j, sz a < sz (ord2 (tw j))
  | Z, _ => ⟨0, by rw [ord2_tw]; exact Z_lt_V _ _⟩
  | V e x, ha =>
    let ⟨j, hj⟩ := tw_cofinal e ha.1
    ⟨j + 1, by rw [ord2_tw (j + 1)]; exact normal_lead_lt x e _ ha hj⟩

/-- Rocq: `Analysis.GoodsteinIndependence.e1_le_V`. -/
theorem e1_le_V (a x : VForm) : sz e1 ≤ sz (V a x) :=
  le_trans (le_trans (VZ_eq Z).le (le_trans (pow_le_pow_right ω (zero_least _)) (VZ_eq a).ge)) (exp_le_V a x)

/-! ## The diagonal argument -/

/-- Rocq: `Analysis.GoodsteinIndependence.hardy_lt_arg`. -/
theorem hardy_lt_arg (a : VForm) {n n' m m' : Nat} (hn : n < n') (hm : Hardy a n m) (hm' : Hardy a n' m') : m < m' := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hn
  clear hn
  induction d generalizing m' with
  | zero => exact (hardy_mono a).1 n m m' hm hm'
  | succ d ih =>
    obtain ⟨k, hk⟩ := hardy_exists a (n + 1 + d)
    exact Nat.lt_trans (ih hk) ((hardy_mono a).1 _ k m' hk hm')

/-- Rocq: `Analysis.GoodsteinIndependence.hardy_add_arg`. -/
theorem hardy_add_arg (a : VForm) {n m m' : Nat} : ∀ d, Hardy a n m → Hardy a (n + d) m' → m + d ≤ m'
  | 0, hm, hm' => Nat.le_of_eq (hardy_fun hm hm')
  | d + 1, hm, hm' => by
    obtain ⟨k, hk⟩ := hardy_exists a (n + d)
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (hardy_add_arg a d hm hk) (hardy_lt_arg a (Nat.lt_succ_self _) hk hm'))

/-- Rocq: `Analysis.GoodsteinIndependence.hardy_omega`. -/
theorem hardy_omega (u : Nat) (hu : 1 ≤ u) : Hardy (V e1 Z) u (2 * u) := hardy_omega_k 1 u hu

theorem le_pow2_self (t : Nat) : t ≤ 2 ^ t := Nat.le_trans (Nat.le_succ t) (pow2_ge t)

theorem Pn3_Z {e : VForm} (h : Pn 3 (V e Z) Z) : e = Z := by
  cases h with
  | one => rfl

/-- Rocq: `Analysis.GoodsteinIndependence.goodstein_diagonal`. -/
theorem goodstein_diagonal (α : VForm) (M : Nat) (hα : IsNormal α) :
    ∃ x, M ≤ x ∧ ∀ h h', Hardy α (x + 1) h → Hardy (ord2 x) 3 h' → h + 3 < h' := by
  obtain ⟨j0, hj0⟩ := tw_cofinal α hα
  let j := Nat.max j0 (M + size α)
  let t := tw j
  let τ := ord2 t
  have hτn : IsNormal τ := ord2_tw_normal j
  have hατ : sz α < sz τ := lt_of_lt_of_le hj0 (ord2_tw_mono (Nat.le_max_left _ _))
  have ht : M + size α ≤ t := Nat.le_trans (Nat.le_max_right _ _) (tw_ge j)
  have htv : vval 2 τ = t := ord2_vval t
  have hτsz : size τ ≤ t := htv ▸ VF_size_vval τ
  let z := 2 ^ t
  let x := 2 ^ (z + 1)
  have hx : ord2 x = V (V τ (V Z Z)) Z := by
    show ord2 (2 ^ (2 ^ t + 1)) = _
    rw [ord2_pow, ord2_pow_succ t (tw_pos j)]
  have htz : t ≤ z := le_pow2_self t
  have hzx : 2 ^ z + 2 ^ z = x := by show _ = 2 ^ (z + 1); rw [Nat.pow_succ, Nat.mul_two]
  refine ⟨x, Nat.le_trans (Nat.le_add_right M (size α)) (Nat.le_trans ht (Nat.le_trans htz
    (Nat.le_trans (le_pow2_self z) (hzx ▸ Nat.le_add_right _ _)))), fun h h' Hh Hh' => ?_⟩
  rw [hx] at Hh'
  let ζ0 := V τ Z
  obtain ⟨y, hy⟩ := Pn_exists_exp 3 ζ0
  have Hstep : Pn 3 (V (V τ (V Z Z)) Z) (vrep 2 ζ0 y) := .exp _ ζ0 y (.tail τ (V Z Z) Z .one) hy
  have Hh'' : Hardy (vcat (V ζ0 Z) (vcat (V ζ0 Z) y)) 4 h' := hardy_P_inv Hstep Hh'
  obtain ⟨b, Hb, Hh3⟩ := hardy_vcat_inv _ _ Hh''
  obtain ⟨a, Ha, Hb'⟩ := hardy_vcat_inv _ _ Hb
  have hyZ : y ≠ Z := fun e => VForm.noConfusion (Pn3_Z (e ▸ hy))
  have Ha4 : 4 < a := hardy_gt Ha hyZ
  obtain ⟨u, Hu⟩ := hardy_exists (V ζ0 Z) 4
  have Hub : u < b := hardy_lt_arg (V ζ0 Z) Ha4 Hu Hb'
  have Hu_ge : 4 + 2 ^ z ≤ u := by
    have hv := hardy_vval (b := 2) (by decide) (by decide) Hu
    have e : vval 2 (V ζ0 Z) = 2 ^ z := by
      show 2 ^ (2 ^ vval 2 τ + 0) + 0 = 2 ^ z
      rw [htv]; rfl
    rw [e] at hv
    exact hv
  -- the chain `H_α(x+1) + 3 ≤ H_α(2u) ≤ H_(ω^τ)(2u) = H_(ω^τ+ω)(u) ≤ H_(ω^ζ0)(u) < h'`
  have hu1 : 1 ≤ u := Nat.le_trans (by decide : 1 ≤ 4) (Nat.le_trans (Nat.le_add_right 4 _) Hu_ge)
  have hz2u : 2 ^ z < u := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (by decide)) Hu_ge
  have htu : t < u := Nat.lt_of_le_of_lt (Nat.le_trans htz (le_pow2_self z)) hz2u
  obtain ⟨h3, Hh3'⟩ := hardy_exists α (x + 1 + 3)
  have E1 : h + 3 ≤ h3 := hardy_add_arg α 3 Hh Hh3'
  obtain ⟨h4, Hh4⟩ := hardy_exists α (2 * u)
  have hx2u : x + 1 + 3 ≤ 2 * u := by
    rw [← hzx, Nat.two_mul]
    show 2 ^ z + 2 ^ z + 4 ≤ u + u
    calc 2 ^ z + 2 ^ z + 4 ≤ 2 ^ z + 2 ^ z + 4 + 4 := Nat.le_add_right _ _
      _ = (4 + 2 ^ z) + (4 + 2 ^ z) := by
        rw [Nat.add_comm 4 (2 ^ z), Nat.add_assoc (2 ^ z) 4 (2 ^ z + 4), Nat.add_comm 4 (2 ^ z + 4),
          Nat.add_assoc (2 ^ z) (2 ^ z) (4 + 4), Nat.add_assoc (2 ^ z) 4 4]
      _ ≤ u + u := Nat.add_le_add Hu_ge Hu_ge
  have E2 : h3 ≤ h4 := hardy_mono_arg α hx2u Hh3' Hh4
  obtain ⟨h5, Hh5⟩ := hardy_exists (V τ Z) (2 * u)
  have hsizeα : size α < 2 * u :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ M) ht) htu) (Nat.le_mul_of_pos_left u (by decide))
  have E3 : h4 ≤ h5 := hardy_dominated (b := V τ Z) hα ⟨hτn, trivial, trivial⟩ (lt_trans hατ (exp_shrink τ)) hsizeα Hh4 Hh5
  have Hc : Hardy (V τ (V e1 Z)) u h5 := hardy_vcat (V τ Z) (hardy_omega u hu1) Hh5
  obtain ⟨h6, Hh6⟩ := hardy_exists (V ζ0 Z) u
  have hnorm : IsNormal (V τ (V e1 Z)) := ⟨hτn, ⟨e1_normal, trivial, trivial⟩, by
    show sz e1 ≤ sz (ord2 (tw j))
    rw [ord2_tw]; exact e1_le_V _ _⟩
  have hsize : size (V τ (V e1 Z)) < u := by
    show size τ + 3 < u
    calc size τ + 3 ≤ t + 3 := Nat.add_le_add_right hτsz 3
      _ ≤ 2 ^ z + 3 := Nat.add_le_add_right (Nat.le_trans htz (le_pow2_self z)) 3
      _ < 2 ^ z + 4 := Nat.lt_succ_self _
      _ = 4 + 2 ^ z := Nat.add_comm _ _
      _ ≤ u := Hu_ge
  have E4 : h5 ≤ h6 := hardy_dominated (b := V ζ0 Z) hnorm ⟨⟨hτn, trivial, trivial⟩, trivial, trivial⟩
    (normal_lead_lt _ τ ζ0 hnorm (exp_shrink τ)) hsize Hc Hh6
  have E5 : h6 < h' := hardy_lt_arg (V ζ0 Z) Hub Hh6 Hh3
  exact Nat.lt_of_le_of_lt (Nat.le_trans E1 (Nat.le_trans E2 (Nat.le_trans E3 (Nat.le_trans E4 (Nat.le_refl _))))) E5

/-! ## Unprovability -/

/-- Rocq: `Analysis.GoodsteinIndependence.goodstein_unprovable`. -/
theorem goodstein_unprovable (θ : Form) (HD : isD θ = true) (HE : isD (ex θ) = false)
    (Hsound : ∀ x y, sat (scons y (scons x ρ0)) θ → ∃ k, k ≤ y ∧ goodsteinSequence x k = 0) :
    ¬ PA [] (all (ex θ)) := by
  intro Hprov
  obtain ⟨α, N, hα, Hbound⟩ := PA_sigma1_bound θ Hprov HD HE
  obtain ⟨x, hx, Hdiag⟩ := goodstein_diagonal α N hα
  obtain ⟨h, Hh⟩ := hardy_exists α (x + 1)
  obtain ⟨h', Hh'⟩ := hardy_exists (ord2 x) 3
  obtain ⟨y, hy, hsat⟩ := Hbound x h hx Hh
  obtain ⟨k, hk, hg⟩ := Hsound x y hsat
  have hlow := goodstein_length_lower x k h' hg Hh'
  have hd := Hdiag h h' Hh Hh'
  exact absurd (Nat.lt_of_lt_of_le hd (Nat.le_trans hlow (Nat.add_le_add_right (Nat.le_trans hk (Nat.le_of_lt hy)) 3)))
    (Nat.lt_irrefl _)

end ConstructiveOrdinals.GoodsteinIndependence
