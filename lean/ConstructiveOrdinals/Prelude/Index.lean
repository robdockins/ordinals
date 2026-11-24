import ConstructiveOrdinals.Prelude.Nat

/-!
# Arithmetic on de Bruijn indices

Two recursive functions on indices: `sv c y`, the index of `y` after the
variables `≥ c` are shifted up, and `svar x y`, what substituting for `x` does
to `y` (`none` if `y = x`). They agree with the `if` forms used in the
definitions (`sv_eq`, `svar_spec`), and their lemmas are proved by structural
induction, without the linear-arithmetic tactics (which use `propext`).
-/

namespace ConstructiveOrdinals.Index


/-- The index of variable `y` after shifting the variables `≥ c`. -/
def sv : Nat → Nat → Nat
  | 0, y => y + 1
  | _ + 1, 0 => 0
  | c + 1, y + 1 => sv c y + 1

theorem sv_eq : ∀ c y : Nat, (if y < c then y else y + 1) = sv c y
  | 0, y => ite_eq_right (Nat.not_lt_zero y)
  | c + 1, 0 => ite_eq_left (Nat.zero_lt_succ c)
  | c + 1, y + 1 => by
    show _ = sv c y + 1
    rw [← sv_eq c y]
    by_cases h : y < c
    · rw [ite_eq_left (Nat.succ_lt_succ h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (Nat.lt_of_succ_lt_succ h')), ite_eq_right h]

/-- What substituting for variable `x` does to variable `y`: `none` if it is
`x`, otherwise its new index. -/
def svar : Nat → Nat → Option Nat
  | 0, 0 => none
  | 0, y + 1 => some y
  | _ + 1, 0 => some 0
  | x + 1, y + 1 => (svar x y).map (· + 1)

theorem svar_spec : ∀ x y : Nat, svar x y = if y = x then none else some (if y < x then y else y - 1)
  | 0, 0 => (ite_eq_left rfl).symm
  | 0, y + 1 => by
    rw [ite_eq_right (fun h => Nat.noConfusion h), ite_eq_right (Nat.not_lt_zero _)]; rfl
  | x + 1, 0 => by
    rw [ite_eq_right (fun h => Nat.noConfusion h), ite_eq_left (Nat.zero_lt_succ x)]; rfl
  | x + 1, y + 1 => by
    show (svar x y).map (· + 1) = _
    rw [svar_spec x y]
    by_cases h : y = x
    · rw [ite_eq_left h, ite_eq_left (congrArg (· + 1) h)]; rfl
    · rw [ite_eq_right h, ite_eq_right (fun e => h (Nat.succ.inj e))]
      by_cases h' : y < x
      · rw [ite_eq_left h', ite_eq_left (Nat.succ_lt_succ h')]; rfl
      · rw [ite_eq_right h', ite_eq_right (fun e => h' (Nat.lt_of_succ_lt_succ e))]
        have hy : 1 ≤ y := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h') (fun e => h e.symm) |>
          fun hlt => Nat.lt_of_le_of_lt (Nat.zero_le x) hlt
        show some (y - 1 + 1) = some (y + 1 - 1)
        rw [Nat.sub_add_cancel hy]; rfl

theorem map_succ_some {o : Option Nat} {z : Nat} (h : o.map (· + 1) = some z) :
    ∃ z0, o = some z0 ∧ z = z0 + 1 := by
  cases o with
  | none => cases h
  | some z0 => cases h; exact ⟨z0, rfl, rfl⟩

theorem sv_sv : ∀ {X Y : Nat} (Z : Nat), X ≤ Y → sv X (sv Y Z) = sv (Y + 1) (sv X Z)
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, 0, _ => rfl
  | _ + 1, _ + 1, Z + 1, h => congrArg (· + 1) (sv_sv Z (Nat.le_of_succ_le_succ h))

theorem svar_sv : ∀ X Z : Nat, svar X (sv X Z) = some Z
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | X + 1, Z + 1 => by show (svar X (sv X Z)).map (· + 1) = _; rw [svar_sv X Z]; rfl

theorem svar_sv_le : ∀ {X Y : Nat} (Z : Nat), X ≤ Y → svar (Y + 1) (sv X Z) = (svar Y Z).map (sv X)
  | 0, Y, Z, _ => by
    show (svar Y Z).map (· + 1) = _
    cases svar Y Z <;> rfl
  | _ + 1, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, 0, _ => rfl
  | X + 1, Y + 1, Z + 1, h => by
    show (svar (Y + 1) (sv X Z)).map (· + 1) = ((svar Y Z).map (· + 1)).map (sv (X + 1))
    rw [svar_sv_le Z (Nat.le_of_succ_le_succ h)]
    cases svar Y Z <;> rfl

theorem svar_sv_ge : ∀ {X Y : Nat} (Z : Nat), Y ≤ X → svar Y (sv (X + 1) Z) = (svar Y Z).map (sv X)
  | _, 0, 0, _ => rfl
  | X, 0, Z + 1, _ => by
    show (svar 0 (sv X Z + 1)) = _
    rfl
  | 0, _ + 1, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, _ + 1, 0, _ => rfl
  | X + 1, Y + 1, Z + 1, h => by
    show (svar Y (sv (X + 1) Z)).map (· + 1) = ((svar Y Z).map (· + 1)).map (sv (X + 1))
    rw [svar_sv_ge Z (Nat.le_of_succ_le_succ h)]
    cases svar Y Z <;> rfl

theorem svar_self : ∀ X : Nat, svar X X = none
  | 0 => rfl
  | X + 1 => by show (svar X X).map (· + 1) = none; rw [svar_self X]; rfl

theorem svar_lt : ∀ {Z X : Nat}, Z < X → svar X Z = some Z
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | Z + 1, X + 1, h => by
    show (svar X Z).map (· + 1) = _
    rw [svar_lt (Nat.lt_of_succ_lt_succ h)]; rfl

theorem svar_none : ∀ {X Z : Nat}, svar X Z = none → Z = X
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | X + 1, Z + 1, h => by
    have h' : (svar X Z).map (· + 1) = none := h
    cases e : svar X Z with
    | none => exact congrArg (· + 1) (svar_none e)
    | some _ => rw [e] at h'; cases h'

theorem svar_ge {X Z z : Nat} (h : svar X Z = some z) (hz : X ≤ z) : Z = z + 1 := by
  induction X generalizing Z z with
  | zero =>
    cases Z with
    | zero => cases h
    | succ Z => cases h; rfl
  | succ X ih =>
    cases Z with
    | zero => cases h; exact absurd hz (Nat.not_succ_le_zero _)
    | succ Z =>
      obtain ⟨z0, h0, rfl⟩ := map_succ_some h
      exact congrArg (· + 1) (ih h0 (Nat.le_of_succ_le_succ hz))

theorem svar_comp {X Y : Nat} (hXY : X ≤ Y) {Z z w : Nat} (h1 : svar X Z = some z) (h2 : svar Y z = some w) :
    ∃ w', svar (Y + 1) Z = some w' ∧ svar X w' = some w := by
  induction X generalizing Y Z z w with
  | zero =>
    cases Z with
    | zero => cases h1
    | succ Z =>
      have e : Z = z := Option.some.inj h1
      subst e
      exact ⟨w + 1, by show (svar Y Z).map (· + 1) = _; rw [h2]; rfl, rfl⟩
  | succ X ih =>
    cases Y with
    | zero => exact absurd hXY (Nat.not_succ_le_zero _)
    | succ Y =>
      cases Z with
      | zero =>
        cases h1; cases h2
        exact ⟨0, rfl, rfl⟩
      | succ Z =>
        obtain ⟨z0, h0, rfl⟩ := map_succ_some h1
        obtain ⟨w0, hw0, rfl⟩ := map_succ_some h2
        obtain ⟨w0', e1, e2⟩ := ih (Nat.le_of_succ_le_succ hXY) h0 hw0
        exact ⟨w0' + 1, by show (svar (Y + 1) Z).map (· + 1) = _; rw [e1]; rfl,
          by show (svar X w0').map (· + 1) = _; rw [e2]; rfl⟩

end ConstructiveOrdinals.Index
