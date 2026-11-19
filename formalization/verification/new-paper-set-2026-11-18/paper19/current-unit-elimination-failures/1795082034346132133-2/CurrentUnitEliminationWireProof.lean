module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationProjectionProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open ExistentialPlan

/-- Form one assignment using a given prefix and an independently specified
base. Only the intended witness prefix is copied. -/
def fillPrefix {Γ Δ : List Ty} :
    (n : Nat) → (Variable (WireCtx n Γ) .ground → Nat) → (Variable Δ .ground → Nat) →
      Variable (WireCtx n Δ) .ground → Nat
  | 0,_,ρ,x => ρ x
  | _+1,v,_,.here => v .here
  | n+1,v,ρ,.there x => fillPrefix n (fun z => v (.there z)) ρ x

theorem fillShift {Γ Δ : List Ty} (n : Nat)
    (v : Variable (WireCtx n Γ) .ground → Nat) (ρ : Variable Δ .ground → Nat) (x : Variable Δ .ground) :
    fillPrefix n v ρ (shift n x) = ρ x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun z => v (.there z))

theorem fillUnder {Γ Δ Θ : List Ty} (n : Nat) (r : Renaming Γ Δ)
    (v : Variable (WireCtx n Θ) .ground → Nat) (ρ : Variable Δ .ground → Nat) :
    ∀ x : Variable (WireCtx n Γ) .ground,
      fillPrefix n v ρ (under r n x) = fillPrefix n v (fun y => ρ (r y)) x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    cases x with
    | here => rfl
    | there x => exact ih (fun z => v (.there z)) x

theorem fillSelf {Γ : List Ty} (n : Nat) (v : Variable (WireCtx n Γ) .ground → Nat) :
    fillPrefix n v (fun x => v (shift n x)) = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    cases x with
    | here => rfl
    | there x => exact congrFun (ih (fun z => v (.there z))) x

theorem fillReset {Γ Δ Θ : List Ty} (n : Nat)
    (v : Variable (WireCtx n Γ) .ground → Nat) (μ : Variable Δ .ground → Nat)
    (ν : Variable Θ .ground → Nat) :
    fillPrefix n (fillPrefix n v μ) ν = fillPrefix n v ν := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    cases x with
    | here => rfl
    | there x => exact congrFun (ih (fun z => v (.there z))) x

theorem reroutePull {Γ Δ : List Ty} (n : Nat) (r : Renaming (WireCtx n Γ) Δ)
    (z : Variable Δ .ground) (ω : Variable Δ .ground → Nat) :
    (fun x => ω (reroute n r z x)) =
      fillPrefix n (fun x => ω (r x)) (extend (fun x => ω (r (shift n x))) (ω z)) := by
  induction n with
  | zero =>
    funext x
    cases x <;> rfl
  | succ n ih =>
    funext x
    cases x with
    | here => rfl
    | there x => exact congrFun (ih (fun w => r (.there w))) x

theorem pullShiftUnder {Γ Δ : List Ty} (n : Nat) (r : Renaming Γ Δ) (x : Variable Γ .ground) :
    under r n (shift n x) = shift n (r x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Variable.there ih

theorem prefixReduction {Γ : List Ty} (n : Nat) (v : Variable (WireCtx n Γ) .ground → Nat)
    (ρ : Variable Γ .ground → Nat) (h : ∀ x, v (shift n x) = ρ x) :
    fillPrefix n v ρ = v := by
  have e : ρ = fun x => v (shift n x) := (funext h).symm
  rw [e]
  exact fillSelf n v

private theorem indexInjective {Γ : List Ty} {τ : Ty} (x : Variable Γ τ) :
    ∀ y : Variable Γ τ,
      RawSourceDAG.variableIndex x = RawSourceDAG.variableIndex y → x=y := by
  induction x with
  | here =>
    intro y h
    cases y with
    | here => rfl
    | there y => simp only [RawSourceDAG.variableIndex] at h; omega
  | there x ih =>
    intro y h
    cases y with
    | here => simp only [RawSourceDAG.variableIndex] at h; omega
    | there y =>
      apply congrArg Variable.there
      apply ih y
      exact Nat.add_right_cancel h

private theorem indexCast {Γ Δ : List Ty} (h : Γ = Δ) (x : Variable Γ .ground) :
    RawSourceDAG.variableIndex (castGround h x) = RawSourceDAG.variableIndex x := by
  cases h
  rfl

private theorem indexShift {Γ : List Ty} (n : Nat) (x : Variable Γ .ground) :
    RawSourceDAG.variableIndex (shift n x) = RawSourceDAG.variableIndex x + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change RawSourceDAG.variableIndex (shift n x) + 1 = _
    rw [ih]
    omega

theorem shiftCastTwo {Γ : List Ty} (m n : Nat) (x : Variable Γ .ground) :
    castGround (congrArg (fun C => .ground :: .ground :: C) (wireCtx_add m n Γ).symm)
        (.there (.there (shift m (shift n x)))) =
      (.there (.there (shift (m+n) x)) : Variable (WireCtx ((m+n)+2) Γ) .ground) := by
  apply indexInjective
  simp only [indexCast,RawSourceDAG.variableIndex,indexShift]
  omega

theorem castGround_left_inverse {Γ Δ} (h : Γ = Δ) (x : Variable Γ .ground) :
    castGround h.symm (castGround h x) = x := by
  cases h
  rfl

theorem castGround_right_inverse {Γ Δ} (h : Γ = Δ) (x : Variable Δ .ground) :
    castGround h (castGround h.symm x) = x := by
  cases h
  rfl

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
