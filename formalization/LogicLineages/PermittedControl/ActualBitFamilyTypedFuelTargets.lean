module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialStepTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyTypedFuel
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyExistentialLow (Satisfiable closed)
open ActualBitFamilyLowSlices (dimension)
open ActualBitFamilyExistentialStep (Layer layer)

/-- Typed logical recursion only. The existing route syntax, finite named
support and candidate tests are noncomputable in this implementation. -/
noncomputable def fuel (f : Nat → Nat) (B : Nat) : Nat → Family → Bool
  | 0, family => if dimension family = 0 then closed family else false
  | n+1, family =>
    match layer f B family with
    | .closed b => b
    | .descend xs => xs.any (fuel f B n)

noncomputable def solve (f : Nat → Nat) (B : Nat) (family : Family) : Bool :=
  fuel f B (dimension family) family

def ExactTypedFuelSound : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (n : Nat) (family : Family), fuel f B n family = true → Satisfiable f family

def ExactTypedFuelComplete : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (n : Nat) (family : Family), dimension family ≤ n → Satisfiable f family → fuel f B n family = true

def ExactTypedFamilySolve : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ family : Family, (solve f B family = true ↔ Satisfiable f family) ∧
      (solve f B family = false ↔ ¬ Satisfiable f family)

def FullActualBitFamilyTypedFuel : Prop :=
  ExactTypedFuelSound ∧ ExactTypedFuelComplete ∧ ExactTypedFamilySolve

end LogicLineages.PermittedControl.ActualBitFamilyTypedFuel
