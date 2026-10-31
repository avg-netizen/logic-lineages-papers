module
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitObservation.Targets
open OriginalDomain

def PositiveValue : Prop := ∀ n : Nat, closedValue (positive n) = ((n+1 : Nat) : Ordinal)

def GroundValue : Prop := ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (x : Variable Γ .ground),
  (substitution ρ).vector x 0 = positive (ρ x) ∧
    valuation (substitution ρ) ⟨.ground,x,0⟩ = ((ρ x+1 : Nat) : Ordinal)

def FunctionalCoordinates : Prop := ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (σ : Ty), 0 < σ.level → ∀ (x : Variable Γ σ) (j : Fin (σ.level+1)),
  (substitution ρ).vector x j = .one

/-- Literal closed expressions agree coordinate by coordinate, not merely
scalar values or independently chosen copies of the remaining vectors. -/
def SelectedTransport : Prop := ∀ (left right : List Ty) (σ : Ty), 0 < σ.level →
  ∀ (ρ : Variable (left ++ σ :: right) .ground → Nat)
    (τ : Ty) (x : Variable (left ++ σ :: right) τ) (j : Fin (τ.level+1)),
  (OneUnit.unitExtension (σ := σ) (substitution (remainingInputs left right σ ρ))).vector
    (SelectedBinder.moveToHead left right σ x) j = (substitution ρ).vector x j

/-- Exactly the selected-name valuation used by the source one-unit theorem,
with the genuine residual admissible substitution, equals the original unit
observation at every component, including ordinal-valued coordinate types. -/
def SelectedValuation : Prop := ∀ (left right : List Ty) (σ : Ty), 0 < σ.level →
  ∀ ρ : Variable (left ++ σ :: right) .ground → Nat,
  OneUnit.selectedValuation (σ := σ) (substitution (remainingInputs left right σ ρ)) =
    valuation (substitution ρ)
end LogicLineages.OrdinalComparison.Source.UnitObservation.Targets
