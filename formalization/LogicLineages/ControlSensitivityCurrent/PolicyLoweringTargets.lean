module
public import LogicLineages.ControlSensitivityCurrent.PolicyLoweringDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyLoweringTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering
def ExpressionCalibration : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat),
  StrictMono f → (∀ n : Nat, n ≤ f n) → ∀ (Γ : List Ty)
  (ρ : OrdinalComponent Γ → Nat) (e : Expr Γ),
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment p e.term = some v ∧
    ParametricSourceSuccessor.denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) =
      ((PolicyLowering.numericValue f ρ e+1 : Nat) : Ordinal)
def SharedInputsAndSyntax : Prop := PrimitiveLowering.Targets.SharedInputs ∧
  PrimitiveLowering.Targets.PrimitiveRealization
/-- Every gate including sort, every policy, same nine shared witnesses and literal forest. -/
def AllGateExact : Prop := ∀ f : Nat → Nat, FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
  (g : Gate Γ) (z : Fin 9 → Nat),
  (PolicyLowering.SourceHolds p f ρ g z ↔ g.Holds ρ ∧ z = PolicyLowering.canonicalWitness f ρ g) ∧
  (PolicyLowering.ForestHolds p f ρ g z ↔ g.Holds ρ ∧ z = PolicyLowering.canonicalWitness f ρ g)
def ActualFixedSize : Prop := PrimitiveLowering.Targets.FixedSize
end LogicLineages.ControlSensitivityCurrent.PolicyLoweringTargets
