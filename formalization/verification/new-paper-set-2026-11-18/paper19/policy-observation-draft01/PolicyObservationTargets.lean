module
public import LogicLineages.ControlSensitivityCurrent.PolicyCollisionDefinitions
public import LogicLineages.OrdinalComparison.WWSourceRenamingDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyObservationTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
/-- Actual selected-f expression interpretation; arbitrary ordinal-valued compatible valuations. -/
def ExpressionNaturality : Prop := ∀ (f : Nat → Nat) (Γ Δ : List Ty) (r : Renaming Γ Δ)
  (ν : OrdinalComponent Γ → Ordinal) (μ : OrdinalComponent Δ → Ordinal),
  (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), μ ⟨τ,r x,j⟩ = ν ⟨τ,x,j⟩) →
  ∀ t : OrdinalExpression Γ,
    ParametricSourceSuccessor.denoteWith f μ (ordinalExpressionRename r t) =
      ParametricSourceSuccessor.denoteWith f ν t
/-- Source scalar naturality on the explicit positive-natural coordinate domain. -/
def SourceNaturality : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ Δ : List Ty) (r : Renaming Γ Δ) (ρ : OrdinalComponent Γ → Nat) (σ : OrdinalComponent Δ → Nat),
  (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), σ ⟨τ,r x,j⟩ = ρ ⟨τ,x,j⟩) →
  ∀ t : OriginalTerm Γ .ground,
    PolicyCollision.rawScalar p f σ (t.rename r) = PolicyCollision.rawScalar p f ρ t
/-- Natural observation is raw minus one; positivity pays nontruncation. -/
def ObservationCalibration : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground),
  (PolicyCollision.rawScalar p f ρ t - 1) + 1 = PolicyCollision.rawScalar p f ρ t ∧
  PolicySort.Observation p f ρ t (PolicyCollision.rawScalar p f ρ t - 1)

def EquationCalibration : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b : OriginalTerm Γ .ground),
  PolicyAddition.Equation p f ρ a b ↔ PolicyCollision.rawScalar p f ρ a = PolicyCollision.rawScalar p f ρ b
end LogicLineages.ControlSensitivityCurrent.PolicyObservationTargets
