module
public import LogicLineages.ControlSensitivityCurrent.FullCollisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.FullAggregate.Targets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PolicyCollision SourceAggregateCompletion
/-- Uniform actual source-code reconstruction and all-policy shared-valuation conjunction semantics. -/
def CompleteAggregate : Prop :=
  SourceGammaAggregateCode.Targets.ExactLiteralCodes ∧
  SourceGammaAggregateCode.Targets.ExactAggregateCode ∧
  SourceGammaAggregateCode.Targets.UniformPrimitiveRecursive ∧
  ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
    rawScalar p f ρ (aggregate es).2 ≤ rawScalar p f ρ (aggregate es).1 ∧
    (rawScalar p f ρ (aggregate es).1 = rawScalar p f ρ (aggregate es).2 ↔
      ∀ e ∈ es, rawScalar p f ρ e.1 = rawScalar p f ρ e.2) ∧
    (¬ (∀ e ∈ es, rawScalar p f ρ e.1 = rawScalar p f ρ e.2) →
      2 ≤ rawScalar p f ρ (aggregate es).1 - rawScalar p f ρ (aggregate es).2)
end LogicLineages.ControlSensitivityCurrent.FullAggregate.Targets
