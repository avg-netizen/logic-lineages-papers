module
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Every successful refusing extraction is exact under every shared ordinal
valuation; the returned normal notation is the executable evaluator's output. -/
def ClosedPositiveEvaluationSound : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (a : ClosedPositive),
    extractPositive t = some a → ∀ ρ : OrdinalComponent Γ → Ordinal,
      a.evaluate.1.repr = denote ρ t

/-- Independently generated positive fields with no occurring components are
all accepted. No evaluator-success premise is used to define this domain. -/
def GeneratedClosedPositiveEvaluationTotal : Prop :=
  ∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ),
    GeneratedOrdinalGrade Γ i t → 0 < i → ordinalExpressionVariables t = [] →
    ∃ a : ClosedPositive, extractPositive t = some a

end LogicLineages.OrdinalComparison.Source.Targets
