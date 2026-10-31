module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-! Ordinary semantic closure below the calibrated epsilon zero. The first
supplier holds for all below-epsilon-zero valuations; the source-facing
corollaries derive that premise from actual closed B-vector substitutions,
rather than postulating it as a new weak-scalar hypothesis. -/
def OrdinalExpressionValueBelowEpsilonZero : Prop :=
  ∀ (ι : Type) (ρ : ι → Ordinal.{0}), (∀ x, ρ x < epsilonZero) →
    ∀ t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι,
      denote ρ t < epsilonZero

def OriginalClosedValueBelowEpsilonZero : Prop :=
  ∀ t : ClosedExpression, closedValue t < epsilonZero

def OriginalAdmissibleValueBelowEpsilonZero : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (x : OrdinalComponent Γ),
    valuation ρ x < epsilonZero

def OriginalExpressionValueBelowEpsilonZero : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (t : OrdinalExpression Γ),
    expressionValue ρ t < epsilonZero

end LogicLineages.OrdinalComparison.Source.Targets
