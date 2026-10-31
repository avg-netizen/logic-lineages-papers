module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

/-! Actual positivity of the original zero-free B/C domains, rather than an
assumption bundled into admissible valuations. This pays B>=1 in the repaired
bounded-norm argument; it does not prove that argument. -/
def OriginalClosedGradePositive : Prop :=
  ∀ (i : Nat) (t : ClosedExpression), ClosedGrade i t → 0 < closedValue t

def OriginalAmbientGradePositive : Prop :=
  ∀ (Γ : List Ty) (i : Nat) (t : OrdinalExpression Γ), AmbientGrade Γ i t →
    ∀ ρ : AdmissibleSubstitution Γ, 0 < expressionValue ρ t

def OriginalScalarPositiveValue : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ), AmbientGrade Γ 0 t →
    ∀ ρ : AdmissibleSubstitution Γ, 1 ≤ finiteValue (expressionValue ρ t)

end LogicLineages.OrdinalComparison.Source.Targets
