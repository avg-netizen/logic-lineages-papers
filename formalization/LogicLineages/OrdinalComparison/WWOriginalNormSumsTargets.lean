module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum AdmissibleAssignment

/-! Exact additive-norm suppliers cited from original Proposition 2.2 in the
repaired bounded-norm proof. These do not assume or assert the missing
product/exponential lower estimates or the final delta norm bound. -/
def ActualNaturalSumNormAdditivity : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    actualOrdinalNorm (ordinalNaturalSum a b) = actualOrdinalNorm a + actualOrdinalNorm b

def OriginalShapeNormAdditivity : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (n : Nat) (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ),
    actualOrdinalNorm (expressionValue ρ (expand s xs)) =
      ((List.ofFn xs).map (fun t => actualOrdinalNorm (expressionValue ρ t))).sum

def OriginalPositiveRepeatNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (p : Policy) (site : MacroSite)
    (k : Nat) (t : OrdinalExpression Γ), 0 < k →
    actualOrdinalNorm (expressionValue ρ (repeated p site k t)) =
      k * actualOrdinalNorm (expressionValue ρ t)

def OriginalScalarValueNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (t : OrdinalExpression Γ),
    AmbientGrade Γ 0 t →
      actualOrdinalNorm (expressionValue ρ t) = finiteValue (expressionValue ρ t)

end LogicLineages.OrdinalComparison.Source.Targets
