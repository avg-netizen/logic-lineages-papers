module
public import LogicLineages.OrdinalComparison.SourcePolynomialGradeOneDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Targets

def ActualGradedRealization : Prop := ∀ p : SourcePolynomialRealization.NonnegativePolynomial,
  p≠0 → ∃ t : OriginalDomain.ClosedExpression,
    OriginalDomain.ClosedGrade 1 t ∧
    SignedPair.signedCNF (OriginalDomain.closedValue t)=SourcePolynomialRealization.embeddedCoefficients p ∧
    0<OriginalDomain.closedValue t ∧
    OriginalDomain.closedValue t < Ordinal.omega0 ^ Ordinal.omega0
end LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Targets
