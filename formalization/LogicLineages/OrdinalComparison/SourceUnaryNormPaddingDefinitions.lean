module
public import LogicLineages.OrdinalComparison.SourcePolynomialGradeOneTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding
noncomputable def scalar (t : OriginalDomain.ClosedExpression) : OriginalDomain.ClosedExpression :=
  UnitObservation.positive (actualOrdinalNorm (OriginalDomain.closedValue t))
noncomputable def vector (t : OriginalDomain.ClosedExpression) (j : Fin 2) : OriginalDomain.ClosedExpression :=
  if j.val=0 then scalar t else t
end LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding
