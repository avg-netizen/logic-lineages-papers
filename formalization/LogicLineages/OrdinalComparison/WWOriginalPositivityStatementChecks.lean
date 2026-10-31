module
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalClosedGradePositive : Source.Targets.OriginalClosedGradePositive :=
  Source.OriginalDomain.originalClosedGradePositive

theorem fixed_originalAmbientGradePositive : Source.Targets.OriginalAmbientGradePositive :=
  Source.OriginalDomain.originalAmbientGradePositive

theorem fixed_originalScalarPositiveValue : Source.Targets.OriginalScalarPositiveValue :=
  Source.OriginalDomain.originalScalarPositiveValue

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
