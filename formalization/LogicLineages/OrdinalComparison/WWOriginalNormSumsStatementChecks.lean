module
public import LogicLineages.OrdinalComparison.WWOriginalNormSumsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualNaturalSumNormAdditivity : Source.Targets.ActualNaturalSumNormAdditivity :=
  Source.OriginalDomain.actualNaturalSumNormAdditivity

theorem fixed_originalShapeNormAdditivity : Source.Targets.OriginalShapeNormAdditivity :=
  Source.OriginalDomain.originalShapeNormAdditivity

theorem fixed_originalPositiveRepeatNorm : Source.Targets.OriginalPositiveRepeatNorm :=
  Source.OriginalDomain.originalPositiveRepeatNorm

theorem fixed_originalScalarValueNorm : Source.Targets.OriginalScalarValueNorm :=
  Source.OriginalDomain.originalScalarValueNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
