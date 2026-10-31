module
public import LogicLineages.OrdinalComparison.WWOriginalProductLowerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualPositiveOrdinalNorm : Source.Targets.ActualPositiveOrdinalNorm :=
  Source.OriginalDomain.actualPositiveOrdinalNorm

theorem fixed_actualNaturalProductNormLower : Source.Targets.ActualNaturalProductNormLower :=
  Source.OriginalDomain.actualNaturalProductNormLower

theorem fixed_actualNaturalProductComponentNorm : Source.Targets.ActualNaturalProductComponentNorm :=
  Source.OriginalDomain.actualNaturalProductComponentNorm

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
