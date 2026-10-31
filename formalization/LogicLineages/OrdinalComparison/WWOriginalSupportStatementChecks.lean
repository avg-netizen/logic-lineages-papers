module
public import LogicLineages.OrdinalComparison.WWOriginalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalSupportedExtension : Source.Targets.OriginalSupportedExtension :=
  Source.OriginalDomain.originalSupportedExtension

theorem fixed_originalComparisonSupportCoverage : Source.Targets.OriginalComparisonSupportCoverage :=
  Source.OriginalDomain.originalComparisonSupportCoverage

theorem fixed_originalSupportComparisonBridge : Source.Targets.OriginalSupportComparisonBridge :=
  Source.OriginalDomain.originalSupportComparisonBridge

theorem fixed_originalSourceWeakScalar : Source.Targets.OriginalSourceWeakScalar :=
  Source.OriginalDomain.originalSourceWeakScalar

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
