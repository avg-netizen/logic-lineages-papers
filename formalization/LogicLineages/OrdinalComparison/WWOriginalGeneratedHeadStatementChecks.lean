module
public import LogicLineages.OrdinalComparison.WWOriginalGeneratedHeadProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_originalFreeAmbientHead : Source.Targets.OriginalFreeAmbientHead :=
  Source.OriginalDomain.originalFreeAmbientHead

theorem fixed_originalGeneratedAmbientHead : Source.Targets.OriginalGeneratedAmbientHead :=
  Source.OriginalDomain.originalGeneratedAmbientHead

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
