module
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_scalarTranslationSound : Source.Targets.ScalarTranslationSound :=
  Source.ForwardTranslation.scalarTranslationSound

theorem fixed_generatedGroundScalarTranslationTotal : Source.Targets.GeneratedGroundScalarTranslationTotal :=
  Source.ForwardTranslation.generatedGroundScalarTranslationTotal

end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
