module
public import LogicLineages.OrdinalComparison.ProfileCompositionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.ProfileComposition.StatementChecks

theorem fixed_source : Targets.ActualProfileCompositionSource := source
theorem fixed_support : Targets.ProfileCompositionInputSupport := support
theorem fixed_program : Targets.ProfileCompositionProgram := program

end LogicLineages.OrdinalComparison.ProfileComposition.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.ProfileComposition
