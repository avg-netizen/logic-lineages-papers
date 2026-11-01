module
public import LogicLineages.OrdinalComparison.OneNameSourceBooleanProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneNameSourceBoolean.StatementChecks

theorem fixed_programs : Targets.ActualOneNameSourceBooleanPrograms := programs
theorem fixed_value : Targets.ActualOneNameSourceBooleanValue := source_value
theorem fixed_full : Targets.FullActualOneNameSourceBooleanClosures := full

#print axioms fixed_programs
#print axioms fixed_value
#print axioms fixed_full

end LogicLineages.OrdinalComparison.OneNameSourceBoolean.StatementChecks
