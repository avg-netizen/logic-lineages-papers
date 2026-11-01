module
public import LogicLineages.OrdinalComparison.OneInputBooleanProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneInputBoolean.StatementChecks

theorem fixed_programs : Targets.ActualOneInputBooleanPrograms := programs
theorem fixed_value : Targets.ActualOneInputBooleanValue := source_value
theorem fixed_tail : Targets.ActualOneInputBooleanTail := source_tail
theorem fixed_full : Targets.FullActualOneInputBooleanClosures := full

#print axioms fixed_programs
#print axioms fixed_value
#print axioms fixed_tail
#print axioms fixed_full

end LogicLineages.OrdinalComparison.OneInputBoolean.StatementChecks
