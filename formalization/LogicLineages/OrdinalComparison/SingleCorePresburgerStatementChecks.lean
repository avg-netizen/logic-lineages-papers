module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger.StatementChecks

theorem fixed_programs : Targets.ActualSingleCorePresburgerPrograms := programs
theorem fixed_output : Targets.ActualSingleCorePresburgerOutput := output
theorem fixed_universal : Targets.ActualSingleCoreUniversal := universal_correct
theorem fixed_full : Targets.FullActualSingleCorePresburger := full

#print axioms fixed_programs
#print axioms fixed_output
#print axioms fixed_universal
#print axioms fixed_full

end LogicLineages.OrdinalComparison.SingleCorePresburger.StatementChecks
