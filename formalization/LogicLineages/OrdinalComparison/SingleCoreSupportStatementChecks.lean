module
public import LogicLineages.OrdinalComparison.SingleCoreSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreSupport.StatementChecks

theorem fixed_program : Targets.ActualSingleCoreSupportProgram := program
theorem fixed_bounds : Targets.ActualSingleCoreSupportBounds := bounds
theorem fixed_agreement : Targets.ActualSingleCoreSupportAgreement := agreement
theorem fixed_dominance : Targets.ActualSingleCoreSupportDominance := dominance
theorem fixed_full : Targets.FullActualSingleCoreSupport := full

#print axioms fixed_program
#print axioms fixed_bounds
#print axioms fixed_agreement
#print axioms fixed_dominance
#print axioms fixed_full

end LogicLineages.OrdinalComparison.SingleCoreSupport.StatementChecks
