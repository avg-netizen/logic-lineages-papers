module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.StatementChecks

theorem exact_monomial_code : Targets.ExactMonomialCode := Proof.exactMonomialCode
theorem exact_rows : Targets.ExactRows := Proof.exactRows
theorem exact_subtract_seed : Targets.ExactSubtractSeed := Proof.exactSubtractSeed
theorem exact_system_inputs : Targets.ExactSystemInputs := Proof.exactSystemInputs
theorem numerical_programs : Targets.NumericalPrograms := Proof.numericalPrograms

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededInputCode
