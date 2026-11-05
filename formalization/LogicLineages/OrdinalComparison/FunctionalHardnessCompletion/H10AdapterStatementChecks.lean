module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterSemanticProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10AdapterProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.StatementChecks

theorem impossible_system_correct : Targets.ImpossibleSystemCorrect := Proof.impossibleSystemCorrect
theorem original_safety : Targets.OriginalSafety := Proof.originalSafety
theorem parsed_calibration : Targets.ParsedCalibration := Proof.parsedCalibration
theorem reduction_primitive : Targets.ReductionPrimitive := Proof.reductionPrimitive
theorem polynomial_circuit_root : Targets.PolynomialCircuitRoot := Proof.polynomialCircuitRoot

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Adapter.StatementChecks
