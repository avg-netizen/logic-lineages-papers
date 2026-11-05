module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeReductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.StatementChecks

theorem exact_query_calibration : Targets.ExactQueryCalibration := Proof.exactQueryCalibration
theorem exact_list_calibration : Targets.ExactListCalibration := Proof.exactListCalibration
theorem primitive_programs : Targets.PrimitivePrograms := Proof.primitivePrograms
theorem exact_total_reduction : Targets.ExactTotalReduction := Proof.exactTotalReduction
theorem exact_strict_reduction : FiniteQueryReduction true := Proof.existingReductions.1
theorem exact_weak_reduction : FiniteQueryReduction false := Proof.existingReductions.2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode
