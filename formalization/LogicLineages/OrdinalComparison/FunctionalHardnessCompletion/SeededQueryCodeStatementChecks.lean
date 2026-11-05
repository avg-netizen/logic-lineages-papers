module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeReductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.StatementChecks

theorem exact_query_calibration : Targets.ExactQueryCalibration := Proof.exactQueryCalibration
theorem exact_well_formed : Targets.ExactWellFormed := Proof.exactWellFormed
theorem primitive_programs : Targets.PrimitivePrograms := Proof.primitivePrograms
theorem exact_total_reduction : Targets.ExactTotalReduction := Proof.exactTotalReduction
theorem exact_strict_reduction : SingleQueryReduction true := Proof.existingReductions.1
theorem exact_weak_reduction : SingleQueryReduction false := Proof.existingReductions.2

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode
