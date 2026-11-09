module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.SupportProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeCalibrationProof
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.CodeProgramsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.StatementChecks

theorem actual_word_linear_elimination : Targets.ActualWordLinearElimination :=
  Proof.actualWordLinearElimination
theorem exact_output_tokens : Targets.ExactOutputTokens := Proof.exactOutputTokens
theorem exact_output_variables : Targets.ExactOutputVariables := Proof.exactOutputVariables
theorem exact_original_domains : Targets.ExactOriginalDomains := Proof.exactOriginalDomains
theorem exact_degree_preservation : Targets.ExactDegreePreservation := Proof.exactDegreePreservation
theorem domain_aware_elimination : Targets.DomainAwareElimination := Proof.domainAwareElimination
theorem literal_code_calibration : Targets.LiteralCodeCalibration := Proof.literalCodeCalibration
theorem actual_numeric_program : Targets.ActualNumericProgram := Proof.actualNumericProgram

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.StatementChecks
