module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportStatementChecks

theorem exact_correlated_body : OutcomeTransportTargets.ExactCorrelatedBody :=
  OutcomeTransportProof.exactCorrelatedBody

theorem body_syntax_and_domains : OutcomeTransportTargets.BodySyntaxAndDomains :=
  OutcomeTransportProof.bodySyntaxAndDomains

theorem literal_code_calibration : OutcomeTransportTargets.LiteralCodeCalibration :=
  OutcomeTransportProof.literalCodeCalibration

theorem exact_actual_matrix : OutcomeTransportTargets.ExactActualMatrix :=
  OutcomeTransportProof.exactActualMatrix

theorem actual_numeric_programs : OutcomeTransportTargets.ActualNumericPrograms :=
  OutcomeTransportPrograms.actualNumericPrograms

theorem full_outcome_transport : OutcomeTransportTargets.FullOutcomeTransport :=
  OutcomeTransportProof.fullOutcomeTransport

#print axioms exact_correlated_body
#print axioms body_syntax_and_domains
#print axioms literal_code_calibration
#print axioms exact_actual_matrix
#print axioms actual_numeric_programs
#print axioms full_outcome_transport

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportStatementChecks
