module

public import LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalizationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.StatementChecks

theorem fullNormalization : Targets.Target := Proof.fullTarget
theorem actualEvaluation : Targets.ActualEvaluation := fullNormalization.1
theorem internalEqualsOne : Targets.InternalEqualsOne := fullNormalization.2.1
theorem internalNormalizedRange : Targets.InternalNormalizedRange := fullNormalization.2.2.1
theorem internalSameASTAcceptance : Targets.InternalSameASTAcceptance := fullNormalization.2.2.2.1
theorem publishedBooleanVerifier : Targets.PublishedBooleanVerifier := fullNormalization.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization
