module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificatesProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.StatementChecks

theorem fullBetaCertificates : Targets.Target := Proof.fullTarget
theorem literalBeta : Targets.LiteralBeta := fullBetaCertificates.1
theorem positiveBetaCertificates : Targets.PositiveBetaCertificates := fullBetaCertificates.2.1
theorem pointwiseValueTotality : Targets.PointwiseValueTotality := fullBetaCertificates.2.2.1
theorem finiteSequenceCertificates : Targets.FiniteSequenceCertificates := fullBetaCertificates.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticBetaCertificates
