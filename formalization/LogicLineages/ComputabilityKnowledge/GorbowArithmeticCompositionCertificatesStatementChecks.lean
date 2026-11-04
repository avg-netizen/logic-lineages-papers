module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificatesProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.StatementChecks

theorem fullCompositionCertificates : Targets.Target := Proof.fullTarget
theorem witnessIntroduction : Targets.WitnessIntroduction := fullCompositionCertificates.1
theorem finiteConjunction : Targets.FiniteConjunction := fullCompositionCertificates.2.1
theorem compositionCertificates : Targets.CompositionCertificates := fullCompositionCertificates.2.2.1
theorem recursionFreeCertificates : Targets.RecursionFreeCertificates := fullCompositionCertificates.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticCompositionCertificates
