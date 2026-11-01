module

public import LogicLineages.ComputabilityKnowledge.GorbowSelectedDistributionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.StatementChecks

theorem fullSelectedDistribution : Targets.Target := Proof.fullTarget
theorem actualPrograms : Targets.ActualPrograms := fullSelectedDistribution.1
theorem numericAxiomChecker : Targets.NumericAxiomChecker := fullSelectedDistribution.2.1
theorem literalCodingCertificates : Targets.LiteralCodingCertificates :=
  fullSelectedDistribution.2.2.1
theorem selectedAgentClosure : Targets.SelectedAgentClosure :=
  fullSelectedDistribution.2.2.2.1
theorem completeSupplier : Targets.CompleteSupplier :=
  fullSelectedDistribution.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution
