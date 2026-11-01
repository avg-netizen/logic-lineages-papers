module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StatementChecks

theorem fullEnumeratedProvability : Targets.Target := Proof.fullTarget
theorem uniformAxiomChecker : Targets.UniformAxiomChecker := fullEnumeratedProvability.1
theorem boundedMonotonicity : Targets.BoundedMonotonicity := fullEnumeratedProvability.2.1
theorem exactAxiomUnion : Targets.ExactAxiomUnion := fullEnumeratedProvability.2.2.1
theorem finiteProofStage : Targets.FiniteProofStage := fullEnumeratedProvability.2.2.2.1
theorem uniformNumericChecker : Targets.UniformNumericChecker := fullEnumeratedProvability.2.2.2.2.1
theorem exactNumericAcceptance : Targets.ExactNumericAcceptance := fullEnumeratedProvability.2.2.2.2.2.1
theorem fixedUniversalProgram : Targets.FixedUniversalProgram := fullEnumeratedProvability.2.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability
