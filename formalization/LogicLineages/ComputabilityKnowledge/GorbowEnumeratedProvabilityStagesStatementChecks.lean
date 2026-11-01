module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityStagesProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StagesStatementChecks

theorem uniformAxiomChecker : Targets.UniformAxiomChecker := StagesProof.uniformAxiomChecker
theorem boundedMonotonicity : Targets.BoundedMonotonicity := StagesProof.boundedMonotonicity
theorem exactAxiomUnion : Targets.ExactAxiomUnion := StagesProof.exactAxiomUnion
theorem finiteProofStage : Targets.FiniteProofStage := StagesProof.finiteProofStage

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StagesStatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvability.StagesStatementChecks
