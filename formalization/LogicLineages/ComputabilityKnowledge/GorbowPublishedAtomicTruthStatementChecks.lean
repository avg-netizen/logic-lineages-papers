module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.StatementChecks

theorem fullAtomicTruth : Targets.Target := Proof.fullTarget
theorem headerCalibration : Targets.HeaderCalibration := fullAtomicTruth.1
theorem codeCalibration : Targets.CodeCalibration := fullAtomicTruth.2.1
theorem positiveAtomicSchemas : Targets.PositiveAtomicSchemas := fullAtomicTruth.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruth
