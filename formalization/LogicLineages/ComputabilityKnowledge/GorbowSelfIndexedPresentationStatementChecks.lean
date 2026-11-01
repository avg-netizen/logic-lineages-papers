module

public import LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.StatementChecks

theorem fullSelfIndexedPresentation : Targets.Target := Proof.fullTarget
theorem literalInstance : Targets.LiteralInstance := fullSelfIndexedPresentation.1
theorem uniformRawChecker : Targets.UniformRawChecker := fullSelfIndexedPresentation.2.1
theorem uniformNumericChecker : Targets.UniformNumericChecker := fullSelfIndexedPresentation.2.2.1
theorem actualFixedPoint : Targets.ActualFixedPoint := fullSelfIndexedPresentation.2.2.2.1
theorem exactPresentedTheory : Targets.ExactPresentedTheory := fullSelfIndexedPresentation.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation
