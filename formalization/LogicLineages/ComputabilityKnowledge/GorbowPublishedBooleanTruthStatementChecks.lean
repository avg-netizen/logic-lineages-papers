module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruthProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.StatementChecks

theorem fullBooleanTruth : Targets.Target := Proof.fullTarget
theorem groundGuard : Targets.GroundGuard := fullBooleanTruth.1
theorem booleanFunctions : Targets.BooleanFunctions := fullBooleanTruth.2.1
theorem positiveBooleanAxioms : Targets.PositiveBooleanAxioms := fullBooleanTruth.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth
