module

public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.StatementChecks

theorem fullAdditiveStructure : Targets.Target := Proof.fullTarget
theorem predecessor : Targets.Predecessor := fullAdditiveStructure.1
theorem leftZero : Targets.LeftZero := fullAdditiveStructure.2.1
theorem leftSuccessor : Targets.LeftSuccessor := fullAdditiveStructure.2.2.1
theorem rightCancellation : Targets.RightCancellation := fullAdditiveStructure.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure
