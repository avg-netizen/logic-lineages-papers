module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.StatementChecks

theorem fullReduction : Targets.Target := Proof.fullTarget
theorem actualDiagonal : Targets.ActualDiagonal := fullReduction.1
theorem localLobReduction : Targets.LocalLobReduction := fullReduction.2.1
theorem globalLobReduction : Targets.GlobalLobReduction := fullReduction.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReduction
