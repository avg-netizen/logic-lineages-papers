module

public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.StatementChecks

theorem termCongruence : Targets.TermCongruence := Proof.termCongruence
theorem callSubstitution : Targets.CallSubstitution := Proof.callSubstitution
theorem callCongruence : Targets.CallCongruence := Proof.callCongruence

end LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruence.StatementChecks
