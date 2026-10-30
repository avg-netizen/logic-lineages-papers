module

public import LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowProofChecker : LogicLineages.ComputabilityKnowledge.Comparators.GorbowProofChecker.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowProofCheckerProof.gorbowProofChecker

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
