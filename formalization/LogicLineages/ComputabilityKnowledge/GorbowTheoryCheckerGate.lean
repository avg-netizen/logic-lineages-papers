module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowTheoryChecker : LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryChecker.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowTheoryCheckerProof.gorbowTheoryChecker

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
