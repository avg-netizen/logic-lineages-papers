module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowDiagonalCode : LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowDiagonalCodeProof.gorbowDiagonalCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
