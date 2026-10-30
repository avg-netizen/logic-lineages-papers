module

public import LogicLineages.ComputabilityKnowledge.GorbowVariableCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowVariableCode : LogicLineages.ComputabilityKnowledge.Comparators.GorbowVariableCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowVariableCodeProof.gorbowVariableCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
