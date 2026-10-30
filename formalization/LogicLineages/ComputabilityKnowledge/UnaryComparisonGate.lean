module

public import LogicLineages.ComputabilityKnowledge.UnaryComparisonProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem unary_comparison : LogicLineages.ComputabilityKnowledge.Comparators.UnaryComparison.Target :=
  LogicLineages.ComputabilityKnowledge.UnaryComparisonProof.unaryComparison

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
