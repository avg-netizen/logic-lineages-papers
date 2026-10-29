module

public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem finite_comparison_enumeration : Comparators.FiniteComparisonEnumeration.Target :=
  FiniteComparisonEnumerationProof.finiteComparisonEnumeration

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
