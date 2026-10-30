module

public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ww_bounded_vector_code : LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorCode.Target :=
  LogicLineages.ComputabilityKnowledge.WWBoundedVectorCodeProof.wwBoundedVectorCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
