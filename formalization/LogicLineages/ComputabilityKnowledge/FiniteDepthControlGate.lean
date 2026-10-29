module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthControlProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem finite_depth_control : Comparators.FiniteDepthControl.Target :=
  FiniteDepthControlProof.finiteDepthControl

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
