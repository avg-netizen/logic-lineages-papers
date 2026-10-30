module

public import LogicLineages.ComputabilityKnowledge.RayHeightInductionProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_height_induction : LogicLineages.ComputabilityKnowledge.Comparators.RayHeightInduction.Target :=
  LogicLineages.ComputabilityKnowledge.RayHeightInductionProof.rayHeightInduction

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
