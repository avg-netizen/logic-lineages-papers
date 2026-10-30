module

public import LogicLineages.ComputabilityKnowledge.RayCodeEvaluationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem ray_code_evaluation : LogicLineages.ComputabilityKnowledge.Comparators.RayCodeEvaluation.Target :=
  LogicLineages.ComputabilityKnowledge.RayCodeEvaluationProof.rayCodeEvaluation

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
