module

public import LogicLineages.ComputabilityKnowledge.ExponentialGapProof
public meta import LogicLineages.Audit

@[expose] public section


/-! Independent statement gate. The author may not edit this file or the
comparator. Additional premises in the proposed result do not match this type. -/

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem exponential_gap : Comparators.ExponentialGap.Target :=
  ExponentialGapProof.finiteSystemCollision

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
