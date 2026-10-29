module

public import LogicLineages.RL.NegativeTransformationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_negativeTransformation (S : Alphabet) : Targets.NegativeTransformation S :=
  NegativeTransformationProof.negativeTransformation S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
