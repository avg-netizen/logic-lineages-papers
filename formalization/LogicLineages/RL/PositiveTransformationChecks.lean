module

public import LogicLineages.RL.PositiveTransformationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_positiveTransformation (S : Alphabet) : Targets.PositiveTransformation S :=
  PositiveTransformationProof.positiveTransformation S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
