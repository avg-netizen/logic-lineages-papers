module

public import LogicLineages.RL.SingletonProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_singletonNoTransformation (S : Alphabet) : Targets.SingletonNoTransformation S :=
  SingletonProof.singletonNoTransformation S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
