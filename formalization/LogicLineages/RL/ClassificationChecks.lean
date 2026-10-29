module

public import LogicLineages.RL.ClassificationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_classification (S : Alphabet) : Targets.Classification S :=
  ClassificationProof.classification S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
