module

public import LogicLineages.RL.OneShotProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.Policy.StatementChecks

theorem fixed_oneShotOffPathRule (S : Alphabet) : Targets.OneShotOffPathRule S :=
  OneShotProof.oneShotOffPathRule S

theorem fixed_oneShotFiniteValue (S : Alphabet) : Targets.OneShotFiniteValue S :=
  OneShotProof.oneShotFiniteValue S

theorem fixed_oneShotAdmissible (S : Alphabet) : Targets.OneShotAdmissible S :=
  OneShotProof.oneShotAdmissible S

theorem fixed_oneShotValue (S : Alphabet) : Targets.OneShotValue S :=
  OneShotProof.oneShotValue S

theorem fixed_oneShotSpecialValues (S : Alphabet) : Targets.OneShotSpecialValues S :=
  OneShotProof.oneShotSpecialValues S

end LogicLineages.RL.Policy.StatementChecks

#audit_namespace LogicLineages.RL.Policy
