module

public import LogicLineages.RL.Noncomposition
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.RL.StatementChecks

theorem fixed_composition_counterexample : Targets.NaturalCompositionFails :=
  natural_composition_fails

end LogicLineages.RL.StatementChecks

#audit_namespace LogicLineages.RL
