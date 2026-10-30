module
public import LogicLineages.OrdinalComparison.ScheduledCountDefinitions
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- The exact indexed budgets spent along the original norm-controlled
source trajectory. This is an observation of that trajectory, not a new
ordinal evaluator or a supplied agreement certificate. -/
noncomputable def actualControlBudgetStream (g : Nat → Nat) (a : Ordinal.{0}) (i : Nat) : Nat :=
  g (actualOrdinalNorm (actualControlledStateAfter g a i))

end LogicLineages.OrdinalComparison
