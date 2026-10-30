module
public import LogicLineages.OrdinalComparison.ControlledCountDefinitions
public import LogicLineages.OrdinalComparison.RestrictedPartitionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Actual source ordinal states of exact norm b strictly below a. -/
noncomputable def actualExactNormPredecessors (a : Ordinal.{0}) (b : Nat) : Finset Ordinal :=
  (actualBoundedPredecessors a b).filter (fun x => actualOrdinalNorm x = b)

end LogicLineages.OrdinalComparison
