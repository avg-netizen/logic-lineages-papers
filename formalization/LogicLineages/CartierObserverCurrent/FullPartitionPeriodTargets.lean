module
public import LogicLineages.OrdinalComparison.RestrictedPartitionTargets
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullPartitionPeriod.Targets
open LogicLineages.OrdinalComparison

/-- Literal sufficient factorial period for the actual weighted-vector count. -/
def CompletePartitionPeriod : Prop :=
  ∀ d m : Nat, 1 ≤ d → 1 ≤ m → ∀ n : Nat,
    Nat.ModEq m (restrictedPartitionCount d (n + d.factorial * m ^ (d - 1)))
      (restrictedPartitionCount d n)
end LogicLineages.CartierObserverCurrent.FullPartitionPeriod.Targets
