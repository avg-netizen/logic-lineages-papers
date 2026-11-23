module
public import Init.Data.List.Perm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionTargets

/-- The two actual tape partitions can be given separate side origins.
These are occurrence-sensitive permutations, not membership equivalences. -/
def ExactOriginConsumption : Prop :=
  ∀ (left right kept removed : List Nat),
    (left ++ right).Perm (kept ++ removed) →
    ∃ keptLeft keptRight removedLeft removedRight : List Nat,
      left.Perm (keptLeft ++ removedLeft) ∧
      right.Perm (keptRight ++ removedRight) ∧
      kept.Perm (keptLeft ++ keptRight) ∧
      removed.Perm (removedLeft ++ removedRight)

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionTargets
