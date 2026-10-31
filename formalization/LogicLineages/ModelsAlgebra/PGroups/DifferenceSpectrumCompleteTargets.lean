module
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceSpectrumCompleteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Original full reduced difference spectrum, with actual unrestricted raw
endpoints and both directions, including zero/limit/finite-infinite boundaries. -/
def differenceSpectrumFullSource : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (α:Ordinal.{0}) [Countable α.ToType],
    (AttainedReducedDifference p α ↔ ∃β:Ordinal.{0},α=β+1) ∧
    (AttainedInfiniteReducedDifference p α ↔ 2≤α ∧ ∃β:Ordinal.{0},α=β+1)
end LogicLineages.ModelsAlgebra.PGroups.Targets
