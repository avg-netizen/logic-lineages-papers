module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance

/-- A literal surviving block greatest by the ACTUAL ordinal-head/complete-input
key. Neither a numerical code order nor a supplied endpoint maximum is used. -/
def GreatestSurvivor (basis : List Nat) (row : Row) (winner : Int × Atom) : Prop :=
  winner ∈ (Collection.collect basis row).atoms ∧
    ∀ a ∈ (Collection.collect basis row).atoms, ¬keyLess basis winner.2 a.2

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance
