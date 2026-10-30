module
public import LogicLineages.ModelsAlgebra.PGroups.FreshCoordinatesDefinitions
public import Mathlib.Data.Set.Disjoint
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupReserveEvenInjective : Prop := ∀ M : ℕ, Function.Injective (reserveEven M)
def groupReserveOddInjective : Prop := ∀ M : ℕ, Function.Injective (reserveOdd M)
def groupReserveRangesDisjoint : Prop := ∀ M : ℕ, Disjoint (Set.range (reserveEven M)) (Set.range (reserveOdd M))
def groupReserveEvenFixes : Prop := ∀ M n : ℕ, n < M → reserveEven M n = n

end LogicLineages.ModelsAlgebra.PGroups.Targets
