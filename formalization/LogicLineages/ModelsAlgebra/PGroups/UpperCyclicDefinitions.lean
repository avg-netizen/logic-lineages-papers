module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Group.Pi.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- The actual finite upper cyclic factor in the source decomposition. -/
abbrev UpperCyclicGroup (p s : ℕ) (r : Fin s → ℕ) := ∀ a : Fin s, ZMod (p ^ r a)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
