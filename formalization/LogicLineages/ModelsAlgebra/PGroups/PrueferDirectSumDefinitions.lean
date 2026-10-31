module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleIsoDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
public import Mathlib.Data.Finsupp.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The literal finite-support direct sum of genuine rational-mod-integer Prüfer groups. -/
abbrev PrueferDirectSum (p : ℕ) (I : Type) := I →₀ PrueferModel p
end LogicLineages.ModelsAlgebra.PGroups
