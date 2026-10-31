module
public import Mathlib.Algebra.Field.Rat
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Torsion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The literal rational quotient ℚ/ℤ. -/
abbrev RationalModIntegers := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)
/-- The genuine Prüfer p-group: p-power torsion in ℚ/ℤ. -/
abbrev PrueferModel (p : ℕ) := AddCommGroup.primaryComponent RationalModIntegers p
end LogicLineages.ModelsAlgebra.PGroups
