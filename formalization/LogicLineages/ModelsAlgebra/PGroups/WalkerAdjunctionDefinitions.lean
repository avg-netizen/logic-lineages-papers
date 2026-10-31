module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Prod
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- The literal one-leaf extension in paper 01, lines 694–700. -/
def walkerAdjunctionRelations {H : Type*} [AddCommGroup H] (p : ℕ) (a : H) :
    AddSubgroup (H × ℤ) := AddSubgroup.zmultiples (-a, (p : ℤ))

abbrev WalkerAdjunction {H : Type*} [AddCommGroup H] (p : ℕ) (a : H) :=
  (H × ℤ) ⧸ walkerAdjunctionRelations p a

def walkerAdjunctionClass {H : Type*} [AddCommGroup H] (p : ℕ) (a : H)
    (h : H) (z : ℤ) : WalkerAdjunction p a :=
  QuotientAddGroup.mk (h, z)

end LogicLineages.ModelsAlgebra.PGroups
