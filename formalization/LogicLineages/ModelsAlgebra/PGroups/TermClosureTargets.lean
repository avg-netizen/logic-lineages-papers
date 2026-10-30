module
public import LogicLineages.ModelsAlgebra.PGroups.BackForthDefinitions
public import Mathlib.Algebra.Group.Subgroup.Lattice
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
universe u

def groupTermClosureMembership : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (t : GroupTerm n),
    t.eval a ∈ AddSubgroup.closure (Set.range a)

def groupClosureTermRepresentation : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (a : Fin n → G) (x : G),
    x ∈ AddSubgroup.closure (Set.range a) → ∃ t : GroupTerm n, t.eval a = x

end LogicLineages.ModelsAlgebra.PGroups.Targets
