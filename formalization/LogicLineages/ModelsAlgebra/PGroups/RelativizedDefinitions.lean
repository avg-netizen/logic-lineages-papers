module
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
public import Mathlib.Algebra.Group.Subgroup.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

/-- Literal quantifier relativization to an actual subgroup; free parameters and
quantifier-free terms remain in the ambient group. -/
def Formula.RealizeIn {G : Type u} [AddCommGroup G] (S : AddSubgroup G) :
    {n : ℕ} → Formula n → (Fin n → G) → Prop
  | _, .qf q, a => q.Realize a
  | _, .disjEx s m matrix, a =>
      ∃ i : s, ∃ c : Fin (m i) → S, (matrix i).RealizeIn S (append a (fun j => (c j : G)))
  | _, .conjAll s m matrix, a =>
      ∀ i : s, ∀ c : Fin (m i) → S, (matrix i).RealizeIn S (append a (fun j => (c j : G)))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
