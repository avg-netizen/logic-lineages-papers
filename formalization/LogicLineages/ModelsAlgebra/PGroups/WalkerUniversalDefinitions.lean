module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Literal equations from the finite rooted-tree presentation. -/
def WalkerAssignmentRelations (p : ℕ) (parent : WalkerParentSequence) (n : ℕ)
    {K : Type} [AddCommGroup K] (y : Fin n → K) : Prop :=
  ∀ i : Fin n, p • y i = (parent i.val).elim 0
    (fun j => y ⟨j.val, lt_trans j.isLt i.isLt⟩)

end LogicLineages.ModelsAlgebra.PGroups
