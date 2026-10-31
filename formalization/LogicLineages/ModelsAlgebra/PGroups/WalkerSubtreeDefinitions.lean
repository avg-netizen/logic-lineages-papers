module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- The actual optional parent, viewed in the complete finite node set. -/
def walkerParentNode (parent : WalkerParentSequence) (n : ℕ) (i : Fin n) :
    Option (Fin n) :=
  (parent i.val).map (fun j => ⟨j.val, lt_trans j.isLt i.isLt⟩)

end LogicLineages.ModelsAlgebra.PGroups
