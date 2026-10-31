module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

def WalkerSequentialAssignment (p : ℕ) (parent : WalkerParentSequence)
    {K : Type} [AddCommGroup K] (y : ℕ → K) : Prop :=
  ∀ i, p • y i = (parent i).elim 0 (fun j => y j.val)

end LogicLineages.ModelsAlgebra.PGroups
