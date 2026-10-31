module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeDefinitions
public import Mathlib.Data.Nat.Init
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Literal old-group inclusion in the next root-adjunction quotient. -/
def walkerStageStep (p : ℕ) (parent : WalkerParentSequence) (n : ℕ) :
    (walkerFinitePresentation p parent n).Carrier →+
      (walkerFinitePresentation p parent (n+1)).Carrier where
  toFun x := walkerAdjunctionClass p
    ((parent n).elim 0 (walkerFinitePresentation p parent n).generator) x 0
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Finite composition of the actual successive quotient inclusions. -/
def walkerStageMap (p : ℕ) (parent : WalkerParentSequence) (n m : ℕ) (h : n ≤ m) :
    (walkerFinitePresentation p parent n).Carrier →+
      (walkerFinitePresentation p parent m).Carrier :=
  Nat.leRecOn h (@fun k f => (walkerStageStep p parent k).comp f) (AddMonoidHom.id _)

end LogicLineages.ModelsAlgebra.PGroups
