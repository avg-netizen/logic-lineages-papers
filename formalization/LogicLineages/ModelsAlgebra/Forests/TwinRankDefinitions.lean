module

public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalDefinitions

/-! Literal equal-closed-neighborhood classes and strict-predecessor ranks for
paper 03 `lem:bridge` uniqueness. No order-recovery property is assumed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridge

def twinClass (F : FiniteOrderForest) (x : F.Carrier) : Set F.Carrier :=
  {y | closedNeighborhood (comparabilityGraph F) y =
    closedNeighborhood (comparabilityGraph F) x}

noncomputable def twinRank (F : FiniteOrderForest) (x : F.Carrier) : Nat := by
  classical
  exact (Finset.univ.filter (fun y => y ∈ twinClass F x ∧ y < x)).card

noncomputable def twinCard (F : FiniteOrderForest) (x : F.Carrier) : Nat := by
  classical
  exact (Finset.univ.filter (fun y => y ∈ twinClass F x)).card

end LogicLineages.ModelsAlgebra.Forests.GraphBridge
