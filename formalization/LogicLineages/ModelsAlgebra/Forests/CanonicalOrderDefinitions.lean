module

public import LogicLineages.ModelsAlgebra.Forests.GraphUniversalDefinitions

/-! Explicit canonical-order data for paper 03 `lem:bridge` representation.
Reverse closed-neighborhood inclusion determines the order except among equal
neighborhoods, where an arbitrary finite enumeration breaks ties. Correctness
is not a structure field or an assumed representation supplier. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridge

noncomputable def canonicalRank {α : Type} [Fintype α] (x : α) : Nat :=
  (Fintype.equivFin α x).val

def canonicalLE {α : Type} [Fintype α] (G : SimpleGraph α) (x y : α) : Prop :=
  closedNeighborhood G y ⊆ closedNeighborhood G x ∧
    (closedNeighborhood G x = closedNeighborhood G y → canonicalRank x ≤ canonicalRank y)

end LogicLineages.ModelsAlgebra.Forests.GraphBridge
