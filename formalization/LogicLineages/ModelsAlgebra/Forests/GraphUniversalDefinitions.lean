module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeDefinitions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Paper 03, `lem:bridge`, reverse-representation supplier.
Closed neighborhoods have their literal graph meaning; no representation or
universal-vertex theorem is part of this definition. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridge

/-- The vertex itself together with its graph neighbors. -/
def closedNeighborhood {α : Type} (G : SimpleGraph α) (v : α) : Set α :=
  {x | x = v ∨ G.Adj v x}

end LogicLineages.ModelsAlgebra.Forests.GraphBridge
