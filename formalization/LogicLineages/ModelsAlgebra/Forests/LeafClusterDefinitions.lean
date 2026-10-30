module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionDefinitions
public import LogicLineages.ModelsAlgebra.Forests.WidthDefinitions

/-! Literal descendant leaves for the saturated-width argument in paper 03
`thm:width`. Leaves are maximal vertices, not additional selected roots or labels. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

abbrev ForestLeaf (F : FiniteOrderForest) := {x : F.Carrier // IsMax x}

def leafCluster (F : FiniteOrderForest) (v : F.Carrier) : Set (ForestLeaf F) :=
  {ℓ | v ≤ ℓ.val}

end LogicLineages.ModelsAlgebra.Forests
