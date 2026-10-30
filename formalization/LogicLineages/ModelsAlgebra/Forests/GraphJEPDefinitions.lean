module

public import LogicLineages.ModelsAlgebra.Forests.GraphBridgeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchDefinitions

/-! Literal finite graph classes in paper 03 `thm:decision`'s semantic reduction.
The forbidden family is exactly P4, C4, and the comparability graphs of U.
There is no algorithm or Carter supplier in these definitions. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridge

structure FiniteSimpleGraph where
  Carrier : Type
  carrierFintype : Fintype Carrier
  graph : SimpleGraph Carrier

attribute [instance] FiniteSimpleGraph.carrierFintype

def finiteComparabilityGraph (F : FiniteOrderForest) : FiniteSimpleGraph :=
  ⟨F.Carrier, F.carrierFintype, comparabilityGraph F⟩

def GraphAvoidsForbidden (U : List FiniteOrderForest) (G : FiniteSimpleGraph) : Prop :=
  ¬ Nonempty (fourPath ↪g G.graph) ∧ ¬ Nonempty (fourCycle ↪g G.graph) ∧
    ∀ B ∈ U, ¬ Nonempty (comparabilityGraph B ↪g G.graph)

def GraphHasJEP (U : List FiniteOrderForest) : Prop :=
  ∀ G H : FiniteSimpleGraph, GraphAvoidsForbidden U G → GraphAvoidsForbidden U H →
    ∃ K : FiniteSimpleGraph, GraphAvoidsForbidden U K ∧
      Nonempty (G.graph ↪g K.graph) ∧ Nonempty (H.graph ↪g K.graph)

end LogicLineages.ModelsAlgebra.Forests.GraphBridge
