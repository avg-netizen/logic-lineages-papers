module
public import LogicLineages.ModelsAlgebra.Forests.GraphJEPDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
public import Mathlib.Order.Preorder.Finite
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation
open GraphBridge RankedParse RankedGraphImage

/-- Only repackaging the same actual finite graph, with a chosen finite enumeration. -/
noncomputable def bridgeGraph (G : FiniteGraph) : FiniteSimpleGraph :=
  ⟨G.Vertex, Fintype.ofFinite G.Vertex, G.edges⟩

def ForbiddenClass (U : List FiniteOrderForest) (G : FiniteGraph) : Prop :=
  GraphAvoidsForbidden U (bridgeGraph G)

def ForbiddenLanguage (U : List FiniteOrderForest) (t : Term) : Prop :=
  ForbiddenClass U (evalFinite t)

/-- Literal leaf occurrences represent exactly a given subset of an actual forest. -/
structure Realizes (F : FiniteOrderForest) (S : Finset F.Carrier) (t : Term) where
  map : Leaf t → F.Carrier
  injective : Function.Injective map
  adjacency : ∀ x y, (comparabilityGraph F).Adj (map x) (map y) ↔ Adj t x y
  image : ∀ y, (∃ x, map x = y) ↔ y ∈ S

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentation
