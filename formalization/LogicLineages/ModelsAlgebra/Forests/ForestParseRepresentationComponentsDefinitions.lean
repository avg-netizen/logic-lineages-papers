module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationACDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents

/-- Actual induced graph on a vertex fiber; these are not assumed abstract components. -/
def fiberGraph {V I : Type} (G : SimpleGraph V) (c : V → I) (i : I) :
    SimpleGraph {v : V // c v = i} := G.induce {v | c v = i}

/-- The concrete decomposition properties used by reduced cotree children:
nonempty connected induced pieces and no edges between distinct pieces. -/
structure ConnectedFibers {V I : Type} (G : SimpleGraph V) (c : V → I) : Prop where
  onto : Function.Surjective c
  connected : ∀ i, (fiberGraph G c i).Connected
  noCross : ∀ v w, G.Adj v w → c v = c w

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents
