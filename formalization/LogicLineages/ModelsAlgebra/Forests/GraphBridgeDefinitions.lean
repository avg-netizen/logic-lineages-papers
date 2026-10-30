module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionDefinitions
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! Literal comparability graphs and forbidden four-vertex graphs for paper 03.
The graph is an ordinary Mathlib SimpleGraph and its embeddings are induced
relation embeddings. An induced graph embedding need not itself preserve order.
-/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.GraphBridge

def comparabilityGraph (F : FiniteOrderForest) : SimpleGraph F.Carrier :=
  SimpleGraph.fromRel (fun x y => x ≤ y)

def fourPath : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => i.val + 1 = j.val)

def fourCycle : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => (i.val + 1) % 4 = j.val)

end LogicLineages.ModelsAlgebra.Forests.GraphBridge
