module
public import LogicLineages.OrdinalComparison.ComparisonExpansionDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison

def ComparisonNumericChild (next current : Nat × Nat) : Prop :=
  next∈encodedComparisonChildren current.1 current.2

def encodedComparisonFrontierStep (nodes : List (Nat × Nat)) : List (Nat × Nat) :=
  nodes.flatMap (fun p => encodedComparisonChildren p.1 p.2)

def encodedComparisonFrontier (root : Nat × Nat) (depth : Nat) : List (Nat × Nat) :=
  (encodedComparisonFrontierStep^[depth]) [root]

/-- Genuine least search for the first EMPTY frontier, not a given depth bound
or an assertion that the child relation terminates. -/
def encodedComparisonDepthPartial (root : Nat × Nat) : Part Nat :=
  Nat.rfind (fun k => Part.some (decide (encodedComparisonFrontier root k=[])))

noncomputable def encodedComparisonTreeDepth (root : Nat × Nat) : Nat := by
  classical
  exact (encodedComparisonDepthPartial root).getOrElse 0

noncomputable def encodedComparisonTreeLayers (root : Nat × Nat) : List (List (Nat × Nat)) :=
  (List.range (encodedComparisonTreeDepth root+1)).map (encodedComparisonFrontier root)

end LogicLineages.OrdinalComparison
