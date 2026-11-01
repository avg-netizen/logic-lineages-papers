module
public import LogicLineages.OrdinalComparison.RangeRangeNodeDefinitions
public import LogicLineages.OrdinalComparison.RangePositiveNodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The actual four-way source-sort dispatcher. All functions are total on
numeric codes; source correctness only asserts genuine source meanings. -/
noncomputable def encodedComparisonQueryNode (q : ComparisonQuery) (table : ComparisonNodeTable) : ComparisonNodeResult :=
  if q.1.1%2=0 then
    if q.1.2%2=0 then encodedPositiveQueryNode q table else encodedRangePositiveQueryNode q table
  else if q.1.2%2=0 then encodedRangePositiveQueryNode q table else encodedRangeRangeQueryNode q table

/-- EVERY result in one layer is computed against the already completed next
layer table. A sibling never supplies a circular comparison hypothesis. -/
noncomputable def encodedComparisonQueryLayer (nodes : List ComparisonQuery) (table : ComparisonNodeTable) : ComparisonNodeTable :=
  nodes.map (fun q => (q,encodedComparisonQueryNode q table))++table

/-- Literal bottom-up fold on the actual computed finite query layers. -/
noncomputable def encodedComparisonQueryTable (layers : List (List ComparisonQuery)) : ComparisonNodeTable :=
  layers.foldr encodedComparisonQueryLayer []

noncomputable def encodedComparisonQueryResult (q : ComparisonQuery) : ComparisonNodeResult :=
  ((encodedComparisonQueryTable (encodedComparisonQueryLayers q)).headD (q,(1,1))).2

noncomputable def encodedOneVariableSignDecision (n m : Nat) : Nat × Nat :=
  encodedComparisonQueryResult ((n,m),(1,1))

end LogicLineages.OrdinalComparison
