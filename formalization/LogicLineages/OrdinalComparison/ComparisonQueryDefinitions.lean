module
public import LogicLineages.OrdinalComparison.ComparisonTreeDefinitions
public import LogicLineages.OrdinalComparison.ProfileCompositionDefinitions
public import LogicLineages.OrdinalComparison.LimitPairCertificateDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

abbrev ComparisonQuery := (Nat × Nat) × (Nat × Nat)

def encodedComparisonHeadContext (source : Nat) : Nat :=
  4*Nat.pair (encodedComparisonPrincipalNote (encodedComparisonOuter source).1) 1+3

def encodedComparisonQueryContexts (source : Nat × Nat) : List Nat :=
  [1,positiveExprEncode (.head profileOmegaNote .input),
    encodedComparisonHeadContext source.1,encodedComparisonHeadContext source.2]

/-- Finite explicit profile requests: raw requested profiles, mandatory
contexts, and both requested compositions with every relevant fixed context.
Invalid requests do not block the comparison tree; semantic gap claims retain
actual source profile-domain hypotheses. -/
def encodedComparisonQueryProfiles (q : ComparisonQuery) : List Nat :=
  [1,q.2.1,q.2.2]++encodedComparisonQueryContexts q.1++
    [q.2.1,q.2.2].flatMap (fun p => (encodedComparisonQueryContexts q.1).map (encodedProfileCompose p))

def encodedComparisonQueryRequests (q : ComparisonQuery) : List (Nat × Nat) :=
  [(1,1)]++(encodedComparisonQueryProfiles q).flatMap (fun p => [(p,1),(1,p)])

def encodedComparisonQueryChildren (q : ComparisonQuery) : List ComparisonQuery :=
  (encodedComparisonChildren q.1.1 q.1.2).flatMap (fun source =>
    (encodedComparisonQueryRequests q).map (fun profiles => (source,profiles)))

def encodedComparisonQueryFrontierStep (nodes : List ComparisonQuery) : List ComparisonQuery :=
  nodes.flatMap encodedComparisonQueryChildren

def encodedComparisonQueryFrontier (q : ComparisonQuery) (depth : Nat) : List ComparisonQuery :=
  (encodedComparisonQueryFrontierStep^[depth]) [q]

/-- ACTUAL computed original-source depth, not a caller-supplied query fuel. -/
noncomputable def encodedComparisonQueryLayers (q : ComparisonQuery) : List (List ComparisonQuery) :=
  (List.range (encodedComparisonTreeDepth q.1+1)).map (encodedComparisonQueryFrontier q)

end LogicLineages.OrdinalComparison
