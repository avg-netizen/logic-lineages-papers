module
public import LogicLineages.OrdinalComparison.ComparisonQueryDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ComparisonQueryProgramsPrimitiveRecursive : Prop := Primrec encodedComparisonHeadContext ∧
  Primrec encodedComparisonQueryContexts ∧ Primrec encodedComparisonQueryProfiles ∧
  Primrec encodedComparisonQueryRequests ∧ Primrec encodedComparisonQueryChildren ∧
  Primrec encodedComparisonQueryFrontierStep ∧ Primrec₂ encodedComparisonQueryFrontier

def ActualComparisonQueryRequestCoverage : Prop :=
  (∀ (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr),
    encodedComparisonHeadContext (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))=
      positiveExprEncode (.head (comparisonPrincipalNote eta) .input)) ∧
  ∀ q : ComparisonQuery,
    (1,1)∈encodedComparisonQueryRequests q ∧
    (∀ p∈[1,q.2.1,q.2.2]++encodedComparisonQueryContexts q.1,
      (p,1)∈encodedComparisonQueryRequests q ∧ (1,p)∈encodedComparisonQueryRequests q) ∧
    ∀ p∈[q.2.1,q.2.2], ∀ context∈encodedComparisonQueryContexts q.1,
      (encodedProfileCompose p context,1)∈encodedComparisonQueryRequests q ∧
        (1,encodedProfileCompose p context)∈encodedComparisonQueryRequests q

def ActualComparisonQueryChildProjection : Prop :=
  ∀ q next : ComparisonQuery, next∈encodedComparisonQueryChildren q ↔
    next.1∈encodedComparisonChildren q.1.1 q.1.2 ∧ next.2∈encodedComparisonQueryRequests q

def ActualComparisonQueryFrontierProjection : Prop :=
  ∀ (q : ComparisonQuery) (depth : Nat), ∀ next∈encodedComparisonQueryFrontier q depth,
    next.1∈encodedComparisonFrontier q.1 depth

def ActualComparisonQueryLayersProgram : Prop := Computable encodedComparisonQueryLayers ∧
  ∀ q : ComparisonQuery,
    (encodedComparisonQueryLayers q).length=encodedComparisonTreeDepth q.1+1 ∧
    (encodedComparisonQueryLayers q).getD 0 []=[q] ∧
    (encodedComparisonQueryLayers q).getD (encodedComparisonTreeDepth q.1) []=[] ∧
    ∀ k<encodedComparisonTreeDepth q.1,
      (encodedComparisonQueryLayers q).getD (k+1) []=
        encodedComparisonQueryFrontierStep ((encodedComparisonQueryLayers q).getD k [])

def FullActualFiniteComparisonQueryTree : Prop := ComparisonQueryProgramsPrimitiveRecursive ∧
  ActualComparisonQueryRequestCoverage ∧ ActualComparisonQueryChildProjection ∧
  ActualComparisonQueryFrontierProjection ∧ ActualComparisonQueryLayersProgram

end LogicLineages.OrdinalComparison.Targets
