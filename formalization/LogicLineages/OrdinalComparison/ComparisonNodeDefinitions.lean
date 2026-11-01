module
public import LogicLineages.OrdinalComparison.ComparisonQueryDefinitions
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

abbrev ComparisonNodeResult := Nat × Nat
abbrev ComparisonNodeTable := List (ComparisonQuery × ComparisonNodeResult)

def comparisonNaturalSign (a b : Nat) : Nat := if a<b then 0 else if b<a then 2 else 1

noncomputable def encodedSourcePairSignAt (n m x : Nat) : Nat :=
  comparisonNaturalSign (encodedOneVariableComparisonValue n x) (encodedOneVariableComparisonValue m x)

def comparisonEventualSignData (E F : OneVariableComparisonExpr) (result : ComparisonNodeResult) : Prop :=
  result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat,result.2≤x →
    oneVariableComparisonDomainAt E x ∧ oneVariableComparisonDomainAt F x ∧
    (result.1=0 ↔ actualOneVariableComparisonValue E x<actualOneVariableComparisonValue F x) ∧
    (result.1=1 ↔ actualOneVariableComparisonValue E x=actualOneVariableComparisonValue F x) ∧
    (result.1=2 ↔ actualOneVariableComparisonValue F x<actualOneVariableComparisonValue E x)

/-- EXACT requested source gap for a bare limit outer exponent, retaining
its actual arbitrary source word argument and the original requested profile. -/
def comparisonBareLimitGap (E F : OneVariableComparisonExpr) (profile threshold : Nat) : Prop :=
  ∀ (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (A : FixedLimitPositiveExpr),
    E=.range (w++[(eta,c)]) A → Order.IsSuccLimit eta.1.repr →
    ∀ P : FixedLimitPositiveExpr,positiveExprEncode P=profile →
      fixedLimitProfileBelow (Ordinal.omega0^eta.1.repr) P →
      ∀ x : Nat,threshold≤x → actualFixedLimitProfileEval P (actualOneVariableComparisonValue F x)<
        actualOneVariableComparisonValue E x

def actualComparisonQueryCorrect (q : ComparisonQuery) (result : ComparisonNodeResult) : Prop :=
  ∀ E F : OneVariableComparisonExpr,
    oneVariableComparisonEncode E=q.1.1 → oneVariableComparisonEncode F=q.1.2 →
    oneVariableComparisonValid E → oneVariableComparisonValid F →
      comparisonEventualSignData E F result ∧
      (result.1=2 → comparisonBareLimitGap E F q.2.1 result.2) ∧
      (result.1=0 → comparisonBareLimitGap F E q.2.2 result.2)

/-- Ordinary finite induction hypothesis on the ACTUAL numeric child list;
not an extra assumption in the final source sign target. -/
def comparisonQueryTableCovers (q : ComparisonQuery) (table : ComparisonNodeTable) : Prop :=
  ∀ child∈encodedComparisonQueryChildren q,∃ result : ComparisonNodeResult,
    (child,result)∈table ∧ actualComparisonQueryCorrect child result

def encodedComparisonTableTail (table : ComparisonNodeTable) : Nat :=
  (table.map (fun p => p.2.2)).foldr max 1

noncomputable def encodedPositiveNodeLocalTail (n m : Nat) : Nat :=
  max (encodedPositiveZeroBound n m)
    ((encodedCollectedNormalize n).unpair.1+(encodedCollectedNormalize m).unpair.1+1)

noncomputable def encodedPositiveQueryNode (q : ComparisonQuery) (table : ComparisonNodeTable) : ComparisonNodeResult :=
  let threshold := max (encodedComparisonTableTail table) (encodedPositiveNodeLocalTail (q.1.1/2) (q.1.2/2))
  (encodedSourcePairSignAt q.1.1 q.1.2 threshold,threshold)

end LogicLineages.OrdinalComparison
