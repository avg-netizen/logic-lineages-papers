module
public import LogicLineages.OrdinalComparison.ComparisonNodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSourcePairPointSignProgram : Prop := Primrec₂ comparisonNaturalSign ∧
  Computable (fun p : Nat × Nat × Nat => encodedSourcePairSignAt p.1 p.2.1 p.2.2) ∧
  ∀ E F : OneVariableComparisonExpr,oneVariableComparisonValid E → oneVariableComparisonValid F →
    ∀ x : Nat,oneVariableComparisonDomainBound E≤x → oneVariableComparisonDomainBound F≤x →
      let sign := encodedSourcePairSignAt (oneVariableComparisonEncode E) (oneVariableComparisonEncode F) x
      sign≤2 ∧ (sign=0 ↔ actualOneVariableComparisonValue E x<actualOneVariableComparisonValue F x) ∧
      (sign=1 ↔ actualOneVariableComparisonValue E x=actualOneVariableComparisonValue F x) ∧
      (sign=2 ↔ actualOneVariableComparisonValue F x<actualOneVariableComparisonValue E x)

def ActualPositiveQueryNodeProgram : Prop := Primrec encodedComparisonTableTail ∧
  Computable₂ encodedPositiveNodeLocalTail ∧ Computable₂ encodedPositiveQueryNode

/-- ACTUAL PP local inductive step, with the exact finite computed child
queries and their proven result records as ordinary induction hypotheses.
No whole-source result is inferred until the actual bottom-up evaluator pays
these hypotheses and the RP/RR cases have also been established. -/
def ActualPositiveQueryNodeCorrect : Prop :=
  ∀ E F : FixedLimitPositiveExpr,fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
  ∀ (leftProfile rightProfile : Nat) (table : ComparisonNodeTable),
    let q : ComparisonQuery := ((oneVariableComparisonEncode (.positive E),oneVariableComparisonEncode (.positive F)),
      (leftProfile,rightProfile))
    comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedPositiveQueryNode q table)

def FullActualPositiveQueryNode : Prop := ActualSourcePairPointSignProgram ∧
  ActualPositiveQueryNodeProgram ∧ ActualPositiveQueryNodeCorrect

end LogicLineages.OrdinalComparison.Targets
