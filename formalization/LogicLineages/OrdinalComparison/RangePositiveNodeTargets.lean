module
public import LogicLineages.OrdinalComparison.RangePositiveNodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualOpenSourceUnconditionalGrowth : Prop := ∀ E : OneVariableComparisonExpr,
  oneVariableComparisonValid E → oneVariableComparisonOpen E →
    ∀ x : Nat,x≤actualOneVariableComparisonValue E x

def ActualGenuineRangeSourceImage : Prop :=
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range w E) → ∀ x : Nat,
      oneVariableComparisonDomainAt (.range w E) x →
        actualOneVariableComparisonValue (.range w E) x∈Set.range Phi

def ActualRangePositiveQueryNodeProgram : Prop :=
  Computable (fun p : Nat × Nat × Nat => encodedRangePositiveLocalTail p.1 p.2.1 p.2.2) ∧
  Computable₂ encodedRangePositiveQueryNode

def ActualRangePositiveQueryNodeCorrect : Prop :=
  ∀ (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range w A) → fixedLimitProfileBelow epsilonZero P →
  ∀ (leftProfile rightProfile : Nat) (table : ComparisonNodeTable),
    let q : ComparisonQuery := ((oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (.positive P)),
      (leftProfile,rightProfile))
    comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedRangePositiveQueryNode q table)

def ActualPositiveRangeQueryNodeCorrect : Prop :=
  ∀ (w : List (NONote × Nat)) (P A : FixedLimitPositiveExpr),
    fixedLimitProfileBelow epsilonZero P → oneVariableComparisonValid (.range w A) →
  ∀ (leftProfile rightProfile : Nat) (table : ComparisonNodeTable),
    let q : ComparisonQuery := ((oneVariableComparisonEncode (.positive P),oneVariableComparisonEncode (.range w A)),
      (leftProfile,rightProfile))
    comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedRangePositiveQueryNode q table)

def FullActualRangePositiveQueryNode : Prop := ActualOpenSourceUnconditionalGrowth ∧ ActualGenuineRangeSourceImage ∧
  ActualRangePositiveQueryNodeProgram ∧ ActualRangePositiveQueryNodeCorrect ∧ ActualPositiveRangeQueryNodeCorrect

end LogicLineages.OrdinalComparison.Targets
