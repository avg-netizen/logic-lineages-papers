module
public import LogicLineages.OrdinalComparison.RangeRangeNodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Exact literal successor pass on a genuine limit exponent: no hidden
rewrite of the original higher head when its requested profiles are retained. -/
def ActualSuccessorNormalizationLimitFixed : Prop :=
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta lower : NONote) (c : Nat),
    Order.IsSuccLimit eta.1.repr →
    encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
      (rawNoteEncode eta.1) (rawNoteEncode lower.1) c=
      (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),rawNoteEncode eta.1,
        max 1 (encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))))

def ActualRangeRangeQueryNodeProgram : Prop :=
  Primrec encodedRangeRangeLocalTail ∧ Computable₂ encodedRangeRangeQueryNode

def ActualRangeRangeQueryNodeCorrect : Prop :=
  ∀ (w v : List (NONote × Nat)) (E F : FixedLimitPositiveExpr),
    oneVariableComparisonValid (.range w E) → oneVariableComparisonValid (.range v F) →
  ∀ (leftProfile rightProfile : Nat) (table : ComparisonNodeTable),
    let q : ComparisonQuery := ((oneVariableComparisonEncode (.range w E),oneVariableComparisonEncode (.range v F)),
      (leftProfile,rightProfile))
    comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedRangeRangeQueryNode q table)

def FullActualRangeRangeQueryNode : Prop := ActualSuccessorNormalizationLimitFixed ∧
  ActualRangeRangeQueryNodeProgram ∧ ActualRangeRangeQueryNodeCorrect

end LogicLineages.OrdinalComparison.Targets
