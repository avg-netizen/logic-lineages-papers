module
public import LogicLineages.OrdinalComparison.SourceCarrierClosureDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def DisplayedRawArgumentHeadContainment : Prop := ∀ E : FixedLimitPositiveExpr,
  ∀ p∈comparisonDisplayedSourceHeads E,
    p.1∈comparisonPositiveSourceHeads E ∧
    ∀ rho∈comparisonPositiveSourceHeads p.2,rho∈comparisonPositiveSourceHeads E

def ActualInitialPairBounds : Prop := ∀ E F : OneVariableComparisonExpr,
  oneVariableComparisonValid E → oneVariableComparisonValid F →
    let budget := encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F)
    comparisonSourceBounded budget E ∧ comparisonSourceBounded budget F

def ActualPeakChildBounds : Prop := ∀ (budget : Nat) (E : FixedLimitPositiveExpr),
  comparisonSourceBounded budget (.positive E) →
  ∀ p∈comparisonDisplayedSourceHeads E,
    comparisonSourceBounded budget (comparisonSourcePeakWord p.1 p.2)

def ActualStrippedChildBounds : Prop := ∀ (budget : Nat) (w : List (NONote × Nat))
  (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr),
  comparisonSourceBounded budget (.range (w++[(eta,c)]) E) →
    comparisonSourceBounded budget (comparisonLiteralInner w E)

/-- SAME fixed initial budget for the ACTUAL source returned by the whole
successor normalization. Its added constants/masses are deliberately NOT
bounded by the parent's conservative syntax budget. -/
def ActualNormalizedSourceBounds : Prop := ∀ (budget : Nat) (w : List (NONote × Nat))
  (E : FixedLimitPositiveExpr) (eta lower : NONote) (c : Nat),
  oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
  comparisonSourceBounded budget (.range (w++[(eta,c)]) E) →
  0<lower.1.repr → lower.1.repr<eta.1.repr →
    ∃ (added : List (NONote × Nat)) (last : NONote),
      (encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c).1=
          oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E) ∧
      comparisonSourceBounded budget (.range ((w++added)++[(last,c)]) E)

def FullActualFixedSourceCarrierClosure : Prop := DisplayedRawArgumentHeadContainment ∧
  ActualInitialPairBounds ∧ ActualPeakChildBounds ∧ ActualStrippedChildBounds ∧ ActualNormalizedSourceBounds

end LogicLineages.OrdinalComparison.Targets
