module
public import LogicLineages.OrdinalComparison.SourcePeakCallsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def LiteralPairStepWellFounded : Prop := ∀ budget, WellFounded (comparisonLiteralPairStep budget)

/-- Actual PP recursive peak children, including a raw source witness for
EVERY distinct canonical signed-row pair and strict measured child descent. -/
def ActualPositivePeakChildCalls : Prop :=
  ∀ (budget : Nat) (E F : FixedLimitPositiveExpr),
    fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
    let row := (signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2
    ∀ a∈row, ∀ b∈row, collectedTagKey a.1.1 a.1.2≠collectedTagKey b.1.1 b.1.2 →
    ∃ rawA rawB : FixedLimitPositiveExpr,
      (a.1.1,rawA)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
      (b.1.1,rawB)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
      collectedPositiveNormalize rawA=a.1.2 ∧ collectedPositiveNormalize rawB=b.1.2 ∧
      oneVariableComparisonValid (comparisonSourcePeakWord a.1.1 rawA) ∧
      oneVariableComparisonValid (comparisonSourcePeakWord b.1.1 rawB) ∧
      comparisonLiteralPairStep budget
        (comparisonSourcePeakWord a.1.1 rawA,comparisonSourcePeakWord b.1.1 rawB)
        (.positive E,.positive F)

/-- Actual nonlinear RP recursive calls; no abstract decrease premise and no
NF-to-source argument-size substitution. Any original range word is retained. -/
def ActualRangePositivePeakChildCalls : Prop :=
  ∀ (budget : Nat) (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr),
    fixedLimitProfileBelow epsilonZero P →
    ∀ p∈comparisonDisplayedSourceHeads P,
      oneVariableComparisonValid (comparisonSourcePeakWord p.1 p.2) ∧
      comparisonLiteralPairStep budget (.range w A,comparisonSourcePeakWord p.1 p.2)
        (.range w A,.positive P)

def FullActualSourcePeakChildCalls : Prop := LiteralPairStepWellFounded ∧
  ActualPositivePeakChildCalls ∧ ActualRangePositivePeakChildCalls

end LogicLineages.OrdinalComparison.Targets
