module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def DisplayedSourceHeadProgram : Prop :=
  Primrec encodedDisplayedSourceHeads ∧ ∀ E : FixedLimitPositiveExpr,
    encodedDisplayedSourceHeads (positiveExprEncode E)=
      (comparisonDisplayedSourceHeads E).map (fun p => (rawNoteEncode p.1.1,positiveExprEncode p.2))

def DisplayedSourceHeadValidity : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    ∀ p∈comparisonDisplayedSourceHeads E,
      Order.IsSuccLimit p.1.1.repr ∧ p.1.1.repr<epsilonZero ∧
      fixedLimitProfileBelow epsilonZero p.2 ∧ positiveExprHasInput p.2=true

def DisplayedSourceHeadOccurrenceBudget : Prop :=
  ∀ E : FixedLimitPositiveExpr,
    ((comparisonDisplayedSourceHeads E).map (fun p => comparisonPositiveSourceHeadCount p.2+1)).sum≤
      comparisonPositiveSourceHeadCount E

def DisplayedSourceArgumentDrop : Prop :=
  (∀ E : FixedLimitPositiveExpr, ∀ p∈comparisonDisplayedSourceHeads E,
    comparisonPositiveSourceHeadCount p.2<comparisonPositiveSourceHeadCount E) ∧
  ∀ (E F : FixedLimitPositiveExpr) (p q : NONote × FixedLimitPositiveExpr),
    p∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F →
    q∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F → p≠q →
    comparisonPositiveSourceHeadCount p.2+comparisonPositiveSourceHeadCount q.2<
      comparisonPositiveSourceHeadCount E+comparisonPositiveSourceHeadCount F

/-- Every ACTUAL normalized root retains an original displayed raw argument,
not just a head label that happens to occur somewhere in the source. -/
def CollectedRootRawSourceProvenance : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E →
    ∀ (rho : NONote) (A : CollectedPositiveNF),
    (rho,A)∈collectedSourceRootTags (collectedPositiveNormalize E) →
    ∃ raw : FixedLimitPositiveExpr, (rho,raw)∈comparisonDisplayedSourceHeads E ∧ collectedPositiveNormalize raw=A

/-- Exact recursive P/P row provenance AND strict raw-argument h decrease
for every pair of genuinely distinct displayed canonical tags. -/
def SignedRowRawSourceArgumentDrop : Prop :=
  ∀ E F : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
    let row := (signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2
    (∀ entry∈row, ∃ raw : FixedLimitPositiveExpr,
      (entry.1.1,raw)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
      collectedPositiveNormalize raw=entry.1.2) ∧
    ∀ a∈row, ∀ b∈row, collectedTagKey a.1.1 a.1.2≠collectedTagKey b.1.1 b.1.2 →
      ∃ rawA rawB : FixedLimitPositiveExpr,
        (a.1.1,rawA)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
        (b.1.1,rawB)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
        collectedPositiveNormalize rawA=a.1.2 ∧ collectedPositiveNormalize rawB=b.1.2 ∧
        comparisonPositiveSourceHeadCount rawA+comparisonPositiveSourceHeadCount rawB<
          comparisonPositiveSourceHeadCount E+comparisonPositiveSourceHeadCount F

/-- Whole actual source head-coordinate supplier for sign/certificate
recursion. No normalized/raw-size identification or decrease oracle. -/
def FullDisplayedSourceHeads : Prop := DisplayedSourceHeadProgram ∧ DisplayedSourceHeadValidity ∧
  DisplayedSourceHeadOccurrenceBudget ∧ DisplayedSourceArgumentDrop ∧
  CollectedRootRawSourceProvenance ∧ SignedRowRawSourceArgumentDrop

end LogicLineages.OrdinalComparison.Targets
