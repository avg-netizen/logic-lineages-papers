module
public import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceTargets
public import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection MixedSameRankResidue
open ActualCanonicalOperandGrouping ActualCanonicalStoppingTrace ActualNormalizedTape
open ActualZeroClassReplacement ActualMixedRowLeadingAnnotations ActualMixedRowLeadingSum
open ActualReadChargeIteration (ReadState ActiveAt RankBound stateValue)
open ActualLinearExit
open ActualSyntaxLinearTerminal (termsTable termsRow)
open OriginalMatrixLinearRowFormula (testFormula choosePolarity)
open ActualPreparedSlotAppend (Packet)
open ActualSignedOrdinaryPairHigh (OrderTest)
open SignedRowGuardedTest (Test)

noncomputable def canonicalPacket (top : Nat) (constant : Int) (raw : List WeightedOperand)
    (test : Test) (positive : Bool) : Packet :=
  let terms := groupTyped raw
  (termsTable top terms,choosePolarity (testFormula test (termsRow top constant terms)) positive)

def ExactCertifiedLinearExit : Prop :=
  ∀ (f ρ : Nat → Nat) (zRank : Nat) (constant : Int) (raw xs : List Read),
    (∀ rd ∈ raw, rd.1.2.rank ≤ zRank) → NormalizedTape f ρ raw xs →
    (¬ ∃ rd ∈ xs, rd.1.1 ≠ 0 ∧ rd.1.2.rank = zRank ∧ NonlinearOperand rd.1.2) →
    let retained := lowerReads zRank xs
    let ops := table zRank xs
    let row := exitRow zRank constant xs
    PreparedInput ops (.atom (.nonnegative row)) ∧
    (∃ ν : Nat → Nat, OriginalSlots ν retained ∧ PreparedTableTied f zRank ρ ops ν) ∧
    (∀ ν : Nat → Nat, PreparedTableTied f zRank ρ ops ν →
      OriginalSlots ν retained ∧
      (∀ (j : Nat) (hj : j < ops.length),
        lowerOperandRead f ρ ops[j] = some (some (ν (j+1)))) ∧
      (∀ z : Nat, PreparedTableTied f zRank (Function.update ρ zRank z) ops
          (Function.update ν 0 z) ∧
        liftedReads f (Function.update ρ zRank z) (replay zRank z xs) ∧
        NormalForm.rowValue row (Function.update ν 0 z) =
          constant + readSum (replay zRank z xs)) ∧
      NormalForm.rowValue row (Function.update ν 0 (ρ zRank)) = constant + readSum raw)

def ExactCanonicalInactiveTruth : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (constant : Int)
    (rs xs : List Read),
    liftedReads f ρ rs → (∀ rd ∈ rs, rd.1.2.rank ≤ top) →
    normalizeCanonical f ρ rs = some xs → ¬ ActiveAt top xs →
    ∀ (test : Test) (positive : Bool), test.Admitted →
      let q := canonicalPacket top constant (rs.map Prod.fst) test positive
      PreparedInput q.1 q.2 ∧
      (∃ ν : Nat → Nat, PreparedTableTied f top ρ q.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ q.1 ν →
        OriginalSlots ν (lowerReads top xs) ∧
        (∀ (j : Nat) (hj : j < q.1.length),
          lowerOperandRead f ρ q.1[j] = some (some (ν (j+1)))) ∧
        ((q.2.eval (Function.update ν 0 (ρ top))) ↔ test.atPolarity positive (constant + readSum rs)) ∧
        ∀ z : Nat,
          liftedReads f (Function.update ρ top z) (replay top z xs) ∧
            ((q.2.eval (Function.update ν 0 z)) ↔ test.atPolarity positive (constant + readSum (replay top z xs)))

/-- Payment is the actual numeric current-row cutoff. No assertion
about a global trace bound, nor about congruence from a sign. -/
def ExactCanonicalNonzeroTruth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ → ∀ (r top : Nat) (s : ReadState) (xs : List Read),
    liftedReads f ρ s.reads → RankBound r top s →
    normalizeCanonical f ρ s.reads = some xs → NonzeroStop f B ρ r top s xs →
    rowCutoffCode s.constant ((xs.map Prod.fst).map encodeWeighted) ≤ ρ top →
    ∃ (a : List ActualFullLabelPairGuards.Answer)
      (anns : List Annotation) (C : Nat),
      let terms := xs.map Prod.fst
      let coef := ActualFullValueMaximalMetadata.maximalCoefficient terms a
      ActualFiniteFullValueGuards.Matches f ρ (ActualFiniteFullValueGuards.pairs
        (ActualFullValueLabels.labels terms)) a ∧
      AlignedAnnotations f ρ terms (xs.map Prod.snd) anns ∧ (fullValues f anns).max? = some C ∧
      coef = (rowParts f C terms (xs.map Prod.snd) anns).1 ∧ coef ≠ 0 ∧
      2 * stateValue s = coef * (C : Int) + 2 * (s.constant + (rowParts f C terms (xs.map Prod.snd) anns).2) ∧
      (s.constant + (rowParts f C terms (xs.map Prod.snd) anns).2).natAbs ≤
        slopeBound terms * Nat.log2 C + (s.constant.natAbs + offsetBound terms) ∧
      (0 < stateValue s ↔ 0 < coef) ∧ (stateValue s < 0 ↔ coef < 0) ∧
      (0 ≤ stateValue s ↔ 0 < coef) ∧ stateValue s ≠ 0 ∧
      ∀ (test : OrderTest) (positive : Bool),
        test.test.atPolarity positive (stateValue s) ↔ test.test.atPolarity positive coef

def FullActualCanonicalTerminalTruth : Prop :=
  ExactCertifiedLinearExit ∧ ExactCanonicalInactiveTruth ∧ ExactCanonicalNonzeroTruth

end LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
