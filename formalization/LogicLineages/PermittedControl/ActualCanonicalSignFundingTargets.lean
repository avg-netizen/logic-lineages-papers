module
public import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTargets
public import LogicLineages.PermittedControl.ActualEffectiveTerminalSignBoundTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSignFunding
open OrdinalComparison MixedSameRankResidue PreparedProjection
open ActualCanonicalZeroTrace ActualCanonicalOperandGrouping ActualFiniteGlobalTail
open ActualReadChargeIteration (ReadState RankBound)
open ActualZeroClassReplacement ActualZeroEdgeAlphabet ActualSignedReadMass
open ActualZeroEdgeConstantShift ActualTraceSignCutoff ActualEffectiveTerminalSignBound
open ActualFullLabelPairGuards (Answer)
open ActualMixedRowLeadingSum (rowCutoffCode)

def ExactCanonicalNormalizedMass : Prop :=
  ∀ (f ρ : Nat → Nat) (raw xs : List Read),
    liftedReads f ρ raw → normalizeCanonical f ρ raw = some xs → signedMass xs ≤ signedMass raw

def ExactCanonicalEdgeMass : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat) (s t : ReadState)
    (a : List Answer), CanonicalZeroWitness f B ρ r top s t a →
    signedMass t.reads ≤ 3 * signedMass s.reads

def ExactCanonicalShift : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (s t : ReadState) (a : List Answer) (alphabet : List LowerOperand),
    CanonicalZeroWitness f B ρ r top s t a → Covers alphabet s →
    (t.constant - s.constant).natAbs ≤ signedMass s.reads * edgeFactor alphabet ∧
    t.constant.natAbs ≤ s.constant.natAbs + signedMass s.reads * edgeFactor alphabet

def ExactCanonicalTraceMass : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    CanonicalTrace f B ρ r top answers initial reached →
    signedMass reached.reads ≤ 3 ^ answers.length * signedMass initial.reads ∧
    signedMass reached.reads ≤ massCeiling r initial

def ExactCanonicalTraceConstant : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    CanonicalTrace f B ρ r top answers initial reached →
    reached.constant.natAbs ≤ initial.constant.natAbs + answers.length * stepCeiling r initial ∧
    reached.constant.natAbs ≤ constantCeiling r initial

/-- Same actual path, no legacy trace premise. Payment at the original
highest coordinate stays explicit. -/
def ExactCanonicalSignFunding : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat) (r top : Nat) (initial reached : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    CanonicalTrace f B ρ r top answers initial reached →
    ∀ xs, normalizeCanonical f ρ reached.reads = some xs →
      let rowCutoff := rowCutoffCode reached.constant ((xs.map Prod.fst).map encodeWeighted)
      let staticCutoff := inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted)
      rowCutoff ≤ terminalCutoffCeiling r initial ∧
      rowCutoff ≤ staticCutoff ∧ (staticCutoff ≤ ρ top → rowCutoff ≤ ρ top)

def FullActualCanonicalSignFunding : Prop :=
  ExactCanonicalNormalizedMass ∧ ExactCanonicalEdgeMass ∧ ExactCanonicalShift ∧
  ExactCanonicalTraceMass ∧ ExactCanonicalTraceConstant ∧ ExactCanonicalSignFunding

end LogicLineages.PermittedControl.ActualCanonicalSignFunding
