module
public import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthTargets
public import LogicLineages.PermittedControl.ActualCanonicalSignFundingTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
open OrdinalComparison PreparedProjection MixedSameRankResidue
open ActualReadChargeIteration (ReadState RankBound ActiveAt stateValue stateCharge)
open ActualCanonicalZeroTrace ActualCanonicalOperandGrouping ActualCanonicalStoppingTrace
open ActualCanonicalTerminalTruth ActualEffectiveTerminalSignBound
open ActualFiniteGlobalTail ActualGlobalComparisonCeiling
open ActualZeroClassReplacement ActualZeroClassOutputState ActualLinearExit
open ActualFullLabelPairGuards ActualFullValueLabels ActualFiniteFullValueGuards ActualFullValueMaximalMetadata
open ActualMixedRowLeadingSum (rowCutoffCode)
open ActualSignedOrdinaryPairHigh (OrderTest)

/-- At the actual inactive highest node, retain the literal read table
and the requested signed order test. Every valid tied slot assignment,
not just the chosen recorded one, gives the same actual input truth. -/
def LinearForward (f ρ : Nat → Nat) (top : Nat) (source stopped : ReadState)
    (xs : List Read) : Prop :=
  ∀ (test : OrderTest) (positive : Bool),
    let packet := canonicalPacket top stopped.constant (stopped.reads.map Prod.fst) test.test positive
    PreparedInput packet.1 packet.2 ∧ (∃ ν, PreparedTableTied f top ρ packet.1 ν) ∧
    ∀ ν, PreparedTableTied f top ρ packet.1 ν →
      OriginalSlots ν (lowerReads top xs) ∧
      (∀ (j : Nat) (h : j < packet.1.length),
        lowerOperandRead f ρ packet.1[j] = some (some (ν (j+1)))) ∧
      (packet.2.eval (Function.update ν 0 (ρ top)) ↔ test.test.atPolarity positive (stateValue source))

/-- The original nonzero node still has its true actual compared branch
and signed decomposition, with the current numeric cutoff paid. -/
def NonzeroForward (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (source stopped : ReadState) (xs : List Read) : Prop :=
  NonzeroStop f B ρ r top stopped xs ∧
  rowCutoffCode stopped.constant ((xs.map Prod.fst).map encodeWeighted) ≤ ρ top ∧
  ∃ a : List Answer,
    let terms := xs.map Prod.fst
    let coef := maximalCoefficient terms a
    Matches f ρ (pairs (labels terms)) a ∧ coef ≠ 0 ∧
    ∀ (test : OrderTest) (positive : Bool),
      test.test.atPolarity positive (stateValue source) ↔ test.test.atPolarity positive coef

def ForwardTruth (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r top : Nat)
    (source stopped : ReadState) : Prop :=
  ∃ xs, normalizeCanonical f ρ stopped.reads = some xs ∧ liftedReads f ρ xs ∧
    ((¬ ActiveAt top xs ∧ LinearForward f ρ top source stopped xs) ∨
      (ActiveAt top xs ∧ NonzeroForward f B ρ r top source stopped xs))

def ExactFundedForwardTruth : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (initial stopped : ReadState) (answers : List (List Answer)),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤ ρ top →
    CanonicalTrace f B ρ r top answers initial stopped → StopsAt f B ρ r top stopped →
    ForwardTruth f B ρ r top initial stopped

def ExactFundedCanonicalTerminal : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (initial : ReadState),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) → PaidComparisonCeiling B r ρ (syntaxOf initial) →
    inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤ ρ top →
    ∃ (answers : List (List Answer)) (rawAnswers : List (List Nat)) (stopped : ReadState),
      CanonicalTrace f B ρ r top answers initial stopped ∧
      StopsAt f B ρ r top stopped ∧ ForwardTruth f B ρ r top initial stopped ∧
      rawAnswers = encodeAnswers answers ∧
      replay answers (eraseState initial) = some (eraseState stopped) ∧
      liftedReads f ρ stopped.reads ∧ RankBound r top stopped ∧ LongState stopped ∧
      OriginalRanks initial.reads stopped.reads ∧ stateValue initial = stateValue stopped ∧
      rawAnswers.length + stateCharge r stopped ≤ stateCharge r initial

def FullActualCanonicalFundedTerminal : Prop :=
  ExactFundedForwardTruth ∧ ExactFundedCanonicalTerminal

end LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
