module
public import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTargets
public import LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawFundedTerminalCandidate
open OrdinalComparison MixedSameRankResidue
open ActualReadChargeIteration (ReadState RankBound stateValue stateCharge)
open ActualFiniteGlobalTail ActualGlobalComparisonCeiling ActualEffectiveTerminalSignBound
open ActualZeroClassReplacement ActualZeroClassOutputState
open ActualCanonicalZeroTrace ActualCanonicalStoppingTrace ActualCanonicalFundedTerminal
open ActualRawSignedStaticCeiling ActualRawCanonicalZeroTraceInclusion ActualRawCanonicalZeroPrefixes
open ActualRawCanonicalZeroReplay (replayCode)
open ActualSyntaxChargeBudget
open ActualFullLabelPairGuards (Answer)

/-- The real signed stopping witness occurs in the executable candidate
list at the existing effective budget. This is one direction, with
genuine actual source inputs and original signed truth attached. -/
def ExactRawFundedTerminalCandidate : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (ρ : Nat → Nat), StrictMono ρ →
  ∀ (r top : Nat) (initial : ReadState),
    liftedReads f ρ initial.reads → RankBound r top initial → LongState initial →
    PaidGlobalTail B r ρ (syntaxOf initial) → PaidComparisonCeiling B r ρ (syntaxOf initial) →
    inputSignBoundCode r initial.constant ((syntaxOf initial).map encodeWeighted) ≤ ρ top →
    ∃ (answers : List (List Answer)) (stopped : ReadState),
      let start := encodeSyntax (eraseState initial)
      let actual := entry answers stopped
      CanonicalTrace f B ρ r top answers initial stopped ∧
      StopsAt f B ρ r top stopped ∧ ForwardTruth f B ρ r top initial stopped ∧
      actual ∈ prefixes (syntaxBudgetCode r start.2) start ∧
      replayCode (actual.1,start) = some actual.2 ∧
      liftedReads f ρ stopped.reads ∧ RankBound r top stopped ∧ LongState stopped ∧
      OriginalRanks initial.reads stopped.reads ∧ stateValue initial = stateValue stopped ∧
      actual.1.length + stateCharge r stopped ≤ stateCharge r initial

end LogicLineages.PermittedControl.ActualRawFundedTerminalCandidate
