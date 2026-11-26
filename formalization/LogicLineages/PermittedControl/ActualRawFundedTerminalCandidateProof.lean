module
public import LogicLineages.PermittedControl.ActualRawFundedTerminalCandidateTargets
import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalProof
import LogicLineages.PermittedControl.ActualRawCanonicalZeroTraceInclusionProof
import LogicLineages.PermittedControl.ActualRawCanonicalZeroPrefixesProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawFundedTerminalCandidate
open ActualCanonicalFundedTerminal ActualCanonicalZeroTrace ActualCanonicalStoppingTrace
open ActualRawSignedStaticCeiling ActualRawCanonicalZeroTraceInclusion ActualRawCanonicalZeroPrefixes
open ActualReadChargeIteration (stateCharge)
open ActualSyntaxChargeBudget

theorem exactRawFundedTerminalCandidate : ExactRawFundedTerminalCandidate := by
  intro f B selected ρ strict r top initial live ranks long transfer comparison signPaid
  obtain ⟨answers,encoded,stopped,path,stop,truth,encoding,_typedReplay,endLive,endRanks,endLong,
    origin,sameValue,cost⟩ := exactFundedCanonicalTerminal f B selected ρ strict r top
      initial live ranks long transfer comparison signPaid
  let start := encodeSyntax (eraseState initial)
  let actual := entry answers stopped
  have member : actual ∈ prefixes (syntaxBudgetCode r start.2) start :=
    exactActualCanonicalBudgetInclusion f B selected ρ r top initial stopped answers path
  have rawReplay := (exactRawZeroPrefixReplay (syntaxBudgetCode r start.2) start actual member).1
  have exactCost : actual.1.length + stateCharge r stopped ≤ stateCharge r initial := by
    change (encodeAnswers answers).length + stateCharge r stopped ≤ stateCharge r initial
    rw [← encoding]
    exact cost
  exact ⟨answers,stopped,path,stop,truth,member,rawReplay,endLive,endRanks,endLong,
    origin,sameValue,exactCost⟩

end LogicLineages.PermittedControl.ActualRawFundedTerminalCandidate
