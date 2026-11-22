module
public import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTargets
import LogicLineages.PermittedControl.ActualCanonicalFundedTerminalTruthProof
import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
open ActualCanonicalStoppingTrace

theorem exactFundedCanonicalTerminal : ExactFundedCanonicalTerminal := by
  intro f B selected ρ strict r top initial live ranks long transfer comparisons signPaid
  obtain ⟨answers,rawAnswers,stopped,path,stop,encoding,literal,endLive,endRanks,endLong,
    origin,sameValue,cost⟩ := exactFundedCanonicalStoppingTrace f B selected ρ strict r top
      initial live ranks long transfer comparisons
  have truth := exactFundedForwardTruth f B selected ρ strict r top initial stopped answers
    live ranks long signPaid path stop
  exact ⟨answers,rawAnswers,stopped,path,stop,truth,encoding,literal,endLive,endRanks,endLong,
    origin,sameValue,cost⟩

end LogicLineages.PermittedControl.ActualCanonicalFundedTerminal
