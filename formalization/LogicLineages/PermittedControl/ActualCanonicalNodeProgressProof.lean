module
public import LogicLineages.PermittedControl.ActualCanonicalNodeProgressTargets
import LogicLineages.PermittedControl.ActualCanonicalNodeProgressLocalProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalNodeProgress
open ActualCanonicalReachedFunding

theorem exactCanonicalReachedProgress : ExactCanonicalReachedProgress := by
  intro f B selected ρ strict r top initial reached answers live ranked long transfer comparison path
  obtain ⟨reachedLive,reachedRanks,_,_,_⟩ := exactCanonicalReachFacts f B selected ρ r top
    initial reached answers live ranked long path
  exact exactCanonicalLocalProgress f B selected ρ strict r top reached reachedLive reachedRanks
    (exactCanonicalReachedFunding f B selected ρ ρ r top initial reached answers strict
      (fun _ _ => rfl) live ranked long transfer comparison path)

end LogicLineages.PermittedControl.ActualCanonicalNodeProgress
