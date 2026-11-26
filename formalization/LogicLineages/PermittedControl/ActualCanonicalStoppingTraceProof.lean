module
public import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceTargets
import LogicLineages.PermittedControl.ActualCanonicalStoppingTraceStrictProof
import LogicLineages.PermittedControl.ActualCanonicalNodeProgressProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
open ActualCanonicalZeroTrace ActualCanonicalReachedFunding ActualCanonicalNodeProgress

theorem exactFundedCanonicalStoppingTrace : ExactFundedCanonicalStoppingTrace := by
  intro f B selected ρ strict r top initial live ranked long transfer comparison
  have reached := fun answers s path =>
    exactCanonicalReachedProgress f B selected ρ strict r top initial s answers
      live ranked long transfer comparison path
  obtain ⟨answers,final,path,stop⟩ := exactCanonicalStrictStopping f B ρ r top initial reached
  obtain ⟨literal,finalLive,finalRank,origin,sameValue,cost⟩ :=
    exactCanonicalTraceReplay f B selected ρ r top initial final answers path
  have finalLong := (exactCanonicalReachFacts f B selected ρ r top initial final answers
    live ranked long path).2.2.1
  refine ⟨answers,encodeAnswers answers,final,path,stop,rfl,literal,finalLive live,
    finalRank ranked,finalLong,origin,sameValue,?_⟩
  simpa only [encodeAnswers,List.length_map] using cost

end LogicLineages.PermittedControl.ActualCanonicalStoppingTrace
