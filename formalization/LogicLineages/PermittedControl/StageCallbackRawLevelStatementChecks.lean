module
public import LogicLineages.PermittedControl.StageCallbackRawLevelTargets
import LogicLineages.PermittedControl.StageCallbackRawLevelProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
open StageCallbackRawLevel

theorem fixed_exactRawActivity : ExactRawActivity := exactRawActivity
theorem fixed_exactRawLevelEntries : ExactRawLevelEntries := exactRawLevelEntries
theorem fixed_exactRawSignedPackets : ExactRawSignedPackets := exactRawSignedPackets
theorem fixed_exactRawRowPackets : ExactRawRowPackets := exactRawRowPackets
theorem fixed_fullStageCallbackRawLevel : FullStageCallbackRawLevel :=
  ⟨fixed_exactRawActivity,fixed_exactRawLevelEntries,fixed_exactRawSignedPackets,
    fixed_exactRawRowPackets⟩

#print axioms fixed_exactRawActivity
#print axioms fixed_exactRawLevelEntries
#print axioms fixed_exactRawSignedPackets
#print axioms fixed_exactRawRowPackets
#print axioms fixed_fullStageCallbackRawLevel

end LogicLineages.PermittedControl.StatementChecks
