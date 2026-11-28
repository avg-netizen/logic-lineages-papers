module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledPacketV2
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowSelectionV2

open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks (exact_OriginalValidWindow)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (exact_ConcreteLiteralDirectCarrierTuple)
open Paper16AccessibilityMilestoneInstalledPacketV2 (installedOfPacket)
open Paper16AccessibilityMilestoneTargetsV2 (SelectInstalledWindows)

/-- Each closed source universe has an installation at its original probe window. -/
theorem exact_SelectInstalledWindows : SelectInstalledWindows := by
  intro S K closed
  have valid := exact_OriginalValidWindow S K closed
  obtain ⟨i, cv, tv, raw, least, application, probes, packet⟩ :=
    exact_ConcreteLiteralDirectCarrierTuple S.entries (fixed S K) (sourceWindow K) valid
  exact ⟨sourceWindow K, ⟨installedOfPacket valid i cv tv raw least application probes packet⟩⟩

#print axioms exact_SelectInstalledWindows

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowSelectionV2
