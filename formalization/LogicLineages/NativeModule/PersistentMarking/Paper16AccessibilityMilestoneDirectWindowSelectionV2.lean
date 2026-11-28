module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDirectWindowSelectionV2

open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks (exact_OriginalValidWindow)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (exact_ConcreteLiteralDirectCarrierTuple)
open Paper16AccessibilityMilestoneTargetsV2 (SelectInstalledWindows)

/-- Each closed source universe has the direct installed packet at its original probe window. -/
theorem exact_SelectInstalledWindows : SelectInstalledWindows := by
  intro S K closed
  have valid := exact_OriginalValidWindow S K closed
  obtain ⟨scalar, cv, tv, raw, least, application, probes, packet⟩ :=
    exact_ConcreteLiteralDirectCarrierTuple S.entries (fixed S K) (sourceWindow K) valid
  exact ⟨sourceWindow K, ⟨⟨valid, scalar, cv, tv, raw, least, application, probes, packet.physical⟩⟩⟩

#print axioms exact_SelectInstalledWindows

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDirectWindowSelectionV2
