module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteProof
open NumberedWindowInternalCombinedMeasuredRouteTargets
open NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
  (exact_FullyMeasuredRoundApplicationLeast)

theorem exact_InstalledMeasuredRound : ExactInstalledMeasuredRound := by
  intro s V TV M M0 B T base body α Γ ctx dom cod f arg μ m fuel vertices out k K
    syn typed argument measured applied round member
  exact exact_FullyMeasuredRoundApplicationLeast V TV M M0 B T base s body α Γ
    ctx dom cod f arg μ m fuel vertices out k syn typed argument measured applied round member

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteProof
