module

public import LogicLineages.NativeModule.PersistentMarking.NativeRankChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedStrictWellFoundedChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeSyntaxCountabilityChecks

/-! Not a twin: a new assembly module (Opus B, round 2) on the module-system twin tree.
It discharges the three hypotheses of the drafted `NativeRankChecks.compose` with the
checked suppliers, giving the frozen `NativeRankGlobalTargets.ActualClosedNativeRanks`
(twin sha256 edfeefe1…a774) with no hypothesis. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRankUnconditionalChecks

theorem exact_ActualClosedNativeRanks : NativeRankGlobalTargets.ActualClosedNativeRanks :=
  NativeRankChecks.compose
    NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded
    NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded
    NativeSyntaxCountabilityChecks.exact_ClosedNativeCountability

#print axioms exact_ActualClosedNativeRanks

end LogicLineages.PersistentMarking.NativeRankUnconditionalChecks
