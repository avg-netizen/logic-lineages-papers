module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneWindowSelection
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalFixedSeedCoverageProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalFixedSettingsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneJoinedWindowSelection

open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks (exact_OriginalValidWindow)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowOriginalFixedSeedCoverageProof (exact_FixedWindowSeedsCovered)
open NumberedWindowOriginalFixedSettingsProof
  (exact_FixedGrammarTypeInclusion exact_FixedWindowTypeIncluded exact_FixedHeadPairsSymmetric)
open NumberedWindowOriginalProbeTotalChecks (exact_FormulaTypeCoding)
open Paper16AccessibilityMilestoneInstalledPacket (JoinedBetaWindow exact_JoinedLambdaWindow)

theorem exact_OriginalFiniteCodesIncluded (S : Spine.Signature) (K : List Ty)
    (closed : DecisionSourceUniverse.Closed K) :
    ∀ n ∈ finiteCodes (sourceWindow K), n ∈ (fixed S K).window.1 := by
  intro n hn
  apply exact_FixedWindowTypeIncluded S K closed
  obtain ⟨probeTy, hprobeTy, rfl⟩ := List.mem_map.mp hn
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hprobeTy
  exact List.mem_map.mpr ⟨τ, hτ, (exact_FormulaTypeCoding τ).symm⟩

/-- The installed packet with the contextual lambda fallback at the original source window. -/
theorem exact_JoinedLambdaWindowAtOriginalWindow (S : Spine.Signature) (K : List Ty)
    (closed : DecisionSourceUniverse.Closed K) : JoinedBetaWindow S K (sourceWindow K) :=
  exact_JoinedLambdaWindow
    (exact_OriginalValidWindow S K closed)
    (exact_FixedWindowSeedsCovered S K)
    (exact_FixedHeadPairsSymmetric S K)
    (exact_FixedGrammarTypeInclusion S K)
    (exact_OriginalFiniteCodesIncluded S K closed)

#print axioms exact_OriginalFiniteCodesIncluded
#print axioms exact_JoinedLambdaWindowAtOriginalWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneJoinedWindowSelection
