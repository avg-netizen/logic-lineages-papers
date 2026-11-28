module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFrontRowsTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFrontTypingProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneGeneralSeedLeastProofV2

/-! Proof of the frozen `FrontLiteralWindowRows`
(`Paper16AccessibilityMilestoneFrontRowsTargetsV2`; Fable B3, 27 November 2026): on the window
of `exact_FrontLiteralWindowTyping`, K2 for arbitrary carriers holds by
`exact_GeneralSeedLeastOnJoinedWindow` from the exported scalar and least equations, the
least-report law and the open type guards; the all-terms sentence follows from the four open
rows by `exact_TypedComputabilityFromRows` (exported guard equation and joined rules) and the
window's own reduction `TypedCarrierComputability A c → AllTerms A c`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontRowsProofV2

open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase)
open Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2 (variableFrontSyntax)
open Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2 (variableFrontWindow)
open Paper16AccessibilityMilestoneFrontTypingProofV2 (exact_FrontLiteralWindowTyping)
open Paper16AccessibilityMilestoneTypedRowsProofV2 (exact_TypedComputabilityFromRows)
open Paper16AccessibilityMilestoneGeneralSeedLeastProofV2 (exact_GeneralSeedLeastOnJoinedWindow)
open Paper16AccessibilityMilestoneFrontRowsTargetsV2

theorem exact_FrontLiteralWindowRows : FrontLiteralWindowRows := by
  intro S K closed
  obtain ⟨A, H, seed, V₀, leaves, other, base₀, T, baseM₀, L₀, X, vaFit, hFit, seedFit,
      shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards, rest⟩ :=
    exact_FrontLiteralWindowTyping S K closed
  refine ⟨A, H, seed, V₀, leaves, other, base₀, T, baseM₀, L₀, X, vaFit, hFit, seedFit,
    shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards,
    fun c => ?_⟩
  obtain ⟨rules, k1, k2, typing, allTerms⟩ := rest c
  have general := exact_GeneralSeedLeastOnJoinedWindow S K (sourceWindow K) A (fixed S K) X
    (variableFrontWindow (selectedBiAuxType (fixed S K) T A.typeGuard) base₀) T
    (variableFrontSyntax A.typeGuard V₀) (namedMeasureBase baseM₀) scalar leastCode selected
    guards c
  exact ⟨rules, k1, k2, typing, allTerms, general, fun neutralRow groundRow reductRow
    instanceRow => allTerms (exact_TypedComputabilityFromRows S K (sourceWindow K) A L₀ _ c
      guard rules neutralRow groundRow reductRow instanceRow)⟩

#print axioms exact_FrontLiteralWindowRows

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontRowsProofV2
