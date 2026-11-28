module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindowV2

/-! Proof of the frozen
`Paper16AccessibilityMilestoneFreshApplicationTargetsV2.InstalledAccessibilityFromLeast`
(Fable B, 27 November 2026): the window of `exact_InstalledAccessibilityReduction` (the joined
lambda window with literal probe leaves), with the fresh application replaced by K1 and K2
through `exact_FreshApplicationFromLeast`. The reinstallation keeps the scalar, the least
program and the application guard, so the guard equation of the joined window applies. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationSelectionProofV2

open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open Paper16AccessibilityMilestoneInstalledLambdaWindowV2
  (exact_InstalledLambdaWindowWithScalarAtOriginalWindow)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (ApplicationResultCarrier)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)
open Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2 (exact_WindowReductionFromJoinedFacts)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2
open Paper16AccessibilityMilestoneFreshApplicationProofV2 (exact_FreshApplicationFromLeast)

/-- One installed window per closed source universe on which K1 and K2 give the type split,
and the type split with typed carrier computability gives the all-terms sentence. -/
theorem exact_InstalledAccessibilityFromLeast : InstalledAccessibilityFromLeast := by
  intro S K closed
  obtain ⟨A, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, scalar, core, guard, rules⟩ :=
    exact_InstalledLambdaWindowWithScalarAtOriginalWindow S K closed
  refine ⟨literalProbeWindow A, fun c => ?_⟩
  have output : ApplicationResultCarrier A c := by
    intro α Γ x u t app
    rw [guard] at app
    exact ((rules c).applicationOutput α Γ x u t app).1
  have arithmetic := (rules c).arithmetic
  have forward := (rules c).forward
  rw [← guard] at arithmetic forward
  obtain ⟨typingFrom, allTerms⟩ := exact_WindowReductionFromJoinedFacts S K A _
    (hop A.contextGuard A.typeGuard
      (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
    neutralSource bottomSource scalar core c output arithmetic forward
  exact ⟨fun k1 k2 => typingFrom
    (exact_FreshApplicationFromLeast S K (sourceWindow K) (literalProbeWindow A) guard c k1 k2),
    allTerms⟩

#print axioms exact_InstalledAccessibilityFromLeast

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationSelectionProofV2
