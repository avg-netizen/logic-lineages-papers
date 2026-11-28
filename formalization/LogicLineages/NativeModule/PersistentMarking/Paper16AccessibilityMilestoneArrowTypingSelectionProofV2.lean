module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindowV2

/-! Proof of the frozen
`Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2.InstalledAccessibilityReduction`
(Fable B, 27 November 2026).

The window is the joined lambda window of
`exact_InstalledLambdaWindowWithScalarAtOriginalWindow` with the three literal probe leaves
installed. Its finite scalar shape, application core, application-output rule, neutral
arithmetic and forward rule are the hypotheses of `exact_WindowReductionFromJoinedFacts`.

Gate status at writing: `Paper16AccessibilityMilestoneInstalledLambdaWindowV2` does not compile,
because of one unresolved identifier in the coordinator's uncommitted
`NumberedWindowInternalLiteralJoinedBetaOutcomeProof` (root ledger, 27 November). This module is
a draft until that dependency passes. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingSelectionProofV2

open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open Paper16AccessibilityMilestoneInstalledLambdaWindowV2
  (exact_InstalledLambdaWindowWithScalarAtOriginalWindow)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (ApplicationResultCarrier)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2
  (literalProbeWindow InstalledAccessibilityReduction)
open Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2 (exact_WindowReductionFromJoinedFacts)

/-- One installed window per closed source universe on which the type split reduces to the
fresh application and the all-terms sentence to the type split and typed computability. -/
theorem exact_InstalledAccessibilityReduction : InstalledAccessibilityReduction := by
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
  exact exact_WindowReductionFromJoinedFacts S K A _
    (hop A.contextGuard A.typeGuard
      (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
    neutralSource bottomSource scalar core c output arithmetic forward

#print axioms exact_InstalledAccessibilityReduction

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingSelectionProofV2
