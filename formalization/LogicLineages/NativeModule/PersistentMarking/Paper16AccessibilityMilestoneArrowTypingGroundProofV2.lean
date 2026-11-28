module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingSelectionProofV2

/-! Proof of the frozen
`Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2.GroundUniverseReduction`
(Fable B, 27 November 2026): the window of `exact_InstalledAccessibilityReduction`, with the
fresh-application premise discharged because no arrow type is listed. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingGroundProofV2

open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (FreshApplicationTotal)
open Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2
open Paper16AccessibilityMilestoneArrowTypingSelectionProofV2 (exact_InstalledAccessibilityReduction)

/-- The type split holds outright on ground universes, and the all-terms sentence follows from
typed carrier computability. -/
theorem exact_GroundUniverseReduction : GroundUniverseReduction := by
  intro S K closed allGround
  obtain ⟨A, reduce⟩ := exact_InstalledAccessibilityReduction S K closed
  refine ⟨A, fun c => ?_⟩
  have total : FreshApplicationTotal A c := by
    intro σ τ listed
    obtain ⟨τ₀, hτ₀, same⟩ := List.mem_map.mp listed
    have ground := allGround τ₀ hτ₀
    subst ground
    have impossible : (.ground : ProbeTy) = (.arrow σ τ : ProbeTy) := same
    cases impossible
  have typing := (reduce c).1 total
  exact ⟨typing, (reduce c).2 typing⟩

#print axioms exact_GroundUniverseReduction

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingGroundProofV2
