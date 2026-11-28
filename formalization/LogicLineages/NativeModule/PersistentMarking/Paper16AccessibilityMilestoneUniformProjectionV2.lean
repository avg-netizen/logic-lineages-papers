module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneUniformProjectionV2

open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledToUniform)

/-- Project the exact four interpreted programs and context from the installed
all-terms derivation into the uniform ordinal interface. -/
theorem exact_InstalledToUniform : InstalledToUniform := by
  intro accessible S K closed
  obtain ⟨W, A, c, allTerms⟩ := accessible S K closed
  exact ⟨A.scalar, jRaw A.scalar, A.path, dCore A.scalar A.path permutation,
    c, A.calibrated, allTerms⟩

#print axioms exact_InstalledToUniform

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneUniformProjectionV2
