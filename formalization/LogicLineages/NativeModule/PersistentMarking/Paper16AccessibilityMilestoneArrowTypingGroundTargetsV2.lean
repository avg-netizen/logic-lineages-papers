module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2

/-! Frozen target: the reduction of `lem:arithmetic-accessibility` on closed source universes
without arrow types (Fable B, 27 November 2026).

When every type of the closed universe `K` is ground, the window `sourceWindow K` lists no arrow
type, so `FreshApplicationTotal` has no instance to supply and the type split holds outright. The
all-terms sentence then needs typed carrier computability only. This is the degenerate case of
`InstalledAccessibilityReduction`; it asserts nothing at arrow types and does not assert
`TypedCarrierComputability`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2

open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open Paper16AccessibilityMilestoneTargetsV2
  (InstalledWindow CarrierTypingCases TypedCarrierComputability AllTerms)

/-- On a closed universe of ground types there is an installed window with the type split, on
which typed carrier computability gives the all-terms sentence. -/
def GroundUniverseReduction : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    (∀ τ ∈ K, τ = Ty.ground) →
    ∃ A : InstalledWindow S K (sourceWindow K), ∀ c : Nat,
      CarrierTypingCases A c ∧ (TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2
