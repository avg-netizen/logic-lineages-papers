module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFrontWindowProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureProofV2

/-! Proof of the frozen `FrontLiteralWindowTyping`
(`Paper16AccessibilityMilestoneFreshCarrierTargetsV2`; Fable B2, 27 November 2026): on the window
of `exact_FrontLiteralWindowWithSeedLeast`, K1 holds by `exact_FreshCarrierOnFrontWindow` from the
exported scalar and least equations, the least-report law, the open type guards and the domain
closure of the source window; with K2 already there, the type split holds outright. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontTypingProofV2

open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (FreshAddressCarrier)
open Paper16AccessibilityMilestoneDomainClosureProofV2 (exact_OriginalWindowDomain)
open Paper16AccessibilityMilestoneFrontWindowProofV2 (exact_FrontLiteralWindowWithSeedLeast)
open Paper16AccessibilityMilestoneFreshCarrierProofV2 (exact_FreshCarrierOnFrontWindow)
open Paper16AccessibilityMilestoneFreshCarrierTargetsV2

theorem exact_FrontLiteralWindowTyping : FrontLiteralWindowTyping := by
  intro S K closed
  obtain ⟨A, H, seed, V₀, leaves, other, base₀, T, baseM₀, L₀, X, vaFit, hFit, seedFit,
      shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards, rest⟩ :=
    exact_FrontLiteralWindowWithSeedLeast S K closed
  refine ⟨A, H, seed, V₀, leaves, other, base₀, T, baseM₀, L₀, X, vaFit, hFit, seedFit,
    shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards,
    fun c => ?_⟩
  obtain ⟨rules, k2, typing, allTerms⟩ := rest c
  have k1 : FreshAddressCarrier A c :=
    exact_FreshCarrierOnFrontWindow S K (sourceWindow K) A (fixed S K) X base₀ T V₀ baseM₀
      scalar leastCode selected guards (exact_OriginalWindowDomain K closed) c
  have split := typing k1
  exact ⟨rules, k1, k2, split, allTerms split⟩

#print axioms exact_FrontLiteralWindowTyping

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontTypingProofV2
