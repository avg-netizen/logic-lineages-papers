module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsTargetsV2

/-! Frozen target: the result of an accepted application of a typed function is typed at the
codomain (`lem:arithmetic-accessibility`; rows B3 and D4 of
`verification/local-fable-trio-2026-11-27/fableB3/TYPED-COMPUTABILITY-MAP.md`; Fable B3,
27 November 2026).

`ApplicationResultTyped`: on an installed window with the type split `CarrierTypingCases A c`
and the joined rules, from `typedAt (σ→τ) x` and `accepts (windowApp A) x u t` derive
`typedAt τ t`. This is the typing premise the beta consumers of
`Paper16AccessibilityMilestoneBetaAddressProof` (`exact_OpenInstalledBetaDirectTypeField`) ask
for at an application result.

Assumed: the type split and the joined rules (both theorems on the window of
`FrontLiteralWindowTyping`). Not assumed: typing or computability of the argument, any carrier
premise. Not claimed: computability of the result. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneApplicationResultTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalNeutralFactsTargets (D)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow CarrierTypingCases)
open Paper16AccessibilityMilestoneTypedRowsTargetsV2 (windowApp JoinedAt)

/-- The result of an accepted application of a function typed at `σ→τ` is typed at `τ`. -/
def ApplicationResultTyped : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (L₀ : Program 3) (U : Program 2) (c : Nat), CarrierTypingCases A c → JoinedAt A L₀ U c →
    ∀ (σ τ : Ty) (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
      D A.presentation c Γ (typedAt (chosenH A.probes W) (formulaType (.arrow σ τ)) x) →
      D A.presentation c Γ (accepts (windowApp A) x u t) →
      D A.presentation c Γ (typedAt (chosenH A.probes W) (formulaType τ) t)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneApplicationResultTargetsV2
