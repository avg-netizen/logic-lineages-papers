module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2

/-! Frozen targets: K2 for arbitrary scalar carriers (`lem:arithmetic-accessibility`; the
totality half of backward application matching and of application decoding, rows N7 and D3 of
`verification/local-fable-trio-2026-11-27/fableB3/TYPED-COMPUTABILITY-MAP.md`; Fable B3,
27 November 2026).

`GeneralSeedLeast A c`: for any two scalar carriers `q`, `u` whose address reports share the
context `ctx` and have result fields `rawCons dom cod` and `dom`, the installed least program
returns a successor on the application seed `auxiliaryTerm dom cod fn arg` at context `ctx` and
type `cod`. This is `FreshSeedLeast` without its listed-type, stored-type and fresh-selector
premises.

`GeneralSeedLeastOnJoinedWindow`: the law holds on every installed window satisfying the
hypotheses of `Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2.SeedLeastOnJoinedWindow`
(scalar and least equations, `MemoSelectedReports`, `OpenRankTypeGuards`), hence on the window
of `FrontLiteralWindowTyping`, which exports them.

Not claimed: an accepted application (that additionally needs
`exact_OpenLiteralApplicationFromReportedLeast`), `ApplicationEdgeMatching`, downward closure,
`TypedCarrierComputability`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGeneralSeedLeastTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (carrier)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (leastSelectedAt)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- K2 for arbitrary scalar carriers with matching address reports. -/
def GeneralSeedLeast (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q u ctx dom cod fn arg : OTerm α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c u)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (addressReport q ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (addressReport u ctx dom arg)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (leastSelectedAt A.least ctx cod (auxiliaryTerm dom cod fn arg)))

/-- The general law from the installed code, under the hypotheses of
`SeedLeastOnJoinedWindow`. -/
def GeneralSeedLeastOnJoinedWindow : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (s : Settings) (X base : Program 2) (T V baseM : Program 1),
    let Tg := selectedBiAuxType s T A.typeGuard
    let C := measuredStrictCover V A.typeGuard baseM
    let Base := joinedBiAuxBase s X base Tg V A.typeGuard baseM
    A.scalar = finiteScalar
      (addressScalar A.contextGuard A.typeGuard
        (joinedAuxiliaryWindow s base Tg V A.typeGuard baseM) A.least)
      (finiteCodes W) →
    A.least = memoFilteredLeast C Base s →
    MemoSelectedReports C s Base →
    OpenRankTypeGuards W Tg A.typeGuard →
    ∀ c : Nat, GeneralSeedLeast A c

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneGeneralSeedLeastTargetsV2
