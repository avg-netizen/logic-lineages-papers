module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFrontWindowTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureTargetsV2

/-! Frozen targets: K1 `FreshAddressCarrier` on the window at the front-tested leaves, and the
composed selection (`lem:arithmetic-accessibility`, type split at arrow types; step 4 of
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md`; Fable B2,
27 November 2026).

`FreshCarrierOnFrontWindow` is the law: for any installed window whose scalar is the finite
filter over the address scalar of the joined auxiliary window at the three front-tested leaves,
whose least is `memoFilteredLeast` over the measured strict cover at those leaves, with the
least-report law, the open type guards and a domain-closed window, K1 holds at every context
numeral. Assumed: two equations between installed programs, two open-term laws and the numeric
domain closure of the window. Not assumed: anything about the fresh address (no window, no
coverage, no syntax bit, no least report at its payload) and no calibration of `V₀`, `baseM₀`,
`base₀`, `T`.

`FrontLiteralWindowTyping` is the composed statement: one window per closed universe, with
everything `FrontLiteralWindowWithSeedLeast` exports, on which K1, K2 and `CarrierTypingCases`
hold and `TypedCarrierComputability A c → AllTerms A c`.

Not claimed: `TypedCarrierComputability`, `AllTerms`, `lem:arithmetic-accessibility`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierTargetsV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks (exact_OriginalValidWindow)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof (BetaJoinedRulesAt)
open NumberedWindowInternalLiteralConcreteLambdaJoinedRulesProof (exact_ConcreteLambdaJoinedRulesAt)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit singletonBound)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (DepthInstanceFit zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaInstanceProof
  (exact_SingletonLambdaLiteralsInstanceConstructor)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof
  (shiftHitLiterals exact_ShiftHitLiteralsFit)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard applicationCore)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowOriginalFixedSeedCoverageProof (exact_FixedWindowSeedsCovered)
open NumberedWindowOriginalFixedSettingsProof (exact_FixedGrammarTypeInclusion exact_FixedHeadPairsSymmetric)
open Paper16AccessibilityMilestoneInstalledPacketV2 (installedOfPacket)
open Paper16AccessibilityMilestoneJoinedWindowSelectionV2 (exact_OriginalFiniteCodesIncluded)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (MemoSelectedReports)
open Paper16AccessibilityMilestoneTargetsV2
  (CarrierTypingCases TypedCarrierComputability AllTerms)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (FreshAddressCarrier FreshSeedLeast)

open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowScalarAlgorithm (Settings)

open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase)
open Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2 (variableFrontSyntax)
open Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2 (variableFrontWindow)

open Paper16AccessibilityMilestoneDomainClosureTargetsV2 (DomainClosed)

/-- K1 from the installed code at the front-tested leaves. -/
def FreshCarrierOnFrontWindow : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (s : Settings) (X base₀ : Program 2) (T V₀ baseM₀ : Program 1),
    let Tg := selectedBiAuxType s T A.typeGuard
    let V := variableFrontSyntax A.typeGuard V₀
    let baseM := namedMeasureBase baseM₀
    let base := variableFrontWindow Tg base₀
    let C := measuredStrictCover V A.typeGuard baseM
    let Base := joinedBiAuxBase s X base Tg V A.typeGuard baseM
    A.scalar = finiteScalar
      (addressScalar A.contextGuard A.typeGuard
        (joinedAuxiliaryWindow s base Tg V A.typeGuard baseM) A.least)
      (finiteCodes W) →
    A.least = memoFilteredLeast C Base s →
    MemoSelectedReports C s Base →
    OpenRankTypeGuards W Tg A.typeGuard →
    DomainClosed W →
    ∀ c : Nat, FreshAddressCarrier A c

/-- The window at the front-tested leaves with literal probe leaves, with everything
`FrontLiteralWindowWithSeedLeast` exports, and with K1, K2 and the type split asserted on it:
`lem:arithmetic-accessibility` on this window rests on `TypedCarrierComputability` alone. -/
def FrontLiteralWindowTyping : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (A : InstalledWindow S K (sourceWindow K)) (H : Program 2) (seed : Program 3)
      (V₀ : Program 1) (leaves : Nat → Program 3) (other : Program 3)
      (base₀ : Program 2) (T baseM₀ : Program 1) (L₀ : Program 3) (X : Program 2),
      let s := fixed S K
      let V := variableFrontSyntax A.typeGuard V₀
      let baseM := namedMeasureBase baseM₀
      let base := variableFrontWindow (selectedBiAuxType s T A.typeGuard) base₀
      let Va := unitAuxSyntax V A.typeGuard
      let shift := shiftHitLiterals Va H
      let depth := singletonLambda Va shift (singletonBound Va shift seed)
      let U := zeroDepthInstance depth
      let Tg := selectedBiAuxType s T A.typeGuard
      let C := measuredStrictCover V A.typeGuard baseM
      let leaf := withBetaLeaf Va U leaves
      ActualRawSyntax Va ∧ ShiftHitFit H ∧ DepthInstanceFit seed ∧ ShiftHitFit shift ∧
      DepthInstanceFit depth ∧ InstanceFit U ∧
      A.raw = guardedRaw (strictDualRaw C s leaf (lambdaFallback other) base base Tg Va Tg) ∧
      A.scalar = finiteScalar
        (addressScalar A.contextGuard A.typeGuard
          (joinedAuxiliaryWindow s base Tg V A.typeGuard baseM) A.least)
        (finiteCodes (sourceWindow K)) ∧
      A.application = applicationCore A.least ∧
      A.probes.applicationGuard = applicationGuard A.scalar A.least ∧
      A.least = memoFilteredLeast C (joinedBiAuxBase s X base Tg V A.typeGuard baseM) s ∧
      MemoSelectedReports C s (joinedBiAuxBase s X base Tg V A.typeGuard baseM) ∧
      OpenRankTypeGuards (sourceWindow K) Tg A.typeGuard ∧
      ∀ c : Nat,
        BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
          (hop A.contextGuard A.typeGuard
            (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
          L₀ A.least U (sourceWindow K) A.probes c ∧
        FreshAddressCarrier A c ∧
        FreshSeedLeast A c ∧
        CarrierTypingCases A c ∧
        (TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierTargetsV2
