module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets

/-! Frozen targets: the window selections of
`Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2`, installed at front-tested leaves
(K1 `FreshAddressCarrier`, step 3 of
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md`; Fable B2,
27 November 2026).

In both statements the three opaque leaves of the packet are replaced by visible front tests
over them: the syntax leaf `V := variableFrontSyntax A.typeGuard V₀`, the measure leaf
`baseM := namedMeasureBase baseM₀` (the legacy named-leaf measure front, so the installed
measure stays `chosenMeasure baseM`), and the window leaf
`base := variableFrontWindow Tg base₀`. `V₀`, `baseM₀`, `base₀` are the existential
Primrec-realization witnesses; everything stated about `V`, `baseM`, `base` is otherwise word
for word `LambdaWindowWithGuards` / `LiteralWindowWithSeedLeast`. In particular K2
`FreshSeedLeast` is asserted again on the new window.

Not claimed: K1 `FreshAddressCarrier`, `TypedCarrierComputability`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontWindowTargetsV2

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

/-- The joined lambda window installed at the front-tested syntax, measure and window leaves,
with the code and the report law of its least program and the open type guards. -/
def FrontLambdaWindow : Prop :=
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
      ∀ c : Nat, BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
        (hop A.contextGuard A.typeGuard
          (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
        L₀ A.least U (sourceWindow K) A.probes c

/-- The same window with literal probe leaves: the code and the report law of its least program,
the open type guards, the joined rules, K2, and both reductions (the first from K1 alone). -/
def FrontLiteralWindowWithSeedLeast : Prop :=
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
        FreshSeedLeast A c ∧
        (FreshAddressCarrier A c → CarrierTypingCases A c) ∧
        (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFrontWindowTargetsV2
