module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindowV2

/-! Frozen target: one installed window with literal probe leaves that carries, together, the
joined beta/lambda rules, the reduction of the type split to K1 and K2, and the reduction of the
all-terms sentence to the type split and `TypedCarrierComputability`
(`lem:arithmetic-accessibility`; Fable B, 27 November 2026).

The statement is that of `exact_InstalledLambdaWindowWithScalarAtOriginalWindow`
(`Paper16AccessibilityMilestoneInstalledLambdaWindowV2`) with the same raw-leaf, scalar, core and
guard equations and the same `BetaJoinedRulesAt`, now on a window whose probe leaves are the
literal ones, and with two further conjuncts per context numeral. It is the window on which
`TypedCarrierComputability` has to be proved: a proof of
`FreshAddressCarrier`, `FreshSeedLeast` and `TypedCarrierComputability` for the window of this
statement gives `AllTerms` on it. None of the three is asserted. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowTargetsV2

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
open Paper16AccessibilityMilestoneTargetsV2
  (CarrierTypingCases TypedCarrierComputability AllTerms)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (FreshAddressCarrier FreshSeedLeast)

/-- The joined lambda window with literal probe leaves: all equations and joined rules of the
original selection, and both reductions, on one installation. -/
def LiteralWindowSelection : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (A : InstalledWindow S K (sourceWindow K)) (H : Program 2) (seed : Program 3)
      (V : Program 1) (leaves : Nat → Program 3) (other : Program 3)
      (base : Program 2) (T baseM : Program 1) (L₀ : Program 3),
      let s := fixed S K
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
      ∀ c : Nat,
        BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
          (hop A.contextGuard A.typeGuard
            (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
          L₀ A.least U (sourceWindow K) A.probes c ∧
        (FreshAddressCarrier A c → FreshSeedLeast A c → CarrierTypingCases A c) ∧
        (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowTargetsV2
