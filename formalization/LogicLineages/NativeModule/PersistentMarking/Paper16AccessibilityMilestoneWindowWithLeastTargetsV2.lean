module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof

/-! Frozen targets: the lambda-window selection and the literal-window selection, restated so
that they also export the code of the installed least program and its least-report law
(Fable B, 27 November 2026; continuation item B).

`LambdaWindowWithLeast` is the statement of
`exact_InstalledLambdaWindowWithScalarAtOriginalWindow` with one more witness (the exchange
program `X` of the memo base) and two more conjuncts: `A.least = memoFilteredLeast C Base s` and
`MemoSelectedReports C s Base`. `LiteralWindowWithLeast` is `LiteralWindowSelection` with the same
additions. No new arithmetic is claimed; these are restatements of existing proofs. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastTargetsV2

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

/-- The joined lambda window with the code and the report law of its least program. -/
def LambdaWindowWithLeast : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (A : InstalledWindow S K (sourceWindow K)) (H : Program 2) (seed : Program 3)
      (V : Program 1) (leaves : Nat → Program 3) (other : Program 3)
      (base : Program 2) (T baseM : Program 1) (L₀ : Program 3) (X : Program 2),
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
      A.least = memoFilteredLeast C (joinedBiAuxBase s X base Tg V A.typeGuard baseM) s ∧
      MemoSelectedReports C s (joinedBiAuxBase s X base Tg V A.typeGuard baseM) ∧
      ∀ c : Nat, BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
        (hop A.contextGuard A.typeGuard
          (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
        L₀ A.least U (sourceWindow K) A.probes c

/-- The joined lambda window with literal probe leaves, with the code and the report law of its
least program, the joined rules, and both reductions. -/
def LiteralWindowWithLeast : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (A : InstalledWindow S K (sourceWindow K)) (H : Program 2) (seed : Program 3)
      (V : Program 1) (leaves : Nat → Program 3) (other : Program 3)
      (base : Program 2) (T baseM : Program 1) (L₀ : Program 3) (X : Program 2),
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
      A.least = memoFilteredLeast C (joinedBiAuxBase s X base Tg V A.typeGuard baseM) s ∧
      MemoSelectedReports C s (joinedBiAuxBase s X base Tg V A.typeGuard baseM) ∧
      ∀ c : Nat,
        BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
          (hop A.contextGuard A.typeGuard
            (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
          L₀ A.least U (sourceWindow K) A.probes c ∧
        (FreshAddressCarrier A c → FreshSeedLeast A c → CarrierTypingCases A c) ∧
        (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastTargetsV2
