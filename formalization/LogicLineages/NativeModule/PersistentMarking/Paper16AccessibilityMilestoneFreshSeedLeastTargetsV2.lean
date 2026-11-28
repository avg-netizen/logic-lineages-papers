module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankForwardRowsProof

/-! Frozen targets for K2 `FreshSeedLeast` on the joined window with literal probe leaves
(`lem:arithmetic-accessibility`, type split at arrow types; Fable B2, 27 November 2026).

`SeedLeastOnJoinedWindow` is the law itself, for any installed window whose scalar is the finite
filter over the address scalar of the joined auxiliary window, whose least program is
`memoFilteredLeast` over the measured strict cover, and for which the least-report law
`MemoSelectedReports` and the open type guards `OpenRankTypeGuards` hold: then K2 holds at every
context numeral. Its premises are equations between installed programs and two open-term laws;
nothing about the application seed is assumed.

`LambdaWindowWithGuards` is `WindowWithLeastTargetsV2.LambdaWindowWithLeast` with one more
conjunct, `OpenRankTypeGuards`, which the packet proves and the earlier restatements drop.

`LiteralWindowWithSeedLeast` is `WindowWithLeastTargetsV2.LiteralWindowWithLeast` with that
conjunct, with K2 asserted on the selected window, and with the type split therefore reduced to
K1 alone. Not asserted: K1 `FreshAddressCarrier`, `TypedCarrierComputability`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2

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

/-- K2 from the installed code. For an installed window with the joined auxiliary window under
its finite address scalar and the memo-filtered least over the measured strict cover, the
least-report law and the open type guards give `FreshSeedLeast` at every context numeral. -/
def SeedLeastOnJoinedWindow : Prop :=
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
    ∀ c : Nat, FreshSeedLeast A c

/-- The joined lambda window with the code and the report law of its least program and the open
type guards of its two type programs. -/
def LambdaWindowWithGuards : Prop :=
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
      OpenRankTypeGuards (sourceWindow K) Tg A.typeGuard ∧
      ∀ c : Nat, BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
        (hop A.contextGuard A.typeGuard
          (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
        L₀ A.least U (sourceWindow K) A.probes c

/-- The joined lambda window with literal probe leaves, with the code and the report law of its
least program, the open type guards, the joined rules, K2, and both reductions (the first now
from K1 alone). -/
def LiteralWindowWithSeedLeast : Prop :=
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
      OpenRankTypeGuards (sourceWindow K) Tg A.typeGuard ∧
      ∀ c : Nat,
        BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
          (hop A.contextGuard A.typeGuard
            (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
          L₀ A.least U (sourceWindow K) A.probes c ∧
        FreshSeedLeast A c ∧
        (FreshAddressCarrier A c → CarrierTypingCases A c) ∧
        (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2
