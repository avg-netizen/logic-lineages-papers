module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLambdaRulesWithLeastV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2

/-! Proofs of the frozen `LambdaWindowWithLeast` and `LiteralWindowWithLeast`
(Fable B, 27 November 2026). The first is the coordinator's proof of
`exact_InstalledLambdaWindowWithScalarAtOriginalWindow` run on
`exact_ConcreteLambdaJoinedRulesWithLeastAt`, keeping the exchange program and the least-report
law. The second installs the literal probe leaves as in `exact_LiteralWindowSelection`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastProofV2

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
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open Paper16AccessibilityMilestoneLambdaRulesWithLeastV2 (exact_ConcreteLambdaJoinedRulesWithLeastAt)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (ApplicationResultCarrier)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)
open Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2 (exact_WindowReductionFromJoinedFacts)
open Paper16AccessibilityMilestoneFreshApplicationProofV2 (exact_FreshApplicationFromLeast)
open Paper16AccessibilityMilestoneLiteralWindowProofV2 (exact_BetaJoinedRulesOnLiteralWindow)
open Paper16AccessibilityMilestoneWindowWithLeastTargetsV2

theorem exact_LambdaWindowWithLeast : LambdaWindowWithLeast := by
  intro S K closed
  let s := fixed S K
  let W := sourceWindow K
  have valid := exact_OriginalValidWindow S K closed
  obtain ⟨H, seed, hFit, seedFit, build⟩ := exact_SingletonLambdaLiteralsInstanceConstructor
  let depth (Vs : Program 1) :=
    singletonLambda Vs (shiftHitLiterals Vs H) (singletonBound Vs (shiftHitLiterals Vs H) seed)
  let mk (Vs : Program 1) := zeroDepthInstance (depth Vs)
  obtain ⟨cv, tv, U, X, base, T, V, baseM, leaves, other, placed, vaFit, same, fit,
      packet, placedApp, selected, rules⟩ :=
    exact_ConcreteLambdaJoinedRulesWithLeastAt S.entries s W valid (exact_FixedWindowSeedsCovered S K)
      (exact_FixedHeadPairsSymmetric S K) (exact_FixedGrammarTypeInclusion S K)
      (exact_OriginalFiniteCodesIncluded S K closed) mk (fun Vs vFit => (build Vs vFit).2)
  change U = mk (unitAuxSyntax V tv) at same
  subst U
  let Tg := selectedBiAuxType s T tv
  let C := measuredStrictCover V tv baseM
  let window := joinedAuxiliaryWindow s base Tg V tv baseM
  let memo := joinedBiAuxBase s X base Tg V tv baseM
  let L₀ := packedLeastOn C (recursiveTypedMemo memo) s
  let L := memoFilteredLeast C memo s
  let scalar := finiteScalar (addressScalar cv tv window L) (finiteCodes W)
  let Va := unitAuxSyntax V tv
  let leaf := withBetaLeaf Va (mk Va) leaves
  let raw := guardedRaw (strictDualRaw C s leaf (lambdaFallback other) base base Tg Va Tg)
  let A := installedOfPacket valid scalar cv tv raw L (applicationCore L) placed packet
  exact ⟨A, H, seed, V, leaves, other, base, T, baseM, L₀, X, vaFit, hFit, seedFit,
    exact_ShiftHitLiteralsFit Va H vaFit hFit, (build Va vaFit).1, fit,
    rfl, rfl, rfl, placedApp, rfl, selected, rules⟩

theorem exact_LiteralWindowWithLeast : LiteralWindowWithLeast := by
  intro S K closed
  obtain ⟨A, H, seed, V, leaves, other, base, T, baseM, L₀, X, vaFit, hFit, seedFit,
      shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, rules⟩ :=
    exact_LambdaWindowWithLeast S K closed
  refine ⟨literalProbeWindow A, H, seed, V, leaves, other, base, T, baseM, L₀, X, vaFit, hFit,
    seedFit, shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, fun c => ?_⟩
  have output : ApplicationResultCarrier A c := by
    intro α Γ x u t app
    rw [guard] at app
    exact ((rules c).applicationOutput α Γ x u t app).1
  have arithmetic := (rules c).arithmetic
  have forward := (rules c).forward
  rw [← guard] at arithmetic forward
  obtain ⟨typingFrom, allTerms⟩ := exact_WindowReductionFromJoinedFacts S K A _
    (hop A.contextGuard A.typeGuard
      (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
    neutralSource bottomSource scalar core c output arithmetic forward
  exact ⟨exact_BetaJoinedRulesOnLiteralWindow A _ L₀ c guard (rules c),
    fun k1 k2 => typingFrom
      (exact_FreshApplicationFromLeast S K (sourceWindow K) (literalProbeWindow A) guard c k1 k2),
    allTerms⟩

#print axioms exact_LambdaWindowWithLeast
#print axioms exact_LiteralWindowWithLeast

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneWindowWithLeastProofV2
