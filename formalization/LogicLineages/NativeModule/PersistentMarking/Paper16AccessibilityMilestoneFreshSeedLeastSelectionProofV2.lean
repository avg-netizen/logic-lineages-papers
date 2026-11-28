module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLambdaRulesWithGuardsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2

/-! Proofs of the frozen `LambdaWindowWithGuards` and `LiteralWindowWithSeedLeast`
(`Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2`; Fable B2, 27 November 2026).

The text is that of Fable B's window-with-least proof module (untouched), run on
`exact_ConcreteLambdaJoinedRulesWithGuardsAt` so that the open type guards of the packet are
kept, followed by one new step: K2 on the selected window with literal probe leaves, by
`exact_SeedLeastOnJoinedWindow` from the exported scalar and least equations, the least-report
law and the type guards. The type split then follows from K1 alone. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastSelectionProofV2

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
open Paper16AccessibilityMilestoneLambdaRulesWithGuardsV2 (exact_ConcreteLambdaJoinedRulesWithGuardsAt)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (ApplicationResultCarrier)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)
open Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2 (exact_WindowReductionFromJoinedFacts)
open Paper16AccessibilityMilestoneFreshApplicationProofV2 (exact_FreshApplicationFromLeast)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (FreshSeedLeast)
open Paper16AccessibilityMilestoneLiteralWindowProofV2 (exact_BetaJoinedRulesOnLiteralWindow)
open Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2
open Paper16AccessibilityMilestoneFreshSeedLeastProofV2 (exact_SeedLeastOnJoinedWindow)

theorem exact_LambdaWindowWithGuards : LambdaWindowWithGuards := by
  intro S K closed
  let s := fixed S K
  let W := sourceWindow K
  have valid := exact_OriginalValidWindow S K closed
  obtain ⟨H, seed, hFit, seedFit, build⟩ := exact_SingletonLambdaLiteralsInstanceConstructor
  let depth (Vs : Program 1) :=
    singletonLambda Vs (shiftHitLiterals Vs H) (singletonBound Vs (shiftHitLiterals Vs H) seed)
  let mk (Vs : Program 1) := zeroDepthInstance (depth Vs)
  obtain ⟨cv, tv, U, X, base, T, V, baseM, leaves, other, placed, vaFit, same, fit,
      packet, placedApp, selected, guards, rules⟩ :=
    exact_ConcreteLambdaJoinedRulesWithGuardsAt S.entries s W valid (exact_FixedWindowSeedsCovered S K)
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
    rfl, rfl, rfl, placedApp, rfl, selected, guards, rules⟩

theorem exact_LiteralWindowWithSeedLeast : LiteralWindowWithSeedLeast := by
  intro S K closed
  obtain ⟨A, H, seed, V, leaves, other, base, T, baseM, L₀, X, vaFit, hFit, seedFit,
      shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards, rules⟩ :=
    exact_LambdaWindowWithGuards S K closed
  refine ⟨literalProbeWindow A, H, seed, V, leaves, other, base, T, baseM, L₀, X, vaFit, hFit,
    seedFit, shiftFit, depthFit, fit, raw, scalar, core, guard, leastCode, selected, guards,
    fun c => ?_⟩
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
  have k2 : FreshSeedLeast (literalProbeWindow A) c :=
    exact_SeedLeastOnJoinedWindow S K (sourceWindow K) (literalProbeWindow A) (fixed S K)
      X base T V baseM scalar leastCode selected guards c
  exact ⟨exact_BetaJoinedRulesOnLiteralWindow A _ L₀ c guard (rules c), k2,
    fun k1 => typingFrom
      (exact_FreshApplicationFromLeast S K (sourceWindow K) (literalProbeWindow A) guard c k1 k2),
    allTerms⟩

#print axioms exact_LambdaWindowWithGuards
#print axioms exact_LiteralWindowWithSeedLeast

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastSelectionProofV2
