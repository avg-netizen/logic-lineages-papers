module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneLiteralWindowTargetsV2.LiteralWindowSelection`
(Fable B, 27 November 2026).

`exact_BetaJoinedRulesOnLiteralWindow` moves the joined rules to `literalProbeWindow A`. Six
fields (`inversion`, `arithmetic`, `forward`, `pullback`, `applicationOutput`, `betaCases`) do not
mention the probe leaves and are reused as they are; `fresh` and `typedComputableToMember` mention
`chosenH`/`chosenA` and are rebuilt from the reinstalled tuple, the neutral arithmetic and the
forward rule, as in the coordinator's `exact_BetaJoinedRulesAfterRetype`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowProofV2

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
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof
  (exact_LiteralFreshFromNeutral exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open Paper16AccessibilityMilestoneInstalledLambdaWindowV2
  (exact_InstalledLambdaWindowWithScalarAtOriginalWindow)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (ApplicationResultCarrier)
open Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2 (literalProbeWindow)
open Paper16AccessibilityMilestoneArrowTypingAssemblyProofV2 (exact_WindowReductionFromJoinedFacts)
open Paper16AccessibilityMilestoneFreshApplicationProofV2 (exact_FreshApplicationFromLeast)
open Paper16AccessibilityMilestoneLiteralWindowTargetsV2

/-- The joined rules on the window with literal probe leaves. -/
theorem exact_BetaJoinedRulesOnLiteralWindow {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) (U : Program 2) (L₀ : Program 3) (c : Nat)
    (guard : A.probes.applicationGuard = applicationGuard A.scalar A.least)
    (old : BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (hop A.contextGuard A.typeGuard
        (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
      L₀ A.least U W A.probes c) :
    BetaJoinedRulesAt (literalProbeWindow A).presentation (literalProbeWindow A).scalar
      (applicationGuard (literalProbeWindow A).scalar (literalProbeWindow A).least)
      (hop (literalProbeWindow A).contextGuard (literalProbeWindow A).typeGuard
        (rawWithTarget (literalProbeWindow A).scalar (literalProbeWindow A).contextGuard
          (literalProbeWindow A).typeGuard (literalProbeWindow A).raw (literalProbeWindow A).least)
        (literalProbeWindow A).least)
      L₀ (literalProbeWindow A).least U W (literalProbeWindow A).probes c := by
  let B := literalProbeWindow A
  let step := hop B.contextGuard B.typeGuard
    (rawWithTarget B.scalar B.contextGuard B.typeGuard B.raw B.least) B.least
  have arithmetic := old.arithmetic
  have forward := old.forward
  rw [← guard] at arithmetic forward
  have tuple := B.installed.1
  have reports := tuple
  obtain ⟨_, _, _, _, _, _, _, _, _, parsed, aligned⟩ := reports
  refine ⟨old.inversion, old.arithmetic, old.forward, old.pullback,
    old.applicationOutput, old.betaCases, ?_, ?_⟩
  · exact exact_LiteralFreshFromNeutral B.probes W B.presentation step neutralSource bottomSource c
      parsed (aligned c) arithmetic
  · intro τ α Γ q typed computed
    exact exact_TupleComputabilityToIFromArithmetic S.entries (fixed S K) W
      B.scalar (jRaw B.scalar) B.path (dCore B.scalar B.path permutation)
      B.probes c step neutralSource bottomSource tuple arithmetic forward τ α Γ q typed computed

/-- The selection with all rules and both reductions on one window. -/
theorem exact_LiteralWindowSelection : LiteralWindowSelection := by
  intro S K closed
  obtain ⟨A, H, seed, V, leaves, other, base, T, baseM, L₀, vaFit, hFit, seedFit,
      shiftFit, depthFit, fit, raw, scalar, core, guard, rules⟩ :=
    exact_InstalledLambdaWindowWithScalarAtOriginalWindow S K closed
  refine ⟨literalProbeWindow A, H, seed, V, leaves, other, base, T, baseM, L₀, vaFit, hFit, seedFit,
    shiftFit, depthFit, fit, raw, scalar, core, guard, fun c => ?_⟩
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

#print axioms exact_BetaJoinedRulesOnLiteralWindow
#print axioms exact_LiteralWindowSelection

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralWindowProofV2
