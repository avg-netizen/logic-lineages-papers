module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneJoinedWindowSelection
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaInstanceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindow

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
open Paper16AccessibilityMilestoneInstalledPacket (installedOfPacket)
open Paper16AccessibilityMilestoneJoinedWindowSelection (exact_OriginalFiniteCodesIncluded)
open Paper16AccessibilityMilestoneTargets (InstalledWindow)

/-- The original window carries the calibrated singleton lambda instance in its
raw beta leaf. The joined rules use that instance and the same installed programs. -/
theorem exact_InstalledLambdaWindowAtOriginalWindow (S : Spine.Signature) (K : List Ty)
    (closed : DecisionSourceUniverse.Closed K) :
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
      A.application = applicationCore A.least ∧
      A.probes.applicationGuard = applicationGuard A.scalar A.least ∧
      ∀ c : Nat, BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
        (hop A.contextGuard A.typeGuard
          (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
        L₀ A.least U (sourceWindow K) A.probes c := by
  let s := fixed S K
  let W := sourceWindow K
  have valid := exact_OriginalValidWindow S K closed
  obtain ⟨H, seed, hFit, seedFit, build⟩ := exact_SingletonLambdaLiteralsInstanceConstructor
  let depth (Vs : Program 1) :=
    singletonLambda Vs (shiftHitLiterals Vs H) (singletonBound Vs (shiftHitLiterals Vs H) seed)
  let mk (Vs : Program 1) := zeroDepthInstance (depth Vs)
  obtain ⟨cv, tv, U, X, base, T, V, baseM, leaves, other, placed, vaFit, same, fit,
      packet, placedApp, rules⟩ :=
    exact_ConcreteLambdaJoinedRulesAt S.entries s W valid (exact_FixedWindowSeedsCovered S K)
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
  exact ⟨A, H, seed, V, leaves, other, base, T, baseM, L₀, vaFit, hFit, seedFit,
    exact_ShiftHitLiteralsFit Va H vaFit hFit, (build Va vaFit).1, fit,
    rfl, rfl, placedApp, rules⟩

#print axioms exact_InstalledLambdaWindowAtOriginalWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindow
