module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneGroundWindowTypingV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneInstalledLambdaWindowV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneRetypedJoinedWindowV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof (BetaJoinedRulesAt)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof
  (exact_LiteralFreshFromNeutral exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonShiftHitAtomsMachineProof (shiftHitLiterals)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open Paper16AccessibilityMilestoneGroundWindowTypingV2 (exact_RetypedCarrierTypingCasesGround)
open Paper16AccessibilityMilestoneInstalledLambdaWindowV2 (exact_InstalledLambdaWindowWithScalarAtOriginalWindow)
open Paper16AccessibilityMilestoneLiteralPriorTypedV2 (priorTypedOf retypeWindow)
open Paper16AccessibilityMilestoneTargetsV2 (CarrierTypingCases InstalledWindow)

/-- Rebuild the two typing-dependent joined rules after reinstalling the prior checker. -/
theorem exact_BetaJoinedRulesAfterRetype {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) (U : Program 2) (L₀ : Program 3) (c : Nat)
    (guard : A.probes.applicationGuard = applicationGuard A.scalar A.least)
    (old : BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
      (hop A.contextGuard A.typeGuard
        (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
      L₀ A.least U W A.probes c) :
    let B := retypeWindow A
    BetaJoinedRulesAt B.presentation B.scalar (applicationGuard B.scalar B.least)
      (hop B.contextGuard B.typeGuard
        (rawWithTarget B.scalar B.contextGuard B.typeGuard B.raw B.least) B.least)
      L₀ B.least U W B.probes c := by
  let B := retypeWindow A
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

/-- At the original singleton ground universe, the retyped lambda packet
carries both the ground split and the joined rules on one installation. -/
theorem exact_OriginalGroundLambdaTypingWindow (S : Spine.Signature) :
    ∃ (A : InstalledWindow S [Ty.ground] (sourceWindow [Ty.ground])) (base : Program 1)
      (U : Program 2) (L₀ : Program 3),
      A.scalar = finiteScalar base [0] ∧
      A.probes.priorTyped = priorTypedOf A.scalar ∧ InstanceFit U ∧
      A.probes.applicationGuard = applicationGuard A.scalar A.least ∧
      ∀ c : Nat, CarrierTypingCases A c ∧
        BetaJoinedRulesAt A.presentation A.scalar (applicationGuard A.scalar A.least)
          (hop A.contextGuard A.typeGuard
            (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least)
          L₀ A.least U (sourceWindow [Ty.ground]) A.probes c := by
  have closed : DecisionSourceUniverse.Closed [Ty.ground] := by
    intro τ hτ σ hσ
    have same : τ = Ty.ground := by simpa using hτ
    subst τ
    simpa [TypeSupport.subtypes] using hσ
  obtain ⟨A, H, seed, V, _, _, base, T, baseM, L₀, _, _, _, _, _, fit, _, scalar, _, guard, rules⟩ :=
    exact_InstalledLambdaWindowWithScalarAtOriginalWindow S [Ty.ground] closed
  let s := fixed S [Ty.ground]
  let Va := unitAuxSyntax V A.typeGuard
  let shift := shiftHitLiterals Va H
  let U := zeroDepthInstance (singletonLambda Va shift (singletonBound Va shift seed))
  let Tg := selectedBiAuxType s T A.typeGuard
  let baseScalar := addressScalar A.contextGuard A.typeGuard
    (joinedAuxiliaryWindow s base Tg V A.typeGuard baseM) A.least
  have shape : A.scalar = finiteScalar baseScalar [0] := scalar
  refine ⟨retypeWindow A, baseScalar, U, L₀, shape, rfl, fit, guard, fun c => ?_⟩
  exact ⟨exact_RetypedCarrierTypingCasesGround A c baseScalar shape,
    exact_BetaJoinedRulesAfterRetype A U L₀ c guard (rules c)⟩

#print axioms exact_BetaJoinedRulesAfterRetype
#print axioms exact_OriginalGroundLambdaTypingWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneRetypedJoinedWindowV2
