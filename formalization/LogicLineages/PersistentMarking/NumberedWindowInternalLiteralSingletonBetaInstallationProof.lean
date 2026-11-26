module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafNumericProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowRootDispatchAlgorithm (fixed)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralBetaLeafNumericProof (exact_LiteralBetaLeafFit)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (DepthInstanceFit zeroDepthInstance exact_ZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (ShiftHitFit singletonBound)
open NumberedWindowInternalLiteralSingletonBoundCalibrationProof (exact_LiteralSingletonBoundCalibration)

/-- The beta leaf can use the physical atomic and bound dispatch, installed
at depth zero, with the original numerical leaf contract. -/
theorem exact_PhysicalSingletonBetaInstallation (xs : Entries) (heads : List Nat)
    (V : Program 1) (H : Program 2) (U : Program 3) (leaf : Nat → Program 3)
    (vFit : ActualRawSyntax V) (hFit : ShiftHitFit H) (uFit : DepthInstanceFit U)
    (fit : LeafFit (fixed xs heads) leaf) :
    let betaInstance := zeroDepthInstance (singletonBound V H U)
    InstanceFit betaInstance ∧ LeafFit (fixed xs heads) (withBetaLeaf V betaInstance leaf) := by
  have instanceFit := exact_ZeroDepthInstance (singletonBound V H U)
    (exact_LiteralSingletonBoundCalibration V H U vFit hFit uFit)
  exact ⟨instanceFit, exact_LiteralBetaLeafFit xs heads V _ vFit instanceFit leaf fit⟩

#print axioms exact_PhysicalSingletonBetaInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
