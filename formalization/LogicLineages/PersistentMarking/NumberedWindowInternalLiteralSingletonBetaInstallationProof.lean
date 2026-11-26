module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
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
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenEvaluationProof (exact_OpenSingletonBoundAtZero)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)

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

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The beta instance wrapper supplies the literal zero depth and retains
the output of the original singleton graph on the resulting open tape. -/
theorem exact_OpenZeroDepthInstance (p : Program 3) (a q out : OTerm α)
    (run : D B Γ (programGraph p out ![a,z,q])) :
    D B Γ (programGraph (zeroDepthInstance p) out ![a,q]) := by
  let xs : Fin 2 → OTerm α := ![a,q]
  apply compositionValue p ![.projection 0,constantZero 2,.projection 1] out xs ![a,z,q] run
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact projectionValue 0 xs
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact constantZeroValue xs
    · obtain rfl := Fin.eq_zero k
      exact projectionValue 1 xs

/-- The actual beta instance program inserts the replacement at the
discharged bound slot of a literal open node. -/
theorem exact_OpenPhysicalBetaBoundZero (V : Program 1) (H : Program 2) (U : Program 3)
    (a t : OTerm α) (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t z))) :
    D B Γ (programGraph (zeroDepthInstance (singletonBound V H U)) (suc a) ![a,boundTerm t z]) :=
  exact_OpenZeroDepthInstance _ a (boundTerm t z) (suc a)
    (exact_OpenSingletonBoundAtZero V H U a t inserted typedNode)

#print axioms exact_PhysicalSingletonBetaInstallation
#print axioms exact_OpenZeroDepthInstance
#print axioms exact_OpenPhysicalBetaBoundZero
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBetaInstallationProof
