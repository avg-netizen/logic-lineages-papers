module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalAllPositionStructuralTraversalDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem window (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : (refined p H G W P).window = p.window := rfl

theorem sourceIdentity (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (OriginalRankGuardedRepresentative.transparentInputs H G W
      (minimumInputs p H G W P)).base.oldSource =
      OriginalPositionStructuralKeyOpeningDefinitions.source p H G W := by
  rw [OriginalStructuralTraversalKeyFieldSupportProof.transparentSource]
  rfl

/-- Collapse the actual selected leaf validity, not a calibrated interpretation. -/
theorem sourceOfValidity (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (input parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalLambdaTraversalSelection.leafData (refined p H G W P).base
          (refined p H G W P).window)) (numeral 1) input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalPositionStructuralKeyOpeningDefinitions.source p H G W)
        (numeral 1) input parameter)) := by
  have hv' : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalRankGuardedLeafProof.selectedData (minimumInputs p H G W P) H G W))
        (numeral 1) input parameter)) := hv
  rw [OriginalRankGuardedLeafProof.selectedValidity] at hv'
  have hs := iffForward (OriginalRankGuardedLeafTupleProof.priorSourceIff
    (minimumInputs p H G W P) H G W (numeral 1) input parameter) hv'
  rw [sourceIdentity] at hs
  exact hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
