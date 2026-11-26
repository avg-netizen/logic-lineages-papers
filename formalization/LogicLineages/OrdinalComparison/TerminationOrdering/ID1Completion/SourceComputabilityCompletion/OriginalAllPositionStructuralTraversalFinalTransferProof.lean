module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalCanonicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalFinalTransferProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalAllPositionStructuralTraversalDefinitions
open OriginalAllPositionStructuralTraversalTargets

/-- Conditional transfer only: the actual traversal supplier is still an explicit
metatheoretic argument here. Neither whole-fold target is declared proved. -/
theorem finalOfTraversal (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (traversal : TraversalLaw p H G W P) :
    FinalLaw p H G W P := by
  dsimp only [FinalLaw]
  intro body alpha Delta out input typ parameter mark cutoff
  let r := refined p H G W P
  let premise := (OriginalFunctionNeutrality.windowGraph
      (OriginalLambdaTraversalSelection.finalInputs r).window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalLambdaTraversalSelection.finalData r) input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph
        (OriginalLambdaTraversalSelection.finalData r) out input parameter)) ⊓
    OriginalIndexedObserverDefinitions.ActualRange cutoff parameter
  have hh : Nonempty (Derivation body (premise :: Delta) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha := andLeft hh
  obtain ⟨law⟩ := OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical
    r body alpha (premise :: Delta) out input typ parameter
  obtain ⟨hp⟩ := andIntro (andLeft ha) (andLeft (andRight ha))
  obtain ⟨hf⟩ := andRight (andRight ha)
  have hc := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination law hp)) hf
  have hw := andLeft ha
  have hs := andLeft (andRight ha)
  change Nonempty (Derivation body (premise :: Delta)
    (OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs r).window input parameter)) at hw
  rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow] at hw
  change Nonempty (Derivation body (premise :: Delta)
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalLambdaTraversalSelection.finalData r) input typ parameter)) at hs
  rw [OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData,
    OriginalCanonicalFoldFusionFinalProof.selectedSourcePremises] at hs
  have htr := andIntro (andIntro hw (andIntro hs ⟨hc⟩)) (andRight hh)
  obtain ⟨ht⟩ := traversal body alpha (premise :: Delta) out input typ parameter mark cutoff
  obtain ⟨htr⟩ := htr
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination ht htr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalFinalTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalFinalTransferProof
