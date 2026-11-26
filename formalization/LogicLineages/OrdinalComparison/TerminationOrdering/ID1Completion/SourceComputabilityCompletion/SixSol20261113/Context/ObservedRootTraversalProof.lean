module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalCanonicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootTraversalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion ObservedRootWorkingDefinitions OriginalAllPositionStructuralTraversalDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalStructuralTraversalKeyTraversal :
    ∀ p H G W P, TraversalLaw p H G W P := by
  intro p H G W P body alpha Delta out input typ parameter mark
  let r := refined p H G W P
  let A := OriginalLambdaTraversalOutput.premises r.base r.window out input typ parameter
  obtain ⟨h⟩ := OriginalStructuralKeyPayloadInductionProof.observationsAtInput
    (body := body) (Gamma := A :: Delta) r.base r.window
    (OriginalStructuralClassKeyDefinitions.key p H G W)
    (ObservedRootClosureProof.applicationClosure p H G W P)
    (ObservedRootClosureProof.lambdaClosure p H G W P)
    (ObservedRootClosureProof.otherClosure p H G W P)
    out input typ parameter mark ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalStructuralTraversalKeyFinal :
    ∀ p H G W P, FinalLaw p H G W P := by
  intro p H G W P body alpha Delta out input typ parameter mark
  let r := refined p H G W P
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  let A := OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)
  have ha : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hcanonical⟩ := OriginalLambdaTraversalFinalCanonicalProof.actualOriginalLambdaTraversalFinalCanonical
    r body alpha (A :: Delta) out input typ parameter
  obtain ⟨hp⟩ := andIntro (andLeft ha) (andLeft (andRight ha))
  obtain ⟨hf⟩ := andRight (andRight ha)
  have hc := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination hcanonical hp)) hf
  have hw := andLeft ha
  have hs := andLeft (andRight ha)
  change Nonempty (Derivation body (A :: Delta)
    (OriginalFunctionNeutrality.windowGraph (OriginalLambdaTraversalSelection.finalInputs r).window input parameter)) at hw
  rw [OriginalLambdaTraversalSelectionFieldProof.finalWindow] at hw
  change Nonempty (Derivation body (A :: Delta)
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (OriginalLambdaTraversalSelection.finalData r) input typ parameter)) at hs
  rw [OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData,
    OriginalCanonicalFoldFusionFinalProof.selectedSourcePremises] at hs
  obtain ⟨hl⟩ := actualOriginalStructuralTraversalKeyTraversal p H G W P
    body alpha (A :: Delta) out input typ parameter mark
  obtain ⟨hargs⟩ := andIntro hw (andIntro hs ⟨hc⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hl hargs)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootTraversalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootTraversalProof
