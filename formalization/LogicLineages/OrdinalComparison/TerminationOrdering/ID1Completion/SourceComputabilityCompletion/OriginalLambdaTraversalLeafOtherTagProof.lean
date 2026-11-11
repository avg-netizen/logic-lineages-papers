module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOtherTagTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafOtherTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The real selected leaf cannot turn an active OTHER-tag input into an
application or lambda. This uses its independently checked root-mark guard,
not native representative calibration or a traversal-output hypothesis. -/
theorem leafOtherTag (rawData : Data) (window : Program 1)
    (out input parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (leaf rawData window) out input parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input))) :
    Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) out)) := by
  apply programCases OriginalLambdaTraversal.rawTag (Fin.cons input Fin.elim0) _
  intro beta j Theta tag hj htag
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hw' := renameInto hw j Theta hj
  have hv' := renameInto hv j Theta hj
  have hl' := renameInto hl j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  rw [graph2Rename] at hl'
  simp only [graph1Rename,sucRelabel,zRelabel] at ht'
  simp only [consTermRename,emptyRename] at htag
  have htagOut := OriginalLambdaTraversalLeafObserverProof.rawTag rawData window
    (out.relabel j) (input.relabel j) (parameter.relabel j) tag hw' hv' hl' htag
  exact OriginalLambdaTraversalOtherTagTransportProof.atSameTag
    (input.relabel j) (out.relabel j) tag (suc z) htag htagOut ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafOtherTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLeafOtherTagProof
