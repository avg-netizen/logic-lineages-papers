module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeFieldSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityRootTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The paid C mark law transports an actual tag after internally binding
its common mark. The older canonical full-fold root-field law is not used. -/
theorem tagTransport (data : Data) (window : Program 1)
    (out input typ parameter tag : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hs : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) input typ parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (ht : Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph tag input))) :
    Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph tag out)) := by
  apply programCases OriginalConstructorShape.mark (Fin.cons input Fin.elim0) _
  intro beta j Theta value hj hm
  rw [OriginalConstructorShapeSyntaxProof.tagGraphRename]
  simp only [consTermRename,emptyRename] at hm
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hs' := renameInto hs j Theta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename] at hs'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have ht' := renameInto ht j Theta hj
  rw [OriginalConstructorShapeSyntaxProof.tagGraphRename] at ht'
  obtain ⟨law⟩ := OriginalApplicationSidecarRootMarkProof.actualOriginalApplicationSidecarRootMark
    body data window beta Theta (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) value
  obtain ⟨premises⟩ := andIntro hw' (andIntro hs' hc')
  have both := Derivation.implicationElimination law premises
  have hmi : Nonempty (Derivation body Theta
      (OriginalConstructorShape.markGraph value (input.relabel j))) := hm
  obtain ⟨hmi'⟩ := hmi
  have hmo : Nonempty (Derivation body Theta
      (OriginalConstructorShape.markGraph value (out.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight both) hmi'⟩
  exact OriginalConstructorShapeRootFieldsProof.sharedTag value (input.relabel j)
    (out.relabel j) (tag.relabel j) ⟨hmi'⟩ hmo ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityRootTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityRootTagProof
