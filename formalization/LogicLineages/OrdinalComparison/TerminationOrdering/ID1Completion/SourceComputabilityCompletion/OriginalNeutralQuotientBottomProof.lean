module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientBottomProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalParameterizedCanonicalResultFold (foldGraph)
open InternalParameterizedCanonicalResultFoldConsumerProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The actual fold preserves the raw source type. Bind that type internally,
then compare its certified output projection with the requested output type.
No source-type witness or fixedness premise is supplied by the caller. -/
theorem sourceType (data : Data) (out input typeCode parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma (graph2 (validity data) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Gamma (foldGraph data out input parameter)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode out))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode input)) := by
  apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
  intro beta j Delta rawType hj hraw
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at hraw
  have hv' := renameInto hv j Delta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hn' := renameInto hn j Delta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename] at hn'
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  have hc := certifiedAt data (out.relabel j) (input.relabel j) rawType
    (parameter.relabel j) hv' hraw hn'
  have he := valueUnique InternalUnpair.left rawType (typeCode.relabel j)
    (Fin.cons (out.relabel j) Fin.elim0) (andLeft (andRight (andRight hc))) ht'
  exact outputTransport InternalUnpair.left rawType (typeCode.relabel j)
    (Fin.cons (input.relabel j) Fin.elim0) he hraw

/-- A literal same-type raw bottom remains that literal bottom after the
actual outer canonical fold. Its type and bottom recognition are derived
through the existing full-fold laws at this SAME selected tuple. -/
theorem bottomThroughFold (base : Data) (window : Program 1)
    (out input typeCode parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity (OuterSelection.data base window)) (suc z) input parameter)))
    (hn : Nonempty (Derivation body Gamma
      (foldGraph (OuterSelection.data base window) out input parameter)))
    (hb : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode input typeCode))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode out typeCode)) := by
  let data := OuterSelection.data base window
  have hfull : OriginalVariableQuotientPath.FullFoldBottomPreservation data window := by
    change OriginalVariableQuotientPath.FullFoldBottomPreservation
      (OuterSelection.data base window) window
    rw [OriginalVariableQuotientPathBottomProof.outerData]
    exact OriginalVariableQuotientPathBottomProof.fullFoldBottomPreservation
      (SpineApplicationTargets.parameters base window) window
  have hl := BottomSourceShapeProof.bottomCodeLeft input typeCode hb
  have hraw := BottomSourceShapeProof.bottomAccept input typeCode hb
  obtain ⟨hlaw⟩ := hfull body alpha Gamma out input typeCode parameter
  obtain ⟨hp⟩ := andIntro hw (andIntro (andIntro hv hl) hn)
  have hi := Derivation.implicationElimination hlaw hp
  obtain ⟨hraw⟩ := hraw
  have hout : Nonempty (Derivation body Gamma (OriginalVariableQuotientPath.bottomAccepted out)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hraw⟩
  have hc := certifiedAt data out input typeCode parameter hv hl hn
  exact BottomSourceShapeProof.bottomRecover out typeCode
    (andLeft (andRight (andRight hc))) hout

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientBottomProof
