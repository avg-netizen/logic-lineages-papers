module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalModeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalStateSyntaxProof OriginalTypedDecoderInternalModeProof
open OriginalTypedDecoderInternalRequestSelectorsProof OriginalTypedDecoderInternalListProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- All eight witnesses are read from the SAME actual first work request.
Nonzero work supplies the original cons, not a postulated decomposition. -/
 theorem nonemptyForward (H : Program 1) (state out w : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 work w state)))
    (hn : Nonempty (Derivation body Delta (equal w (SourceComputabilityFormulaSupportProof.numeral 0)).not))
    (ho : Nonempty (Derivation body Delta (graph1 (modeProgram H) out state))) :
    Nonempty (Derivation body Delta (StepNonemptyWork H out w)) := by
  let qs : Fin 8 → Program 1 := ![currentRequest,rest,mode,gamma,typ,raw,tag,payload]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [nonemptyRename]
  have hw' := renameInto hw j Theta hj
  have hn' := renameInto hn j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hw' ho'
  simp only [consTermRename,emptyRename] at hq
  have hnonzero : Nonempty (Derivation body Theta
      (equal (w.relabel j) (SourceComputabilityFormulaSupportProof.numeral 0)).not) := by
    change Nonempty (Derivation body Theta
      (((equal w (SourceComputabilityFormulaSupportProof.numeral 0)).relabel j).not)) at hn'
    simpa only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,
      SourceComputabilityFormulaSupportProof.numeral,InternalTagArithmeticSyntaxProof.zRelabel] using hn'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hwork := consFields (w.relabel j) (ys 0) (ys 1) hnonzero
    (arrowFields work (w.relabel j) (ys 0) (ys 1) xx hw' (hq 0) (hq 1))
  have hrequest := requestFields currentRequest (ys 0) (ys 2) (ys 3) (ys 4) (ys 5) xx
    (hq 0) (hq 2) (hq 3) (hq 4) (hq 5)
  have hraw := pairFields raw (ys 5) (ys 6) (ys 7) xx (hq 5) (hq 6) (hq 7)
  have hmode := modeForward H (state.relabel j) (out.relabel j)
    (ys 2) (ys 3) (ys 4) (ys 6) (ys 7) (ys 1)
    (hq 2) (hq 3) (hq 4) (hq 6) (hq 7) (hq 1) ho'
  exact nonemptyIntro H _ _ ys (andIntro hwork (andIntro hrequest (andIntro hraw hmode)))

/-- The independent pair/list formula reconstructs the actual selector graphs
before the mode branch is introduced, including arbitrary malformed requests. -/
 theorem nonemptyBackward (H : Program 1) (state out w : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 work w state)))
    (ho : Nonempty (Derivation body Delta (StepNonemptyWork H out w))) :
    Nonempty (Derivation body Delta (graph1 (modeProgram H) out state)) := by
  apply nonemptyCases H out w _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hw' := renameInto hw j Theta hj
  rw [graph1Rename] at hw'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hfields := consArrowFields (w.relabel j) (ys 0) (ys 1) (andLeft hq)
  have hrequest := headValue work (w.relabel j) (ys 0) (ys 1) xx hw' hfields
  have hrest := tailValue work (w.relabel j) (ys 0) (ys 1) xx hw' hfields
  have hv := fun i => requestFieldValue currentRequest i (ys 0)
    (ys 2) (ys 3) (ys 4) (ys 5) xx hrequest (andLeft (andRight hq))
  have htag := pairLeftValue raw (ys 5) (ys 6) (ys 7) xx (hv 3) (andLeft (andRight (andRight hq)))
  have hpayload := pairRightValue raw (ys 5) (ys 6) (ys 7) xx (hv 3) (andLeft (andRight (andRight hq)))
  exact modeBackward H (state.relabel j) (out.relabel j)
    (ys 2) (ys 3) (ys 4) (ys 6) (ys 7) (ys 1)
    (hv 0) (hv 1) (hv 2) htag hpayload hrest (andRight (andRight (andRight hq)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalStateProof
