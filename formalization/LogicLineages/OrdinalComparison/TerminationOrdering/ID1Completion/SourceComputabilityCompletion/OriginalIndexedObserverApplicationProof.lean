module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection OriginalIndexedObserverDefinitions
open OriginalIndexedObserverSyntaxProof OriginalIndexedObserverBindingProof
open OriginalIndexedObserverRangeSyntaxProof (rangeRename)
open OriginalLambdaTraversalInternalTargets InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The function observer IH uses the original strictly smaller payload.
Both actual child output types come from the independently checked OutputLaws. -/
theorem atOutputs (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K)
    (q input typ parameter payload arrow d e fp ap fn arg functionOut argumentOut out mark cutoff : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hRange : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload)))
    (hf : Nonempty (Derivation body Delta (graph2 (canonical data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (canonical data window) argumentOut arg parameter))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark cutoff)) := by
  have hs := andLeft (andRight hp)
  have children := OriginalApplicationInverseValidityProof.sourceRecover
    (leafData data window) arrow d e fp ap fn arg input parameter hc (andLeft hs)
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload q (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  obtain ⟨hal⟩ := hal
  have hwf := BottomDescentStepProof.windowChange window (suc z) input fn parameter (andLeft hp)
  have hwa := BottomDescentStepProof.windowChange window (suc z) input arg parameter (andLeft hp)
  have hfp := andIntro hwf (andIntro (andIntro (andLeft (andRight children))
      (pairLeft fn arrow fp (andLeft (andRight hc)))) hf)
  have hap := andIntro hwa (andIntro (andIntro (andRight (andRight children))
      (pairLeft arg d ap (andLeft (andRight (andRight hc))))) ha)
  have fields := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap fn arg input hc
  obtain ⟨law⟩ := recurrence body (leaf data window) alpha Delta
    input d e fn arg functionOut argumentOut out parameter
  obtain ⟨prem⟩ := andIntro fields (andIntro hf ha)
  obtain ⟨hparent⟩ := andRight (andRight hp)
  have hraw : Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law prem)) hparent⟩
  have hinput : Nonempty (Derivation body Delta (graph4 application input d e fn arg)) :=
    applicationBackward d e fn arg fp ap input hfr har (andRight (andRight (andRight hc)))
  change Nonempty (Derivation body Delta (premises data window functionOut fn arrow parameter)) at hfp
  change Nonempty (Derivation body Delta (premises data window argumentOut arg d parameter)) at hap
  apply OriginalIndexedObserverQueryProof.indexedPairOutputCases K fn arg parameter cutoff _
  intro beta j Theta fValue aValue hj hfk hak
  rw [observationsRename]
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hfp' := renameInto hfp j Theta hj
  have hap' := renameInto hap j Theta hj
  rw [premisesRename] at hfp' hap'
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  rw [graph1Rename] at hfr' har'
  have hfl' := renameInto (show Nonempty (Derivation body Delta (InternalLessThan.strictLess fp q)) from ⟨orderRight fp hep hfl⟩) j Theta hj
  have hal' := renameInto (show Nonempty (Derivation body Delta (InternalLessThan.strictLess ap q)) from ⟨orderRight ap hep hal⟩) j Theta hj
  simp only [InternalLessThan.strictLess, InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  obtain ⟨hfi⟩ := belowPayloadApply data window K (q.relabel j) (fp.relabel j) (fn.relabel j)
    (arrow.relabel j) (functionOut.relabel j) (parameter.relabel j) fValue (cutoff.relabel j) hb' hfl' hfr' hfp' hRange'
  obtain ⟨hai⟩ := belowPayloadApply data window K (q.relabel j) (ap.relabel j) (arg.relabel j)
    (d.relabel j) (argumentOut.relabel j) (parameter.relabel j) aValue (cutoff.relabel j) hb' hal' har' hap' hRange'
  obtain ⟨hfk⟩ := hfk
  obtain ⟨hak⟩ := hak
  have hfout : Nonempty (Derivation body Theta (graph3 K fValue (cutoff.relabel j) (functionOut.relabel j) (parameter.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hfi) hfk⟩
  have haout : Nonempty (Derivation body Theta (graph3 K aValue (cutoff.relabel j) (argumentOut.relabel j) (parameter.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hai) hak⟩
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hi' := renameInto hinput j Theta hj
  have ho' := renameInto hraw j Theta hj
  rw [graph4Rename] at hi' ho'
  have fields' := renameInto fields j Theta hj
  rw [OriginalLambdaTraversalInternalFieldsSyntaxProof.applicationFieldsRename] at fields'
  have harrow := renameInto (andLeft hc) j Theta hj
  rw [graph2Rename] at harrow
  exact appLaw body beta Theta (input.relabel j) (out.relabel j) (typ.relabel j)
    (parameter.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fn.relabel j) (arg.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
    fValue aValue (mark.relabel j) (cutoff.relabel j) hRange' hp' hfp' hap' harrow fields' hi' ho' ⟨hfk⟩ hfout ⟨hak⟩ haout




/-- Bind actual child outputs internally; no child C graph appears in the
final induction-step antecedent. -/
theorem withOutputs (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K)
    (q input typ out parameter payload arrow d e fp ap fn arg mark cutoff : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hRange : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark cutoff)) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases (canonical data window) fn arg parameter _
  intro beta j Theta functionOut argumentOut hj hf ha
  rw [observationsRename]
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hc' := renameInto hc j Theta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hpr' := renameInto hpr j Theta hj
  have hfr' := renameInto hfr j Theta hj
  have har' := renameInto har j Theta hj
  rw [graph1Rename] at hpr' hfr' har'
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  unfold InternalLessThan.strictLess at hfl' hal'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl' hal'
  exact atOutputs recurrence data window K appLaw (q.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) functionOut argumentOut (out.relabel j) (mark.relabel j) (cutoff.relabel j)
    hb' hr' hp' hRange' hc' hpr' hfr' har' hfl' hal' hf ha

/-- Only the literal tag TWO is added to the genuine payload IH and frozen
window/source/type/C premises. All constructors and outputs are recovered. -/
theorem atTag (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1) (K : Program 3) (appLaw : ApplicationLaw data window K) (q input typ out parameter mark cutoff : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hRange : Nonempty (Derivation body Delta (ActualRange cutoff parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag positionTerm input))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark cutoff)) := by
  apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases input parameter _ ht
  intro beta j Theta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal
  rw [observationsRename]
  have hRange' := renameInto hRange j Theta hj
  rw [rangeRename] at hRange'
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact withOutputs recurrence data window K appLaw (q.relabel j) (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) payload arrow d e fp ap fn arg (mark.relabel j) (cutoff.relabel j) hb' hr' hp' hRange' hc hpr hfr har hfl hal

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverApplicationProof
