module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputApplicationInductionProof
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
open OriginalLambdaTraversalSelection OriginalLambdaTraversalOutput
open OriginalLambdaTraversalOutputSyntaxProof OriginalLambdaTraversalOutputBindingProof
open OriginalLambdaTraversalInternalTargets InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both actual child C outputs obtain all four invariant facts from the
strictly smaller original payloads. The runtime parameter stays shared. -/
theorem atOutputs (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1)
    (q input typ parameter payload arrow d e fp ap fn arg functionOut argumentOut out : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload)))
    (hf : Nonempty (Derivation body Delta (graph2 (canonical data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (canonical data window) argumentOut arg parameter))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  have hs := andLeft (andRight hp)
  have children := OriginalApplicationInverseValidityProof.sourceRecover
    (leafData data window) arrow d e fp ap fn arg input parameter hc (andLeft hs)
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload q (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  obtain ⟨hal⟩ := hal
  have hwf := BottomDescentStepProof.windowChange window (suc z) input fn parameter (andLeft hp)
  have hwa := BottomDescentStepProof.windowChange window (suc z) input arg parameter (andLeft hp)
  have hfi := belowPayloadApply data window q fp fn arrow functionOut parameter hb
    ⟨orderRight fp hep hfl⟩ hfr
    (andIntro hwf (andIntro (andIntro (andLeft (andRight children))
      (pairLeft fn arrow fp (andLeft (andRight hc)))) hf))
  have hai := belowPayloadApply data window q ap arg d argumentOut parameter hb
    ⟨orderRight ap hep hal⟩ har
    (andIntro hwa (andIntro (andIntro (andRight (andRight children))
      (pairLeft arg d ap (andLeft (andRight (andRight hc))))) ha))
  have fields := OriginalLambdaTraversalApplicationFieldsProof.fromConstructors arrow d e fp ap fn arg input hc
  obtain ⟨law⟩ := recurrence body (leaf data window) alpha Delta
    input d e fn arg functionOut argumentOut out parameter
  obtain ⟨prem⟩ := andIntro fields (andIntro hf ha)
  obtain ⟨hparent⟩ := andRight (andRight hp)
  have hraw : Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law prem)) hparent⟩
  exact OriginalLambdaTraversalOutputRecurrenceProof.applicationAtOutputs recurrence data window
    arrow d e fp ap fn arg input functionOut argumentOut out typ parameter hc hs hraw hfi hai

/-- Bind actual child outputs internally; no child C graph appears in the
final induction-step antecedent. -/
theorem withOutputs (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1)
    (q input typ out parameter payload arrow d e fp ap fn arg : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp fn)))
    (har : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap arg)))
    (hfl : Nonempty (Derivation body Delta (InternalLessThan.strictLess fp payload)))
    (hal : Nonempty (Derivation body Delta (InternalLessThan.strictLess ap payload))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases (canonical data window) fn arg parameter _
  intro beta j Theta functionOut argumentOut hj hf ha
  rw [outputInvariantRename]
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
  exact atOutputs recurrence data window (q.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) functionOut argumentOut (out.relabel j)
    hb' hr' hp' hc' hpr' hfr' har' hfl' hal' hf ha

/-- Only the literal tag TWO is added to the genuine payload IH and frozen
window/source/type/C premises. All constructors and outputs are recovered. -/
theorem atTag (recurrence : ActualOriginalLambdaTraversalInternalApplication)
    (data : Data) (window : Program 1) (q input typ out parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag positionTerm input))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  apply OriginalLambdaTraversalApplicationOpeningProof.applicationCases input parameter _ ht
  intro beta j Theta payload arrow d e fp ap fn arg hj hc hpr hfr har hfl hal
  rw [outputInvariantRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact withOutputs recurrence data window (q.relabel j) (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) payload arrow d e fp ap fn arg hb' hr' hp' hc hpr hfr har hfl hal

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputApplicationInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputApplicationInductionProof
