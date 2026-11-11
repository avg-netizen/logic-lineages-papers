module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRecurrenceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection OriginalLambdaTraversalOutput
open OriginalLambdaTraversalOutputSyntaxProof OriginalLambdaTraversalOutputBindingProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The lambda IH is instantiated at its actual different raw parameter,
with child validity/type/window derived from the original parent graphs. -/
theorem atOutput (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1)
    (q input typ out parameter d e child bodyParameter childPayload childOut : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
    (hcl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
    (hchild : Nonempty (Derivation body Delta (graph2 (canonical data window) childOut child bodyParameter))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  have hs := andLeft (andRight hp)
  have childSource := OriginalLambdaTraversalLambdaSourceProof.sourceChild data window
    input d e child parameter bodyParameter hf (andLeft hs)
  have childWindow := OriginalLambdaTraversalLambdaWindowProof.windowChild window
    (suc z) input child parameter bodyParameter (andRight (andRight (andRight (andRight hf)))) (andLeft hp)
  have hi := belowPayloadApply data window q childPayload child e childOut bodyParameter hb hcl hcr
    (andIntro childWindow (andIntro childSource hchild))
  obtain ⟨law⟩ := recurrence body (leaf data window) alpha Delta
    input d e child childOut out parameter bodyParameter
  obtain ⟨pre⟩ := andIntro hf hchild
  obtain ⟨hparent⟩ := andRight (andRight hp)
  have hraw : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law pre)) hparent⟩
  exact OriginalLambdaTraversalLambdaRecurrenceOutputProof.lambdaAtOutput recurrence data window
    input out d e child childOut typ parameter bodyParameter hf hs hi hraw

/-- The actual child C graph is obtained by Program totality and discharged
inside the object-language continuation. -/
theorem withChildOutput (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1)
    (q input typ out parameter d e child bodyParameter childPayload : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
    (hcl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  apply programCases (canonical data window) (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) _
  intro beta j Theta childOut hj hchild
  rw [outputInvariantRename]
  simp only [consTermRename,emptyRename] at hchild
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  have hcr' := renameInto hcr j Theta hj
  rw [graph1Rename] at hcr'
  have hcl' := renameInto hcl j Theta hj
  unfold InternalLessThan.strictLess at hcl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hcl'
  exact atOutput recurrence data window (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (bodyParameter.relabel j)
    (childPayload.relabel j) childOut hb' hp' hf' hcr' hcl' hchild

/-- The lambda body payload bound is proved from the original raw pairs,
not from source decoding or an assumed successful child execution. -/
theorem atFields (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1)
    (q input typ out parameter d e child bodyParameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases input child q _
    (andLeft (andRight (andRight (andRight hf)))) hr (andLeft hf)
  intro beta j Theta childPayload hj hcr hbound
  rw [outputInvariantRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  exact withChildOutput recurrence data window (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (bodyParameter.relabel j)
    childPayload hb' hp' hf' hcr (OriginalLambdaTraversalInternalPayloadArithmeticProof.lambdaDescent _ _ hbound)

/-- The literal tag ONE opens exactly the original selector witnesses.
All actual child graphs and four IH facts are conclusions of this step. -/
theorem atTag (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1) (q input typ out parameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversal.rawTag InternalOriginalStepGuard.one input))) :
    Nonempty (Derivation body Delta (outputInvariant data window out input typ parameter)) := by
  apply OriginalLambdaTraversalOutputLambdaOpeningProof.lambdaFieldsCases input parameter _ ht
  intro beta j Theta d e child bodyParameter hj hf
  rw [outputInvariantRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact atFields recurrence data window (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) d e child bodyParameter hb' hr' hp' hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaInductionProof
