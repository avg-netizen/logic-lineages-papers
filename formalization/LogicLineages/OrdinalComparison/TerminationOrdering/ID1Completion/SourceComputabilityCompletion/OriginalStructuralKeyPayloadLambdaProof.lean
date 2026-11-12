module
-- Recovery draft reconstructed after environment reset; not an exact restored artifact.
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaRecurrenceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open OriginalLambdaTraversalSelection OriginalStructuralKeyPayloadDefinitions
open OriginalStructuralKeyPayloadSyntaxProof OriginalStructuralKeyPayloadBindingProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The lambda IH is instantiated at its actual different raw parameter,
with child validity/type/window derived from the original parent graphs. -/
theorem atOutput (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1) (K : Program 2) (lamLaw : LambdaLaw data window K)
    (q input typ out parameter mark d e child bodyParameter childPayload childOut : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
    (hcl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
    (hchild : Nonempty (Derivation body Delta (graph2 (canonical data window) childOut child bodyParameter))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark)) := by
  apply programCases K (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) _
  intro beta j Theta rank hj hrank
  rw [observationsRename]
  simp only [consTermRename,emptyRename] at hrank
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
  have hchild' := renameInto hchild j Theta hj
  rw [graph2Rename] at hchild'
  have hs := andLeft (andRight hp')
  have cp := OriginalLambdaTraversalLambdaOutputProof.childPremises data window
    (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (typ.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) hf' (andLeft hp') hs
  obtain ⟨hi⟩ := belowPayloadApply data window K (q.relabel j) (childPayload.relabel j)
    (child.relabel j) (e.relabel j) (childOut.relabel j) (bodyParameter.relabel j) rank
    hb' hcl' hcr' (andIntro (andLeft cp) (andIntro (andRight cp) hchild'))
  obtain ⟨hrank⟩ := hrank
  have hrankOut : Nonempty (Derivation body Theta (graph2 K rank (childOut.relabel j) (bodyParameter.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hrank⟩
  exact lamLaw body beta Theta (input.relabel j) (out.relabel j) (typ.relabel j)
    (parameter.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (bodyParameter.relabel j) (childOut.relabel j) rank (mark.relabel j)
    hp' hf' hchild' ⟨hrank⟩ hrankOut



/-- The actual child C graph is obtained by Program totality and discharged
inside the object-language continuation. -/
theorem withChildOutput (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1) (K : Program 2) (lamLaw : LambdaLaw data window K)
    (q input typ out parameter mark d e child bodyParameter childPayload : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
    (hcl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark)) := by
  apply programCases (canonical data window) (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) _
  intro beta j Theta childOut hj hchild
  rw [observationsRename]
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
  exact atOutput recurrence data window K lamLaw (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (mark.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (bodyParameter.relabel j)
    (childPayload.relabel j) childOut hb' hp' hf' hcr' hcl' hchild

/-- The lambda body payload bound is proved from the original raw pairs,
not from source decoding or an assumed successful child execution. -/
theorem atFields (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1) (K : Program 2) (lamLaw : LambdaLaw data window K)
    (q input typ out parameter mark d e child bodyParameter : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark)) := by
  apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases input child q _
    (andLeft (andRight (andRight (andRight hf)))) hr (andLeft hf)
  intro beta j Theta childPayload hj hcr hbound
  rw [observationsRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  exact withChildOutput recurrence data window K lamLaw (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (mark.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (bodyParameter.relabel j)
    childPayload hb' hp' hf' hcr (OriginalLambdaTraversalInternalPayloadArithmeticProof.lambdaDescent _ _ hbound)

/-- The literal tag ONE opens exactly the original selector witnesses.
All actual child graphs and four IH facts are conclusions of this step. -/
theorem atTag (recurrence : ActualOriginalLambdaTraversalInternalLambda)
    (data : Data) (window : Program 1) (K : Program 2) (lamLaw : LambdaLaw data window K) (q input typ out parameter mark : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window K q)))
    (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversal.rawTag InternalOriginalStepGuard.one input))) :
    Nonempty (Derivation body Delta (observations K out input parameter mark)) := by
  apply OriginalLambdaTraversalOutputLambdaOpeningProof.lambdaFieldsCases input parameter _ ht
  intro beta j Theta d e child bodyParameter hj hf
  rw [observationsRename]
  have hb' := renameInto hb j Theta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact atFields recurrence data window K lamLaw (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (mark.relabel j) d e child bodyParameter hb' hr' hp' hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadLambdaProof
