module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLambdaChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaTraversalSelection OriginalFinalGuardedRankObserverProof
open OriginalFinalGuardedRankSyntaxProof OriginalFinalGuardedRankBindingProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalRawSyntaxTransport (variableRankPackedRaw)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atChild (data : Data) (window : Program 1)
    (q input typ out parameter mark d e child bodyParameter childPayload childOut : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (belowPayload data window q)))
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hcr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
    (hcl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
    (hchild : Nonempty (Derivation body Delta (graph2 (canonical data window) childOut child bodyParameter))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  apply programCases variableRankPackedRaw (Fin.cons child Fin.elim0) _
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
  obtain ⟨hi⟩ := belowPayloadApply data window (q.relabel j) (childPayload.relabel j)
    (child.relabel j) (e.relabel j) (childOut.relabel j) (bodyParameter.relabel j) rank
    hb' hcl' hcr' (andIntro (andLeft cp) (andIntro (andRight cp) hchild'))
  obtain ⟨hrank⟩ := hrank
  have hrankOut : Nonempty (Derivation body Theta (graph1 variableRankPackedRaw rank (childOut.relabel j))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hrank⟩
  have old := andRight (OriginalLambdaTraversalLambdaRootProof.sourceConstructor data window
    (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (typ.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) hf' (andRight hs) (andLeft hs))
  have new := OriginalLambdaTraversalInternalLambdaProof.lambdaForward (leaf data window)
    (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) (childOut.relabel j) (out.relabel j)
    hf' hchild' (andRight (andRight hp'))
  have hin := OriginalFinalGuardedRankConstructorProof.lambdaValue (input.relabel j)
    (d.relabel j) (e.relabel j) (child.relabel j) rank old ⟨hrank⟩
  have hout := OriginalFinalGuardedRankConstructorProof.lambdaValue (out.relabel j)
    (d.relabel j) (e.relabel j) (childOut.relabel j) rank new hrankOut
  exact BottomRepresentativeInternalProof.indicatorIff variableRankPackedRaw (mark.relabel j)
    (out.relabel j) (input.relabel j) rank rank hout hin ⟨refl rank⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankLambdaChildProof
