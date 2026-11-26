module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionRunProof OriginalLambdaTraversalInternalCompletionOutputProof
open OriginalLambdaTraversalInternalCompletionTotalityProof OriginalLambdaTraversalInternalCompletionLambdaProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atBodyPayload (leaf : Program 2)
    (value d e body parameter bodyParameter payload bp bodyOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc bp) payload)))
    (hpb : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right bp body)))
    (hbody : Nonempty (Derivation positive Delta (graph2 (fold leaf) bodyOut body bodyParameter)))
    (hr : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor out d e bodyOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply completionAtFoldCases leaf body bodyParameter bp bodyOut _ hpb hbody
    (hasCompletion leaf body bodyParameter bp hpb)
  intro beta j Theta cb hj hcb hcc
  rw [graph2Rename]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hb' := renameInto hb j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [lambdaFieldsRename] at hf'
  rw [graph1Rename] at hp'
  rw [weakBoundRename,sucRelabel] at hb'
  rw [graph3Rename] at hr'
  exact completionFold leaf (value.relabel j) (parameter.relabel j) (payload.relabel j) (suc (suc cb))
    (out.relabel j) hp' (lambdaCount (payload.relabel j) (bp.relabel j) cb hb' hcb)
    (lambdaComplete leaf (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
      (parameter.relabel j) (bodyParameter.relabel j) cb (bodyOut.relabel j) (out.relabel j) hf' hr' hcc)

theorem atRootPayload (leaf : Program 2)
    (value d e body parameter bodyParameter payload bodyOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hbody : Nonempty (Derivation positive Delta (graph2 (fold leaf) bodyOut body bodyParameter)))
    (hr : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor out d e bodyOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases value body payload _
    (andLeft (andRight (andRight (andRight hf)))) hp (andLeft hf)
  intro beta j Theta bp hj hpb hb
  rw [graph2Rename]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hbody' := renameInto hbody j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [lambdaFieldsRename] at hf'
  rw [graph1Rename] at hp'
  rw [graph2Rename] at hbody'
  rw [graph3Rename] at hr'
  exact atBodyPayload leaf (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) (payload.relabel j) bp (bodyOut.relabel j) (out.relabel j)
    hf' hp' hb hpb hbody' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaSupportProof
