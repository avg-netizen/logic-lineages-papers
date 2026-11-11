module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionPayloadBindingProof
open OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


theorem fromRun (leaf : Program 2) (value d e child parameter childParameter payload bp cb bodyOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e child parameter childParameter)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc bp) payload)))
    (hcb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cb (payloadFuel bp))))
    (hcc : Nonempty (Derivation positive Delta (Completes leaf child childParameter cb bodyOut))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply programCases OriginalLambdaConstructor.constructor (Fin.cons d (Fin.cons e (Fin.cons bodyOut Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hcb' := renameInto hcb j Theta hj
  have hcc' := renameInto hcc j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at hf' hb' hcb' hcc'
  simp only [consTermRename,emptyRename] at hp
  exact hasCompletionIntro leaf (value.relabel j) (parameter.relabel j) (payload.relabel j)
    (suc (suc (cb.relabel j))) produced
    (lambdaCount (payload.relabel j) (bp.relabel j) (cb.relabel j) hb' hcb')
    (OriginalLambdaTraversalInternalCompletionLambdaProof.lambdaComplete leaf (value.relabel j)
      (d.relabel j) (e.relabel j) (child.relabel j) (parameter.relabel j) (childParameter.relabel j)
      (cb.relabel j) (bodyOut.relabel j) produced hf' hp hcc')

theorem fromChild (leaf : Program 2) (value d e child parameter childParameter payload bp : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e child parameter childParameter)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (suc bp) payload)))
    (hc : Nonempty (Derivation positive Delta (HasCompletion leaf child childParameter bp))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply hasCompletionCases leaf child childParameter bp _ hc
  intro beta j Theta cb bodyOut hj hcb hcc
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at hf' hb'
  exact fromRun leaf (value.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (parameter.relabel j) (childParameter.relabel j) (payload.relabel j) (bp.relabel j) cb bodyOut hf' hb' hcb hcc

theorem fromFields (leaf : Program 2) (value d e child parameter childParameter payload : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e child parameter childParameter)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases value child payload _
    (andLeft (andRight (andRight (andRight hf)))) hp (andLeft hf)
  intro beta j Theta bp hj hbp hb
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at hf' hi'
  exact fromChild leaf (value.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (parameter.relabel j) (childParameter.relabel j) (payload.relabel j) bp hf' hb
    (belowPayloadApply leaf (payload.relabel j) bp (child.relabel j) (childParameter.relabel j)
      hi' (lambdaDescent (payload.relabel j) bp hb) hbp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceLambdaProof
