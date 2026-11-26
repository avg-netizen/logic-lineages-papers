module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionRunProof OriginalLambdaTraversalInternalCompletionOutputProof
open OriginalLambdaTraversalInternalCompletionTotalityProof OriginalLambdaTraversalInternalCompletionApplicationProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromDurations (leaf : Program 2)
    (value d e fn arg parameter payload fp ap cf ca fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel fp))))
    (hab : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound ca (payloadFuel ap))))
    (hfc : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hac : Nonempty (Derivation positive Delta (Completes leaf arg parameter ca aOut)))
    (hr : Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) :=
  completionFold leaf value parameter payload (suc (add cf (add ca (suc z)))) out hp
    (applicationCount payload fp ap cf ca hb hfb hab)
    (applicationComplete leaf value d e fn arg parameter cf ca fOut aOut out hf hr hfc hac)

theorem afterLeft (leaf : Program 2)
    (value d e fn arg parameter payload fp ap cf fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hpa : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right ap arg)))
    (ha : Nonempty (Derivation positive Delta (graph2 (fold leaf) aOut arg parameter)))
    (hfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel fp))))
    (hfc : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hr : Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply completionAtFoldCases leaf arg parameter ap aOut _ hpa ha (hasCompletion leaf arg parameter ap hpa)
  intro beta j Theta ca hj hab hac
  rw [graph2Rename]
  have hf' := renameInto hf j Theta hj
  rw [applicationFieldsRename] at hf'
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hp'
  have hb' := renameInto hb j Theta hj
  rw [weakBoundRename,childFuelSumRename] at hb'
  have hfb' := renameInto hfb j Theta hj
  rw [weakBoundRename,payloadFuelRename] at hfb'
  have hfc' := renameInto hfc j Theta hj
  rw [completesRename] at hfc'
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  exact fromDurations leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) (fp.relabel j) (ap.relabel j) (cf.relabel j) ca
    (fOut.relabel j) (aOut.relabel j) (out.relabel j) hf' hp' hb' hfb' hab hfc' hac hr'

theorem atPayloads (leaf : Program 2)
    (value d e fn arg parameter payload fp ap fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hpf : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right fp fn)))
    (hpa : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right ap arg)))
    (hfn : Nonempty (Derivation positive Delta (graph2 (fold leaf) fOut fn parameter)))
    (ha : Nonempty (Derivation positive Delta (graph2 (fold leaf) aOut arg parameter)))
    (hr : Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply completionAtFoldCases leaf fn parameter fp fOut _ hpf hfn (hasCompletion leaf fn parameter fp hpf)
  intro beta j Theta cf hj hfb hfc
  rw [graph2Rename]
  have hf' := renameInto hf j Theta hj
  rw [applicationFieldsRename] at hf'
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hp'
  have hb' := renameInto hb j Theta hj
  rw [weakBoundRename,childFuelSumRename] at hb'
  have hpa' := renameInto hpa j Theta hj
  rw [graph1Rename] at hpa'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  exact afterLeft leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) (fp.relabel j) (ap.relabel j) cf
    (fOut.relabel j) (aOut.relabel j) (out.relabel j) hf' hp' hb' hpa' ha' hfb hfc hr'

theorem atRootPayload (leaf : Program 2)
    (value d e fn arg parameter payload fOut aOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hfn : Nonempty (Derivation positive Delta (graph2 (fold leaf) fOut fn parameter)))
    (ha : Nonempty (Derivation positive Delta (graph2 (fold leaf) aOut arg parameter)))
    (hr : Nonempty (Derivation positive Delta (graph4 application out d e fOut aOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply OriginalLambdaTraversalInternalPayloadApplicationProof.applicationPayloadCases value fn arg payload _
    (andLeft (andRight (andRight (andRight hf)))) (andRight (andRight (andRight (andRight hf)))) hp (andLeft hf)
  intro beta j Theta fp ap hj hpf hpa hb
  rw [graph2Rename]
  have hf' := renameInto hf j Theta hj
  rw [applicationFieldsRename] at hf'
  have hp' := renameInto hp j Theta hj
  rw [graph1Rename] at hp'
  have hfn' := renameInto hfn j Theta hj
  rw [graph2Rename] at hfn'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  exact atPayloads leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) fp ap (fOut.relabel j) (aOut.relabel j) (out.relabel j)
    hf' hp' hb hpf hpa hfn' ha' hr'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalApplicationSupportProof
