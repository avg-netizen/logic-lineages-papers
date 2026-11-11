module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionPayloadBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceApplicationProof
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


theorem fromRuns (leaf : Program 2) (value d e fn arg parameter payload fp ap cf ca fOut aOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel fp))))
    (hab : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound ca (payloadFuel ap))))
    (hfc : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hac : Nonempty (Derivation positive Delta (Completes leaf arg parameter ca aOut))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply programCases application (Fin.cons d (Fin.cons e (Fin.cons fOut (Fin.cons aOut Fin.elim0)))) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hfb' := renameInto hfb j Theta hj
  have hab' := renameInto hab j Theta hj
  have hfc' := renameInto hfc j Theta hj
  have hac' := renameInto hac j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel,InternalPairingSumBounds.childFuelSum] at hf' hb' hfb' hab' hfc' hac'
  simp only [consTermRename,emptyRename] at hp
  exact hasCompletionIntro leaf (value.relabel j) (parameter.relabel j) (payload.relabel j)
    (suc (add (cf.relabel j) (add (ca.relabel j) (suc z)))) produced
    (applicationCount (payload.relabel j) (fp.relabel j) (ap.relabel j) (cf.relabel j) (ca.relabel j) hb' hfb' hab')
    (OriginalLambdaTraversalInternalCompletionApplicationProof.applicationComplete leaf
      (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) (parameter.relabel j)
      (cf.relabel j) (ca.relabel j) (fOut.relabel j) (aOut.relabel j) produced hf' hp hfc' hac')

theorem fromFunction (leaf : Program 2) (value d e fn arg parameter payload fp ap cf fOut : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hfb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound cf (payloadFuel fp))))
    (hfc : Nonempty (Derivation positive Delta (Completes leaf fn parameter cf fOut)))
    (hac : Nonempty (Derivation positive Delta (HasCompletion leaf arg parameter ap))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply hasCompletionCases leaf arg parameter ap _ hac
  intro beta j Theta ca aOut hj hab hac'
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hfb' := renameInto hfb j Theta hj
  have hfc' := renameInto hfc j Theta hj
  simp only [ApplicationFields,conjunctionRename,graph1Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel,completesRename,hasCompletionRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel,InternalPairingSumBounds.childFuelSum] at hf' hb' hfb' hfc'
  exact fromRuns leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) (fp.relabel j) (ap.relabel j) (cf.relabel j) ca
    (fOut.relabel j) aOut hf' hb' hfb' hab hfc' hac'

theorem fromChildren (leaf : Program 2) (value d e fn arg parameter payload fp ap : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (InternalPairingSumBounds.childFuelSum fp ap) payload)))
    (hfc : Nonempty (Derivation positive Delta (HasCompletion leaf fn parameter fp)))
    (hac : Nonempty (Derivation positive Delta (HasCompletion leaf arg parameter ap))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply hasCompletionCases leaf fn parameter fp _ hfc
  intro beta j Theta cf fOut hj hfb hfc'
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hb' := renameInto hb j Theta hj
  have hac' := renameInto hac j Theta hj
  simp only [ApplicationFields,conjunctionRename,graph1Rename,SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel,completesRename,hasCompletionRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel,InternalPairingSumBounds.childFuelSum] at hf' hb' hac'
  exact fromFunction leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) (fp.relabel j) (ap.relabel j) cf fOut hf' hb' hfb hfc' hac'

theorem fromFields (leaf : Program 2) (value d e fn arg parameter payload : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply OriginalLambdaTraversalInternalPayloadApplicationProof.applicationPayloadCases value fn arg payload _
    (andLeft (andRight (andRight (andRight hf)))) (andRight (andRight (andRight (andRight hf)))) hp (andLeft hf)
  intro beta j Theta fp ap hj hfp hap hb
  rw [hasCompletionRename]
  have hf' := renameInto hf j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at hf' hi'
  have hd := applicationDescent (payload.relabel j) fp ap hb
  exact fromChildren leaf (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (parameter.relabel j) (payload.relabel j) fp ap hf' hb
    (belowPayloadApply leaf (payload.relabel j) fp (fn.relabel j) (parameter.relabel j) hi' (andLeft hd) hfp)
    (belowPayloadApply leaf (payload.relabel j) ap (arg.relabel j) (parameter.relabel j) hi' (andRight hd) hap)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceApplicationProof
