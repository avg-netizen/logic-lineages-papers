module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobReconcileProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationOffsetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletedCellProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalInternalIndexedPrefixCasesTargets (bump)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem deletedCell (H : Program 1) (M W : Program 2) (arity : Nat)
 (index cutoff role typ raw gamma c contextCount deleted erasedType erased
  rawCell erasedParameter inheritedAnnotation child childRole childType typed stored annotation childRaw childParameter childGamma : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
 (hindex : Nonempty (Derivation body Delta (eqn index (bump arity cutoff))))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length contextCount gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff contextCount)))
 (hdelete : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (herase : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell erased erasedParameter)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParameter c deleted)))
 (hinherit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inheritedAnnotation role typ)))
 (hdecor : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hann : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 have hacc := OriginalInternalJobAdmissibleDeletionProof.actualDeletion body H M W alpha Delta
  role typ raw gamma c contextCount cutoff deleted erasedType erased ha hl hb hdelete hlookup herase
 have hnot := OriginalInternalAnnotationOffsetProof.shiftedNotBelow arity index cutoff hindex
 have hinherited := OriginalInternalAnnotationInheritedProof.actualInherited body alpha Delta
  index role typ raw (numeral arity) inheritedAnnotation harity hnot hinherit
 exact OriginalInternalJobReconcileProof.reconcile H M W
  index role typ raw rawCell child childRole childType typed stored annotation
  inheritedAnnotation role typ erased erasedParameter deleted childRaw childParameter childGamma c
  hdecor hp ht hann hinherit hinherited hr hg hcr hcg hacc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletedCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletedCellProof
