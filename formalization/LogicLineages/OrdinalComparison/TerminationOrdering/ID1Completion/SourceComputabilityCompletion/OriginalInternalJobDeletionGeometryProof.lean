module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletedCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobContextTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm refl)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalInternalIndexedPrefixCasesTargets (bump)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atGeometry (H : Program 1) (M W : Program 2) (arity : Nat)
 (index cutoff role typ raw parameter gamma c contextCount queryGamma queryC deleted erasedType erased rawCell erasedParameter inheritedAnnotation child childRole childType typed stored annotation childRaw childParameter childGamma : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hqp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter queryC queryGamma)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
 (hindex : Nonempty (Derivation body Delta (eqn index (bump arity cutoff))))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length contextCount queryGamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff contextCount)))
 (hdelete : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff queryGamma)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff queryGamma)))
 (herase : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased erasedType cutoff raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell erased erasedParameter)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParameter queryC deleted)))
 (hinherit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inheritedAnnotation role typ)))
 (hdecor : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hann : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 : Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 have he := OriginalInternalAnnotationEqualityProof.pairFields parameter parameter queryC queryGamma c gamma
  hqp hp ⟨refl parameter⟩
 have hac := OriginalInternalJobContextTransportProof.contexts H M W role typ raw gamma c queryGamma queryC
  ⟨symm (Classical.choice (andRight he))⟩ ⟨symm (Classical.choice (andLeft he))⟩ ha
 have hleft := outputTransport InternalUnpair.left c queryC (Fin.cons childParameter Fin.elim0)
  ⟨symm (Classical.choice (andLeft he))⟩ (pairLeft childParameter c childGamma hcg)
 have hchildParam := reconstructPair childParameter queryC childGamma hleft (pairRight childParameter c childGamma hcg)
 have hresult := OriginalInternalJobDeletedCellProof.deletedCell H M W arity
  index cutoff role typ raw queryGamma queryC contextCount deleted erasedType erased
  rawCell erasedParameter inheritedAnnotation child childRole childType typed stored annotation childRaw childParameter childGamma
  hac harity hindex hl hb hdelete hlookup herase hr hg hinherit hdecor hcp ht hann hcr hchildParam
 exact OriginalInternalJobContextTransportProof.contexts H M W childRole childType childRaw childGamma queryC childGamma c
  ⟨refl childGamma⟩ (andLeft he) hresult
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionGeometryProof
