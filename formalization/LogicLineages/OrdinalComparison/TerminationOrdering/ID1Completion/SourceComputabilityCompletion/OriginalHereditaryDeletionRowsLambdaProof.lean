module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaAgreementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaTraversalInternalFieldsSyntaxProof (lambdaFieldsRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem exactShiftedLambdaRows : OriginalHereditaryDeletionRowsLambdaTargets.ShiftedLambdaRows := by
 intro Q body alpha Delta input other domain codomain child otherChild parameter childParameter c gamma extended count childRow otherChildRow tail otherTail row otherRow
 let A : Formula alpha := OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter ⊓ (OriginalLambdaTraversalInternal.LambdaFields other domain codomain otherChild parameter childParameter ⊓ (graph3 OriginalLambdaConstructor.constructor input domain codomain child ⊓ (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild ⊓ (graph2 InternalPairing.pairing parameter c gamma ⊓ (OriginalContextInsertion.lengthGraph count gamma ⊓ (graph2 InternalListCodec.consCode extended domain gamma ⊓ (graph2 InternalPairing.pairing childParameter c extended ⊓ (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter ⊓ (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter ⊓ (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow ⊓ (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow ⊓ (equal tail otherTail ⊓ (graph2 (OriginalHereditaryDeletionRows.rows (OriginalRootObservation.rootObservation Q)) row input parameter ⊓ (graph2 (OriginalHereditaryDeletionRows.rows (OriginalRootObservation.rootObservation Q)) otherRow other parameter))))))))))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hf := (andLeft h)
 have hf2 := (andLeft (andRight h))
 have hc := (andLeft (andRight (andRight h)))
 have hc2 := (andLeft (andRight (andRight (andRight h))))
 have hp := (andLeft (andRight (andRight (andRight (andRight h)))))
 have hlen := (andLeft (andRight (andRight (andRight (andRight (andRight h))))))
 have hext := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight h)))))))
 have hcp := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))
 have hr := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))))
 have hr2 := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))))
 have ht := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))))))
 have ht2 := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))))))
 have heq := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h)))))))))))))
 have hrow := (andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))))))))
 have hrow2 := (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight h))))))))))))))
 have hcells := OriginalHereditaryDeletionRowsLambdaAgreementProof.cells Q input other domain codomain child otherChild parameter childParameter c gamma extended count childRow otherChildRow tail otherTail hf hf2 hc hc2 hp hlen hext hcp hr hr2 ht ht2 heq
 obtain ⟨he⟩ := OriginalHereditaryDeletionRowsWrapperCongruenceProof.exactRowsCongruence (OriginalRootObservation.rootObservation Q) body alpha (A :: Delta) count input parameter gamma other parameter gamma row otherRow (pairRight parameter c gamma hp) hlen (pairRight parameter c gamma hp) hlen hcells hrow hrow2
 exact ⟨Derivation.implicationIntroduction he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaProof
