module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaRootEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellProof
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
open InternalTagArithmeticSyntaxProof (suc)
theorem cellAtCoordinates (Q : Program 2) (input other domain codomain child otherChild parameter childParameter c gamma extended count childRow otherChildRow tail otherTail cutoff erasedType deleted deletedParam childDeleted childDeletedParam inputE otherE childE otherChildE value otherValue out otherOut : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input domain codomain child parameter childParameter)))
 (hf2 : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields other domain codomain otherChild parameter childParameter)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input domain codomain child)))
 (hc2 : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hext : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) childRow child childParameter)))
 (hr2 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) otherChildRow otherChild childParameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (numeral 1) childRow)))
 (ht2 : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop otherTail (numeral 1) otherChildRow)))
 (heq : Nonempty (Derivation body Delta (equal tail otherTail)))
 (hbound : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup erasedType cutoff gamma)))
 (hdelete : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (hdp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing deletedParam c deleted)))
 (hcd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted domain deleted)))
 (hcdp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childDeletedParam c childDeleted)))
 (hie : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw inputE erasedType cutoff input)))
 (hoe : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw otherE erasedType cutoff other)))
 (hce : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childE erasedType (suc cutoff) child)))
 (hoce : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw otherChildE erasedType (suc cutoff) otherChild)))
 (hq : Nonempty (Derivation body Delta (graph2 Q value childE childDeletedParam)))
 (hq2 : Nonempty (Derivation body Delta (graph2 Q otherValue otherChildE childDeletedParam)))
 (hobs : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalRootObservation.rootObservation Q)) out cutoff input parameter)))
 (hobs2 : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalRootObservation.rootObservation Q)) otherOut cutoff other parameter)))
 :
 Nonempty (Derivation body Delta (equal out otherOut)) := by
 obtain ⟨hinsert⟩ := OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion body alpha Delta count gamma cutoff deleted erasedType
 obtain ⟨hins⟩ := andIntro hlen (andIntro hbound (andIntro hdelete hlookup))
 have hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)) := ⟨Derivation.implicationElimination hinsert hins⟩
 have shifted := OriginalPositionStructuralKeyLambdaContextProof.shiftedLookupAndDeletion gamma deleted extended childDeleted domain cutoff erasedType hext hcd hlookup hdelete
 have selChild := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro (suc cutoff) child childParameter c extended erasedType childDeleted childE childDeletedParam hcp shifted.1 shifted.2 hce hcdp
 have selOtherChild := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro (suc cutoff) otherChild childParameter c extended erasedType childDeleted otherChildE childDeletedParam hcp shifted.1 shifted.2 hoce hcdp
 have obsChild := binaryValue Q OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter value childE childDeletedParam ![suc cutoff,child,childParameter] hq selChild.1 selChild.2
 have obsOtherChild := binaryValue Q OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter otherValue otherChildE childDeletedParam ![suc cutoff,otherChild,childParameter] hq2 selOtherChild.1 selOtherChild.2
 have extLength := OriginalContextInsertionLengthProof.lengthCons extended domain gamma count hext hlen
 have childBound := InternalRecursionGraphExtensionSupportProof.successorOrder cutoff count hbound
 have values := OriginalHereditaryDeletionRowsLambdaChildProof.childTailValues Q count child otherChild childParameter c extended cutoff childRow otherChildRow tail otherTail value otherValue hcp extLength childBound hr hr2 ht ht2 heq obsChild obsOtherChild
 have erasedF := OriginalPositionStructuralKeyLambdaGeometryProof.erasedFields input inputE child childE domain codomain parameter childParameter erasedType cutoff c deleted gamma deletedParam childDeleted childDeletedParam hf hc hie hce hi hdp hcd hcdp
 have erasedF2 := OriginalPositionStructuralKeyLambdaGeometryProof.erasedFields other otherE otherChild otherChildE domain codomain parameter childParameter erasedType cutoff c deleted gamma deletedParam childDeleted childDeletedParam hf2 hc2 hoe hoce hi hdp hcd hcdp
 have sel := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro cutoff input parameter c gamma erasedType deleted inputE deletedParam hp hlookup hdelete hie hdp
 have sel2 := OriginalHereditaryDeletionRowsSquareSupportProof.selectorsIntro cutoff other parameter c gamma erasedType deleted otherE deletedParam hp hlookup hdelete hoe hdp
 have root := binaryRecover (OriginalRootObservation.rootObservation Q) OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter out inputE deletedParam ![cutoff,input,parameter] hobs sel.1 sel.2
 have root2 := binaryRecover (OriginalRootObservation.rootObservation Q) OriginalClassContextAllPositionObserver.erasedPacked OriginalClassContextAllPositionObserver.erasedParameter otherOut otherE deletedParam ![cutoff,other,parameter] hobs2 sel2.1 sel2.2
 rw [equalEqn] at values
 obtain ⟨values⟩ := values
 have hq2' := outputTransport Q otherValue value ![otherChildE,childDeletedParam] ⟨InternalTagArithmeticSupportProof.symm values⟩ hq2
 exact OriginalHereditaryDeletionRowsLambdaRootEqualityProof.sameChildValue Q inputE otherE domain codomain childE otherChildE deletedParam childDeletedParam c deleted childDeleted value out otherOut (andLeft erasedF) (andLeft erasedF2) (andRight erasedF) (andRight erasedF2) hdp hcd hcdp hq hq2' root root2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellProof
