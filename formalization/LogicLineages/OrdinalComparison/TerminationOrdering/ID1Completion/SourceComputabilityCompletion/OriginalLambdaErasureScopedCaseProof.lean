module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedCaseSquaresProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedCaseSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedCaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaErasureScopedCaseDefinitions OriginalLambdaErasureCaseSupportProof
open OriginalLambdaOriginalRankDefinitions (Result)
open OriginalLambdaOriginalRankDichotomyProof (resultRename)
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaErasureScopedCaseSquaresProof (squareRename)
open OriginalLambdaErasureScopedCaseSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended oldChildExtended context before after : OTerm alpha)
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldS domain codomain oldBody arrow)))
 (htf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldT domain codomain oldTargetBody arrow)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) oldS oldParam)))
 (hc : Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (numeral 1) oldBody oldTargetBody oldChildCert oldChildParam)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)))
 (het : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)))
 (hce : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode oldChildExtended domain extended)))
 (hocp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldChildParam context oldChildExtended)))
 (hstrip : Nonempty (Derivation body Delta (graph1 OriginalLambdaGuardLeaf.stripCertificate oldChildCert oldCert)))
 (ih : ScopedChildIH body (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert codomain erasedType cutoff context before after)
 :
 Nonempty (Derivation body Delta (Result (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) newS newT newParam oldS oldT before after)) := by
 apply OriginalLambdaErasureCasePayloadProof.packedFromFields oldS domain codomain oldBody arrow _ hsf
 intro beta j Theta rawS hj hpS
 rw [resultRename]
 have hsf := renameInto hsf j Theta hj
 simp only [fieldsRename] at hsf
 have htf := renameInto htf j Theta hj
 simp only [fieldsRename] at htf
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] at hs
 have hc := renameInto hc j Theta hj
 simp only [graph4Rename, GuardedSourceSyntaxProof.numeralRename] at hc
 have hi := renameInto hi j Theta hj
 simp only [OriginalContextInsertionSyntaxProof.insertRename] at hi
 have hes := renameInto hes j Theta hj
 simp only [graph3Rename] at hes
 have het := renameInto het j Theta hj
 simp only [graph3Rename] at het
 have hop := renameInto hop j Theta hj
 simp only [graph2Rename] at hop
 have hnp := renameInto hnp j Theta hj
 simp only [graph2Rename] at hnp
 have hce := renameInto hce j Theta hj
 simp only [graph2Rename] at hce
 have hocp := renameInto hocp j Theta hj
 simp only [graph2Rename] at hocp
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have ih := scopedChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert codomain erasedType cutoff context before after j ih
 let oldS := oldS.relabel j
 let oldT := oldT.relabel j
 let oldCert := oldCert.relabel j
 let oldBody := oldBody.relabel j
 let oldTargetBody := oldTargetBody.relabel j
 let oldChildCert := oldChildCert.relabel j
 let oldParam := oldParam.relabel j
 let oldChildParam := oldChildParam.relabel j
 let newS := newS.relabel j
 let newT := newT.relabel j
 let newParam := newParam.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let erasedType := erasedType.relabel j
 let cutoff := cutoff.relabel j
 let gamma := gamma.relabel j
 let extended := extended.relabel j
 let oldChildExtended := oldChildExtended.relabel j
 let context := context.relabel j
 let before := before.relabel j
 let after := after.relabel j

 apply OriginalLambdaErasureCasePayloadProof.packedFromFields oldT domain codomain oldTargetBody arrow _ htf
 intro beta j Theta rawT hj hpT
 rw [resultRename]
 have hsf := renameInto hsf j Theta hj
 simp only [fieldsRename] at hsf
 have htf := renameInto htf j Theta hj
 simp only [fieldsRename] at htf
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] at hs
 have hc := renameInto hc j Theta hj
 simp only [graph4Rename, GuardedSourceSyntaxProof.numeralRename] at hc
 have hi := renameInto hi j Theta hj
 simp only [OriginalContextInsertionSyntaxProof.insertRename] at hi
 have hes := renameInto hes j Theta hj
 simp only [graph3Rename] at hes
 have het := renameInto het j Theta hj
 simp only [graph3Rename] at het
 have hop := renameInto hop j Theta hj
 simp only [graph2Rename] at hop
 have hnp := renameInto hnp j Theta hj
 simp only [graph2Rename] at hnp
 have hce := renameInto hce j Theta hj
 simp only [graph2Rename] at hce
 have hocp := renameInto hocp j Theta hj
 simp only [graph2Rename] at hocp
 have hpS := renameInto hpS j Theta hj
 simp only [graph3Rename] at hpS
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have ih := scopedChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert codomain erasedType cutoff context before after j ih
 let oldS := oldS.relabel j
 let oldT := oldT.relabel j
 let oldCert := oldCert.relabel j
 let oldBody := oldBody.relabel j
 let oldTargetBody := oldTargetBody.relabel j
 let oldChildCert := oldChildCert.relabel j
 let oldParam := oldParam.relabel j
 let oldChildParam := oldChildParam.relabel j
 let newS := newS.relabel j
 let newT := newT.relabel j
 let newParam := newParam.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let erasedType := erasedType.relabel j
 let cutoff := cutoff.relabel j
 let gamma := gamma.relabel j
 let extended := extended.relabel j
 let oldChildExtended := oldChildExtended.relabel j
 let context := context.relabel j
 let before := before.relabel j
 let after := after.relabel j
 let rawS := rawS.relabel j

 exact OriginalLambdaErasureScopedCaseSquaresProof.atPayloads H G M W oldStep endpoint window
   oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended oldChildExtended context before after rawS rawT
   hsf htf hs hc hi hes het hop hnp hce hocp hstrip ih hpS hpT

theorem actualScopedLambdaErasureCase : ActualScopedLambdaErasureCase := by
 intro H G M W oldStep endpoint window body alpha Delta
   oldS oldT oldCert oldParam newS newT newParam oldBody domain codomain arrow
   erasedType cutoff gamma extended context before after
 dsimp only
 intro hsf hs hroot hi hes het hop hnp ih
 apply OriginalHereditaryLambdaGlobalInternalProof.actualOriginalHereditaryLambdaGlobalInternalClosure
   endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)
   body alpha Delta oldS oldT oldCert oldParam _ hroot
 intro beta j Theta hj recoveredS recoveredT childCert childParam recovered
 rw [resultRename]
 have hsf := renameInto hsf j Theta hj
 simp only [fieldsRename] at hsf
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] at hs
 have hi := renameInto hi j Theta hj
 simp only [OriginalContextInsertionSyntaxProof.insertRename] at hi
 have hes := renameInto hes j Theta hj
 simp only [graph3Rename] at hes
 have het := renameInto het j Theta hj
 simp only [graph3Rename] at het
 have hop := renameInto hop j Theta hj
 simp only [graph2Rename] at hop
 have hnp := renameInto hnp j Theta hj
 simp only [graph2Rename] at hnp
 have childCertGraph := andLeft (andRight (andRight (andRight (andRight (andRight recovered)))))
 have hstrip := unaryRecover OriginalLambdaGuardLeaf.stripCertificate (.projection 2)
   childCert (oldCert.relabel j)
   (Fin.cons (oldS.relabel j) (Fin.cons (oldT.relabel j) (Fin.cons (oldCert.relabel j) (Fin.cons (oldParam.relabel j) Fin.elim0))))
   childCertGraph (projectionValue (2 : Fin 4)
     (Fin.cons (oldS.relabel j) (Fin.cons (oldT.relabel j) (Fin.cons (oldCert.relabel j) (Fin.cons (oldParam.relabel j) Fin.elim0)))))
 have ih := scopedChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert codomain erasedType cutoff context before after j ih
 let oldS := oldS.relabel j
 let oldT := oldT.relabel j
 let oldCert := oldCert.relabel j
 let oldParam := oldParam.relabel j
 let newS := newS.relabel j
 let newT := newT.relabel j
 let newParam := newParam.relabel j
 let oldBody := oldBody.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let erasedType := erasedType.relabel j
 let cutoff := cutoff.relabel j
 let gamma := gamma.relabel j
 let extended := extended.relabel j
 let context := context.relabel j
 let before := before.relabel j
 let after := after.relabel j

 apply OriginalLambdaRecoveredGeometryProof.actualOriginalLambdaRecoveredGeometry body beta Theta
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) oldS oldT oldCert oldParam oldBody recoveredS recoveredT childCert childParam
   domain codomain arrow context extended _ hsf hop recovered
 intro beta j Theta oldChildExtended hj geometry
 rw [resultRename]
 have hsf := renameInto hsf j Theta hj
 simp only [fieldsRename] at hsf
 have hs := renameInto hs j Theta hj
 simp only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] at hs
 have hi := renameInto hi j Theta hj
 simp only [OriginalContextInsertionSyntaxProof.insertRename] at hi
 have hes := renameInto hes j Theta hj
 simp only [graph3Rename] at hes
 have het := renameInto het j Theta hj
 simp only [graph3Rename] at het
 have hop := renameInto hop j Theta hj
 simp only [graph2Rename] at hop
 have hnp := renameInto hnp j Theta hj
 simp only [graph2Rename] at hnp
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have ih := scopedChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert codomain erasedType cutoff context before after j ih
 let oldS := oldS.relabel j
 let oldT := oldT.relabel j
 let oldCert := oldCert.relabel j
 let oldParam := oldParam.relabel j
 let newS := newS.relabel j
 let newT := newT.relabel j
 let newParam := newParam.relabel j
 let oldBody := oldBody.relabel j
 let domain := domain.relabel j
 let codomain := codomain.relabel j
 let arrow := arrow.relabel j
 let erasedType := erasedType.relabel j
 let cutoff := cutoff.relabel j
 let gamma := gamma.relabel j
 let extended := extended.relabel j
 let context := context.relabel j
 let before := before.relabel j
 let after := after.relabel j
 let recoveredS := recoveredS.relabel j
 let recoveredT := recoveredT.relabel j
 let childCert := childCert.relabel j
 let childParam := childParam.relabel j

 have htf := andLeft (andRight geometry)
 have hce := andLeft (andRight (andRight (andRight geometry)))
 have hocp := andLeft (andRight (andRight (andRight (andRight geometry))))
 have hc := leafSourceTransport (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) recoveredS oldBody recoveredT childCert childParam
   (andLeft geometry) (andRight (andRight (andRight (andRight (andRight geometry)))))
 exact fromFields H G M W oldStep endpoint window oldS oldT oldCert oldBody recoveredT childCert
   oldParam childParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended
   oldChildExtended context before after hsf htf hs hc hi hes het hop hnp hce hocp hstrip ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedCaseProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedCaseProof
