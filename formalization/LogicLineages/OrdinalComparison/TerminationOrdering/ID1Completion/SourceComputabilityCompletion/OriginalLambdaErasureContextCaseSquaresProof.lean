module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseSquaresProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceSupportProof
open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionClosureSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaErasureContextCaseDefinitions OriginalLambdaErasureCaseSupportProof
open OriginalLambdaOriginalRankDefinitions (Result)
open OriginalLambdaOriginalRankDichotomyProof (resultRename)
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalLambdaErasureContextCaseSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem squareRename {beta : Type}
 (out child childOut domain codomain erasedType cutoff childGamma childExtended : OTerm alpha) (j : alpha → beta) :
 (OriginalLambdaErasureSquareDefinitions.Result out child childOut domain codomain erasedType cutoff childGamma childExtended).relabel j =
 OriginalLambdaErasureSquareDefinitions.Result (out.relabel j) (child.relabel j) (childOut.relabel j)
   (domain.relabel j) (codomain.relabel j) (erasedType.relabel j) (cutoff.relabel j)
   (childGamma.relabel j) (childExtended.relabel j) := by
 simp only [OriginalLambdaErasureSquareDefinitions.Result,conjunctionRename,graph1Rename,graph3Rename,
   OriginalContextInsertionSyntaxProof.insertRename,sucRelabel]

theorem atPayloads (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended oldChildExtended context before after rawS rawT : OTerm alpha)
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
 (hlink : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter oldChildParam oldS oldT oldCert oldParam)))
 (ih : ContextChildIH body Delta (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context before after)
 (hpS : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.packedLambda oldS domain codomain rawS)))
 (hpT : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.packedLambda oldT domain codomain rawT))) :
 Nonempty (Derivation body Delta (Result (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) newS newT newParam oldS oldT before after)) := by
 apply namedSquare oldS newS domain codomain rawS oldBody erasedType cutoff gamma extended _ hpS
   (andRight (andRight (andRight (andRight hsf)))) hes hi
 intro beta j Theta childS childGamma childExtended hj hsq
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
 have hpT := renameInto hpT j Theta hj
 simp only [graph3Rename] at hpT
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have hlink := renameInto hlink j Theta hj
 simp only [graph4Rename] at hlink
 have ih := contextChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context before after j Theta hj ih
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
 let rawT := rawT.relabel j

 have hsame := valueUnique InternalListCodec.consCode oldChildExtended childExtended
   (Fin.cons domain (Fin.cons extended Fin.elim0)) hce (andRight (andRight hsq))
 have oldPair := OriginalFinalVariableObjectInternalSupportProof.secondTransport InternalPairing.pairing
   oldChildParam context oldChildExtended childExtended (by simpa only [equalEqn] using hsame) hocp
 apply namedSquare oldT newT domain codomain rawT oldTargetBody erasedType cutoff gamma extended _ hpT
   (andRight (andRight (andRight (andRight htf)))) het hi
 intro beta j Theta childT otherGamma otherExtended hj htq
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
 have hsq := renameInto hsq j Theta hj
 simp only [conjunctionRename, squareRename, graph2Rename] at hsq
 have oldPair := renameInto oldPair j Theta hj
 simp only [graph2Rename] at oldPair
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have hlink := renameInto hlink j Theta hj
 simp only [graph4Rename] at hlink
 have ih := contextChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context before after j Theta hj ih
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
 let childS := childS.relabel j
 let childGamma := childGamma.relabel j
 let childExtended := childExtended.relabel j

 apply programCases InternalPairing.pairing (Fin.cons context (Fin.cons childGamma Fin.elim0)) _
 intro beta j Theta childParam hj hcp
 rw [resultRename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hcp
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
 have hsq := renameInto hsq j Theta hj
 simp only [conjunctionRename, squareRename, graph2Rename] at hsq
 have oldPair := renameInto oldPair j Theta hj
 simp only [graph2Rename] at oldPair
 have htq := renameInto htq j Theta hj
 simp only [conjunctionRename, squareRename, graph2Rename] at htq
 have hstrip := renameInto hstrip j Theta hj
 simp only [graph1Rename] at hstrip
 have hlink := renameInto hlink j Theta hj
 simp only [graph4Rename] at hlink
 have ih := contextChildIHRename (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context before after j Theta hj ih
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
 let childS := childS.relabel j
 let childGamma := childGamma.relabel j
 let childExtended := childExtended.relabel j
 let childT := childT.relabel j
 let otherGamma := otherGamma.relabel j
 let otherExtended := otherExtended.relabel j

 exact OriginalLambdaErasureContextCaseChildrenProof.atChildren H G M W oldStep endpoint window
   oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam
   childS childT childParam domain codomain arrow erasedType cutoff gamma extended childGamma childExtended
   context before after hsf htf hs hc hi hes hop hnp (andLeft (andRight hsq)) (andRight (andRight hsq))
   oldPair hcp (andLeft hsq)
   (andIntro (andLeft (andLeft htq)) (andIntro (andLeft (andRight (andLeft htq)))
     (andLeft (andRight (andRight (andLeft htq)))))) hstrip hlink ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseSquaresProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseSquaresProof
