module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureSquaresProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalMixedClosedLambdaErasureDefinitions OriginalLambdaErasureCaseSupportProof
open OriginalExistentialRankResultDefinitions (Result)
open OriginalMixedExistentialCongruenceSupportProof (resultRename)
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalMixedClosedLambdaErasureSquaresProof (squareRename)
open OriginalMixedClosedLambdaErasureSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromFields (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended oldChildExtended context : OTerm alpha)
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldS domain codomain oldBody arrow)))
 (htf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldT domain codomain oldTargetBody arrow)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) oldS oldParam)))
 (hc : Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) oldBody oldTargetBody oldChildCert oldChildParam)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)))
 (het : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)))
 (hce : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode oldChildExtended domain extended)))
 (hocp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldChildParam context oldChildExtended)))
 (hstrip : Nonempty (Derivation body Delta (graph1 OriginalLambdaGuardLeaf.stripCertificate oldChildCert oldCert)))
 (hlink : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter oldChildParam oldS oldT oldCert oldParam)))
 (ih : ContextChildIH body Delta (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context)
 :
 Nonempty (Derivation body Delta (Result (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) newS newT newParam oldS oldT)) := by
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
 have hlink := renameInto hlink j Theta hj
 simp only [graph4Rename] at hlink
 have ih := contextChildIHRename (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context j Theta hj ih
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
 have hlink := renameInto hlink j Theta hj
 simp only [graph4Rename] at hlink
 have ih := contextChildIHRename (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context j Theta hj ih
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
 let rawS := rawS.relabel j

 exact OriginalMixedClosedLambdaErasureSquaresProof.atPayloads H G M W oldStep window
   oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam newS newT newParam domain codomain arrow erasedType cutoff gamma extended oldChildExtended context rawS rawT
   hsf htf hs hc hi hes het hop hnp hce hocp hstrip hlink ih hpS hpT


def prefixQueries : Fin 3 → Program 1 := ![InternalUnpair.left,InternalUnpair.right,
 InternalApplicationCertificateConstructors.consOf (InternalAcceptance.constantZero 1) InternalUnpair.left]

theorem actualAtFields : OriginalMixedClosedLambdaErasureTargets.ActualAtFields := by
 intro H G M W oldStep window body alpha Delta oldS oldT oldCert oldParam oldBody oldTargetBody oldChildCert oldChildParam
  domain codomain arrow context gamma extended oldChildExtended newS newT newParam erasedType cutoff hsf htf hh hparent hi hes het hnp ih
 have hchild : Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (numeral 1) oldBody oldTargetBody oldChildCert oldChildParam)) := by
  obtain ⟨law⟩ := OriginalTransparentMixedPathLambdaPrefixProof.hop
   (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentDirectBottom.refined (OriginalTransparentMixedDirectBottom.source H G M W) oldStep)
   oldS oldT oldCert oldParam oldBody oldTargetBody oldChildCert oldChildParam domain codomain context extended oldChildExtended (numeral 1) hh
  obtain ⟨hparent⟩ := hparent
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft law) hparent⟩
 apply InternalApplicationStepPeelSupportProof.queryCases prefixQueries (Fin.cons oldChildCert Fin.elim0) _
 intro beta j ys Theta hj hq
 rw [resultRename]
 simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hq
 have hsf' := renameInto hsf j Theta hj
 have htf' := renameInto htf j Theta hj
 rw [fieldsRename] at hsf' htf'
 have hh' := renameInto hh j Theta hj
 simp only [OriginalTransparentLambdaStep.LambdaHop,InternalRecursionGraphStepSyntaxProof.conjunctionRename,
  graph1Rename,graph2Rename,graph3Rename,InternalOriginalStepGuard.one,
  InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hh'
 have hchild' := renameInto hchild j Theta hj
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at hchild'
 have hi' := renameInto hi j Theta hj
 rw [OriginalContextInsertionSyntaxProof.insertRename] at hi'
 have hes' := renameInto hes j Theta hj
 have het' := renameInto het j Theta hj
 rw [graph3Rename] at hes' het'
 have hnp' := renameInto hnp j Theta hj
 rw [graph2Rename] at hnp'
 have ih' := contextChildIHRename (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
  (OriginalTransparentMixedDirectBottom.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context j Theta hj ih
 have hpref := andLeft (andRight (andRight (andRight (andRight (andRight hh')))))
 have hparam := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh'))))))
 have hext := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hh')))))))
 have hcp := andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hh')))))))
 have hcons := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalListCodec.consCode
  (InternalAcceptance.constantZero 1) InternalUnpair.left (ys 2) InternalTagArithmeticSyntaxProof.z (ys 0)
  (Fin.cons (oldChildCert.relabel j) Fin.elim0) (hq 2)
  (InternalAcceptanceConjunctionProof.constantZeroValue _) (hq 0)
 have hstrip := OriginalTransparentLambdaStepPrefixProof.stripPrefix (oldCert.relabel j) (oldChildCert.relabel j)
  (ys 2) (ys 0) (ys 1) hpref (hq 0) (hq 1) hcons
 have hlink := OriginalTransparentLambdaStepFieldsProof.selectors (oldS.relabel j) (oldT.relabel j)
  (oldCert.relabel j) (oldParam.relabel j) (oldBody.relabel j) (oldTargetBody.relabel j)
  (oldChildCert.relabel j) (oldChildParam.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j)
  (context.relabel j) (extended.relabel j) (oldChildExtended.relabel j) hsf' htf' hstrip hparam hext hcp (3 : Fin 4)
 exact fromFields H G M W oldStep window (oldS.relabel j) (oldT.relabel j) (oldCert.relabel j)
  (oldBody.relabel j) (oldTargetBody.relabel j) (oldChildCert.relabel j) (oldParam.relabel j) (oldChildParam.relabel j)
  (newS.relabel j) (newT.relabel j) (newParam.relabel j) (domain.relabel j) (codomain.relabel j) (arrow.relabel j)
  (erasedType.relabel j) (cutoff.relabel j) (gamma.relabel j) (extended.relabel j) (oldChildExtended.relabel j) (context.relabel j)
  hsf' htf' (andLeft hh') hchild' hi' hes' het' hparam hnp' hext hcp hstrip hlink ih'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedLambdaErasureProof
