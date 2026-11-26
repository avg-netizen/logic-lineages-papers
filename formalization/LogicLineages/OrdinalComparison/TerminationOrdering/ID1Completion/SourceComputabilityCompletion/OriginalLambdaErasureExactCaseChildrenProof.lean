module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaErasureExactCaseDefinitions
open OriginalLambdaOriginalRankDefinitions (Result)
open OriginalLambdaErasureSquareDichotomyDefinitions (Frame)
open InternalTagArithmeticSyntaxProof (suc)
open OriginalLambdaErasureExactCaseSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Assembly at actual named children. Every displayed coordinate is an
actual graph, later supplied by geometry and the two query squares. Parent
and child source acceptance are DERIVED from the original decoder, never from
leaf acceptance. The only induction assumption is the frozen ChildIH. -/
theorem atChildren (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1)
 (oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam
  newS newT newParam childS childT childParam domain codomain arrow
  erasedType cutoff gamma extended childGamma childExtended context before after : OTerm alpha)
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldS domain codomain oldBody arrow)))
 (htf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldT domain codomain oldTargetBody arrow)))
 (hs : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) oldS oldParam)))
 (hc : Nonempty (Derivation body Delta
   (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
     (numeral 1) oldBody oldTargetBody oldChildCert oldChildParam)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)))
 (hce : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childExtended domain extended)))
 (hocp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldChildParam context childExtended)))
 (hncp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context childGamma)))
 (hcs : Nonempty (Derivation body Delta
   (OriginalLambdaErasureSquareDefinitions.Result newS oldBody childS domain codomain erasedType cutoff childGamma childExtended)))
 (hct : Nonempty (Derivation body Delta
   (graph3 OriginalLambdaConstructor.constructor newT domain codomain childT ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw childT erasedType (suc cutoff) oldTargetBody ⊓
     graph1 InternalUnpair.left codomain childT))))
 (hstrip : Nonempty (Derivation body Delta (graph1 OriginalLambdaGuardLeaf.stripCertificate oldChildCert oldCert)))
 (hlink : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter oldChildParam oldS oldT oldCert oldParam)))
 (ih : ExactChildIH body
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   (OriginalUniverseDecoder.source H G M W) oldS oldT oldCert oldParam codomain erasedType cutoff context before after) :
 Nonempty (Derivation body Delta (Result
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   newS newT newParam oldS oldT before after)) := by
 let source := OriginalUniverseDecoder.source H G M W
 let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
   (OriginalTransparentLambdaStep.refined source oldStep)
 have holdChild := OriginalPackedSourceLambdaChildProof.sourceChild H G M W
   oldS oldParam oldBody domain codomain arrow context extended childExtended oldChildParam
   hsf hs hop hce hocp
 have hnewSource := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure
   body alpha Delta H G M W oldS newS erasedType cutoff gamma extended context oldParam newParam
   hi hes hop hnp hs
 have frame : Nonempty (Derivation body Delta
   (Frame source newS newT newParam childS childT childParam domain codomain context gamma childGamma)) :=
   andIntro hnewSource (andIntro (andLeft hcs) (andIntro (andLeft hct)
    (andIntro (andLeft (andRight (andRight hcs))) (andIntro (andRight (andRight hct))
     (andIntro hnp (andIntro hcg hncp))))))
 have supplier := ih alpha id Delta oldBody oldTargetBody oldChildCert oldChildParam
   childS childT childParam childGamma childExtended
   (by simpa only [Term.relabel_id] using andRight (andRight (andRight (andRight hsf))))
   (by simpa only [Term.relabel_id] using andRight (andRight (andRight (andRight htf))))
   holdChild hc
   (by simpa only [Term.relabel_id] using hocp)
   (by simpa only [Term.relabel_id] using hncp)
   (by simpa only [Term.relabel_id] using andRight (andRight (andRight hcs)))
   (by simpa only [Term.relabel_id] using andLeft (andRight hcs))
   (by simpa only [Term.relabel_id] using andLeft (andRight hct))
   (by simpa only [Term.relabel_id] using hstrip)
   (by simpa only [Term.relabel_id] using hlink)
 apply OriginalLambdaOriginalRankDichotomyProof.actualLocalRankedCongruence
   source oldStep endpoint window body alpha Delta newS newT newParam childS childT childParam
   domain codomain context gamma childGamma oldS oldT oldBody oldTargetBody before after frame
   (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction oldS domain codomain oldBody arrow hsf)
   (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction oldT domain codomain oldTargetBody arrow htf)
 simpa only [Term.relabel_id] using supplier

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseChildrenProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureExactCaseChildrenProof
