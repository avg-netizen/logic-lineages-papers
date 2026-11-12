module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaErasureCaseDefinitions
open OriginalLambdaOriginalRankDefinitions (Result)
open OriginalLambdaErasureSquareDichotomyDefinitions (Frame)
open InternalTagArithmeticSyntaxProof (suc)

/-- Coordinate-level local adapter only. The supplier concerns precisely the
actual recovered child edge, whose old certificate is the actual strip of the
parent certificate. It is an explicit local IH, not all-child certificate
closure, a recognizer of desired outcomes, or a completed chain theorem. -/
def ActualScopedChildren : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)), ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
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
 (hstrip : Nonempty (Derivation body Delta
   (graph1 OriginalLambdaGuardLeaf.stripCertificate oldChildCert oldCert)))
 (supplier : OriginalLambdaOriginalRankDefinitions.ChildSupplier
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep)) body Delta childS childT childParam
   oldBody oldTargetBody before after),
 Nonempty (Derivation body Delta (Result
   (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
     (OriginalTransparentLambdaStep.refined (OriginalUniverseDecoder.source H G M W) oldStep))
   newS newT newParam oldS oldT before after))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenTargets
