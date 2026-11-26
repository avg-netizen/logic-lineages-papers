module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualScopedChildren : OriginalLambdaErasureScopedChildrenTargets.ActualScopedChildren := by
 intro body alpha Delta H G M W oldStep endpoint window
  oldS oldT oldCert oldBody oldTargetBody oldChildCert oldParam oldChildParam
  newS newT newParam childS childT childParam domain codomain arrow
  erasedType cutoff gamma extended childGamma childExtended context before after
  hsf htf hs hc hi hes hop hnp hcg hce hocp hncp hcs hct hstrip supplier
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
 apply OriginalLambdaOriginalRankDichotomyProof.actualLocalRankedCongruence
   source oldStep endpoint window body alpha Delta newS newT newParam childS childT childParam
   domain codomain context gamma childGamma oldS oldT oldBody oldTargetBody before after frame
   (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction oldS domain codomain oldBody arrow hsf)
   (OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction oldT domain codomain oldTargetBody arrow htf)
 exact supplier

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureScopedChildrenProof
