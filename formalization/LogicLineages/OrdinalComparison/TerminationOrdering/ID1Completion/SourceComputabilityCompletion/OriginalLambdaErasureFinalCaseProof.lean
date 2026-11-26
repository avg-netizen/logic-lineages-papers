module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalTransparentDirectBottomGlobal
open OriginalLambdaErasureFinalCaseTargets

theorem actualOriginalLambdaErasureFinalCase : ActualOriginalLambdaErasureFinalCase := by
 intro p H G W P body alpha Delta oldS oldT oldCert oldParam newS newT newParam oldBody
   domain codomain arrow erasedType cutoff gamma extended context before after
 dsimp only
 rw [OriginalTransparentDirectBottomGlobalInternalProof.finalLeaf p H G W P]
 exact OriginalLambdaErasureCaseProof.actualOriginalLambdaErasureCase H G
   (InternalOriginalUniformContextMembership.contextMember p.base.member) W
   (OriginalHereditaryLambdaGlobal.priorFinal (initial p H G W)).oldStep
   (OriginalHereditaryLambdaGlobal.endpoint (OriginalLambdaTraversalSelection.prepareInputs
     (OriginalTransparentLambdaStepGlobal.refined (initial p H G W) H G W P)))
   (OriginalTransparentLambdaStepGlobal.refined (initial p H G W) H G W P).window
   body alpha Delta oldS oldT oldCert oldParam newS newT newParam oldBody
   domain codomain arrow erasedType cutoff gamma extended context before after

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseProof
