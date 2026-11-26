module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (suc z)
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open UniformCertificateCompletion
open OriginalHereditaryLambdaGlobal

theorem closedFactor (endpoint : Program 6) (window : Program 1) (step : Program 4)
 (s t cert parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph4 (closedLeaf endpoint window step) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 step (suc z) s t cert parameter)) := by
 let inner := wrapper endpoint window step
 have hh := OriginalHereditaryLambdaGlobalInternalProof.wrapperFactor endpoint window (OriginalHereditaryLambda.refined inner) s t cert parameter h
 have hi := conjunctionRecover inner (OriginalHereditaryLambda.guard inner) ![s,t,cert,parameter] hh
 exact OriginalHereditaryLambdaGlobalInternalProof.wrapperFactor endpoint window step s t cert parameter (andLeft hi)

theorem initialAcceptance (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (s t cert parameter : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (h : Nonempty (Derivation body Delta (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentDirectBottom.refined (OriginalTransparentDirectBottomGlobal.source p H G W) p.oldStep) (suc z) s t cert parameter)) := by
 let b := OriginalTransparentDirectBottomGlobal.initial p H G W
 let r := OriginalTransparentLambdaStepGlobal.refined b H G W P
 let E := endpoint (OriginalLambdaTraversalSelection.prepareInputs r)
 rw [OriginalTransparentDirectBottomGlobalInternalProof.finalLeaf] at h
 have hn := closedFactor E r.window
  (OriginalTransparentLambdaStep.refined (OriginalTransparentDirectBottomGlobal.source p H G W) (priorFinal b).oldStep) s t cert parameter h
 have hpath := OriginalTransparentVariableStepHereditaryProof.certificatePath s cert hc
 have hp := OriginalTransparentLambdaStepNilNormalizationProof.elimination (OriginalTransparentDirectBottomGlobal.source p H G W) (priorFinal b).oldStep (suc z) s t cert parameter hpath hn
 rw [(OriginalHereditaryLambdaGlobalPreparationProof.pipelineIdentities b).1] at hp
 exact OriginalHereditaryLambdaGlobalInternalProof.wrapperFactor (endpoint b) b.window b.oldStep s t cert parameter hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroLeafProof
