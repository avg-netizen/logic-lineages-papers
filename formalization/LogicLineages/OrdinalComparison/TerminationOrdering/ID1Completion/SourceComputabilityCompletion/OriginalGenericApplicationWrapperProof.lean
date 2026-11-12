module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperGuardsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalHereditaryLambdaGlobal
open OriginalHereditaryLambdaGlobalInternalProof (wrapperFactor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem wrapperIntroduction (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
 (s t cert parameter : OTerm alpha)
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (suc (suc z)) s)))
 (hg : Nonempty (Derivation body Delta (graph4 (OriginalNeutralLeaf.guardAt endpoint) (suc z) s t cert parameter)))
 (hsp : Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) (suc z) s t cert parameter)))
 (hold : Nonempty (Derivation body Delta (graph4 oldStep (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (wrapper endpoint window oldStep) (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hg := OriginalApplicationWrapperGuardsProof.guards endpoint window s t cert parameter htag hg
 have hspine := conjunctionAccept oldStep
  (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hold hsp
 have hn := conjunctionAccept (OriginalSpineGuardLeaf.refined oldStep)
  (OriginalNeutralLeaf.leafGuard endpoint window) xs hspine (andLeft hg)
 exact conjunctionAccept (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
  (InternalAcceptance.conjunction
   (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
   OriginalConstructorLeaf.variableGuard) xs hn (andRight hg)

theorem actualIntroduction : OriginalGenericApplicationWrapperTargets.ActualIntroduction := by
 intro source oldStep endpoint window hraw body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hend hsp hchild
 have hlinks := OriginalTransparentMixedPathApplicationFieldsProof.applicationFields source s t cert parameter
  childS childT childCert arg d e arrow hh
 have htag := andLeft hlinks
 have hg := OriginalApplicationWrapperGuardAtProof.guardAt source endpoint s t cert parameter
  childS childT childCert arg d e arrow hh hend
 let inner := wrapper endpoint window oldStep
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,parameter]
 have hch := wrapperFactor endpoint window (OriginalHereditaryLambda.refined inner) childS childT childCert parameter hchild
 have hci := andLeft (conjunctionRecover inner (OriginalHereditaryLambda.guard inner) ys hch)
 have hcr := wrapperFactor endpoint window oldStep childS childT childCert parameter hci
 have hparent := hraw body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hcr
 have hpi := wrapperIntroduction endpoint window oldStep s t cert parameter htag hg hsp hparent
 have hstop := OriginalApplicationWrapperGuardsProof.stopAtApplication s t cert parameter htag
 have hguard := OriginalHereditaryLambdaStoppedProof.stoppedGuard inner body alpha Delta s t cert parameter hstop
 have hhered := conjunctionAccept inner (OriginalHereditaryLambda.guard inner) xs hpi hguard
 exact wrapperIntroduction endpoint window (OriginalHereditaryLambda.refined inner) s t cert parameter htag hg hsp hhered
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperProof
