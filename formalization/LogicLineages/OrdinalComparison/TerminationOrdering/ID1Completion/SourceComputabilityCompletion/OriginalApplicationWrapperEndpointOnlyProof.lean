module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryLambdaGlobal
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem wrapperSpine (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
 (s t cert parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph4 (wrapper endpoint window oldStep) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have hn := andLeft (conjunctionRecover
  (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
  (InternalAcceptance.conjunction (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
   OriginalConstructorLeaf.variableGuard) xs h)
 have hs := andLeft (conjunctionRecover (OriginalSpineGuardLeaf.refined oldStep)
  (OriginalNeutralLeaf.leafGuard endpoint window) xs hn)
 exact andRight (conjunctionRecover oldStep
  (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure) xs hs)

theorem actualEndpointIntroduction : OriginalApplicationWrapperEndpointOnlyTargets.ActualEndpointIntroduction := by
 intro source oldStep endpoint window hraw body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hend hchild
 have hsp := wrapperSpine endpoint window (OriginalHereditaryLambda.refined (wrapper endpoint window oldStep))
  childS childT childCert parameter hchild
 have hp := OriginalApplicationSpinePrefixProof.actualSpinePrefix body alpha Delta s t cert childCert parameter
  childS childT arg d e arrow
  (andLeft (andRight (andRight (andRight hh))))
  (andLeft (andRight (andRight (andRight (andRight hh)))))
  (andLeft (andRight (andRight (andRight (andRight (andRight hh))))))
  (andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh)))))))
  (andLeft (andRight hh)) (andLeft (andRight (andRight hh))) hsp
 exact OriginalGenericApplicationWrapperProof.actualIntroduction source oldStep endpoint window hraw
  body alpha Delta s t cert parameter childS childT childCert arg d e arrow hh hend hp hchild
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyProof
