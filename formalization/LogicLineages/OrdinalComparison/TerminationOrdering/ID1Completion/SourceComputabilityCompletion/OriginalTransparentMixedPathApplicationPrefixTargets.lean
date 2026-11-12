module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine application-function prefix alone; all path/live coordinate witnesses are queried internally. SAME mixed refined Program, arbitrary output, no global retention claim. -/
def ActualApplicationPrefix : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert arg d e arrow out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalTransparentMixedPathInternalDefinitions.ApplicationHop source s t cert parameter childS childT childCert arg d e arrow).imp
      ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
        (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert parameter))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixTargets
