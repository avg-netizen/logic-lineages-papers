module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine lambda prefix alone; all path/live coordinate witnesses are queried internally. SAME mixed refined Program, arbitrary output, no global retention claim. -/
def ActualLambdaPrefix : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended).imp
      ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
        (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert childParam))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixTargets
