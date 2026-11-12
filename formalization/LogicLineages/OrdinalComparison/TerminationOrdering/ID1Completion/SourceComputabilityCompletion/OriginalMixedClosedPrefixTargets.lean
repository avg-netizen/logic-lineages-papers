module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedPathInternalDefinitions OriginalTransparentLambdaStep
def ActualLambda : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentMixedPathDefinitions.refined source oldStep)
  Nonempty (Derivation body Delta
    ((LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
      graph4 leaf InternalOriginalStepGuard.one childS childT childCert childParam).imp
      (graph4 leaf InternalOriginalStepGuard.one s t cert parameter)))

def ActualApplication : Prop := ∀ (source : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1),
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha),
 Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph endpoint
  InternalOriginalStepGuard.one d e childS childT arg parameter)) →
 Nonempty (Derivation body Delta (graph4
  (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  InternalOriginalStepGuard.one s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentMixedPathDefinitions.refined source oldStep))
  InternalOriginalStepGuard.one childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (OriginalTransparentMixedPathDefinitions.refined source oldStep))
  InternalOriginalStepGuard.one s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPrefixTargets
