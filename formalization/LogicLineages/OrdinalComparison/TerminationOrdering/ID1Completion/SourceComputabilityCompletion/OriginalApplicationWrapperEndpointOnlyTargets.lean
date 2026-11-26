module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedPathInternalDefinitions
/-- Conditional supporting law, NOT an endpoint-discharge or final transport theorem.
The literal endpoint remains explicit; parent spine is derived from the child spine. No recognizer changes. -/
def ActualEndpointIntroduction : Prop := ∀ (source : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1), OriginalGenericApplicationWrapperTargets.RawIntroduction source oldStep →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha),
 Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph endpoint
  InternalOriginalStepGuard.one d e childS childT arg parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep)
  InternalOriginalStepGuard.one childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep)
  InternalOriginalStepGuard.one s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationWrapperEndpointOnlyTargets
