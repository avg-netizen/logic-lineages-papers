module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedPathInternalDefinitions
def RawIntroduction (source : Program 2) (oldStep : Program 4) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha),
 Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (graph4 oldStep InternalOriginalStepGuard.one childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 oldStep InternalOriginalStepGuard.one s t cert parameter))
/-- Conditional supporting law, NOT an endpoint-discharge or final transport theorem.
The literal endpoint and parent spine graphs remain explicit obligations. No recognizer changes. -/
def ActualIntroduction : Prop := ∀ (source : Program 2) (oldStep : Program 4)
 (endpoint : Program 6) (window : Program 1), RawIntroduction source oldStep →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha),
 Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)) →
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph endpoint
  InternalOriginalStepGuard.one d e childS childT arg parameter)) →
 Nonempty (Derivation body Delta (graph4
  (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  InternalOriginalStepGuard.one s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep)
  InternalOriginalStepGuard.one childS childT childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep)
  InternalOriginalStepGuard.one s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericApplicationWrapperTargets
