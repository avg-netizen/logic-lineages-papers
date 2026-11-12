module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The WHOLE same effective closed leaf occurs at child and parent: both
existing spine/neutral/constructor wrapper layers and the intervening original
hereditary guard. Parent raw source membership, actual matching constructors,
body types, exact prefix, and actual context extension are literal graph
premises. No parent oldStep acceptance or guard success is assumed. This is
not a full positive certificate, canonical quotient lift or erasure dichotomy. -/
def ActualOriginalTransparentLambdaClosedLeafIntroduction : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window (refined source oldStep)
  Nonempty (Derivation body Delta
    ((LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
      graph4 leaf InternalOriginalStepGuard.one childS childT childCert childParam).imp
      (graph4 leaf InternalOriginalStepGuard.one s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperTargets
