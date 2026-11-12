module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTransparentLambdaStep
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/- Supporting proof interface only: the raw introduction supplier is explicit. -/
def RawIntroduction (source : Program 2) (oldStep : Program 4) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert childParam d e context gamma extended : InternalGraphComposition.OTerm alpha),
 Nonempty (Derivation body Delta (LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended)) →
 Nonempty (Derivation body Delta (graph4 oldStep InternalOriginalStepGuard.one childS childT childCert childParam)) →
 Nonempty (Derivation body Delta (graph4 oldStep InternalOriginalStepGuard.one s t cert parameter))

def ActualIntroduction : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (rawIntroduction : RawIntroduction source oldStep)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter childS childT childCert childParam d e context gamma extended : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window oldStep
  Nonempty (Derivation body Delta
    ((LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
      graph4 leaf InternalOriginalStepGuard.one childS childT childCert childParam).imp
      (graph4 leaf InternalOriginalStepGuard.one s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGenericLambdaWrapperTargets
