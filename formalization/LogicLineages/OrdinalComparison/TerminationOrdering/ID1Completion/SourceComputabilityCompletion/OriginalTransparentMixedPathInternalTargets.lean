module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedPathInternalDefinitions
/-- Genuine lambda geometry and actual state encodings, no guard-success or
transition premise. This is a single step, not a global leaf package. -/
def ActualLambdaHop : Prop := ∀ (source : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert childParam d e context gamma extended state next : OTerm alpha),
 Nonempty (Derivation body Delta
  ((OriginalTransparentLambdaStep.LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended ⊓
   (graph4 OriginalHereditaryLambda.live state s t cert parameter ⊓
    graph4 OriginalHereditaryLambda.live next childS childT childCert childParam)).imp
   (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)))
/-- Genuine application-function geometry. Lambda rejection is proved from
actual application shape, not added as a premise. Child parameter is unchanged. -/
def ActualApplicationHop : Prop := ∀ (source : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert arg d e arrow state next : OTerm alpha),
 Nonempty (Derivation body Delta
  ((ApplicationHop source s t cert parameter childS childT childCert arg d e arrow ⊓
   (graph4 OriginalHereditaryLambda.live state s t cert parameter ⊓
    graph4 OriginalHereditaryLambda.live next childS childT childCert parameter)).imp
   (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
