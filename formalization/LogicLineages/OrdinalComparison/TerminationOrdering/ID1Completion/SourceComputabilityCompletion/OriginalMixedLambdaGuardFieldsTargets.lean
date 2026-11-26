module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual lambda guard and source-derived Fields reconstruct genuine target Fields and original prefix Hop. Only actual selectors/context coordinates are supplied, never target typing or child acceptance. -/
def ActualAtFields : Prop := ∀ (source : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter childS childT childCert childParam d e arrow context gamma extended : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e childS arrow)) →
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentLambdaStep.hopGuard source) (numeral 1) s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.targetBody childT s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter childParam s t cert parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)) →
 Nonempty (Derivation body Delta
  (OriginalLambdaConstructor.Fields t d e childT arrow ⊓
   OriginalTransparentLambdaStep.LambdaHop source s t cert parameter childS childT childCert childParam d e context gamma extended))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaGuardFieldsTargets
