module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace
/-- The actual original stripped certificate has the literal parent path tail;
therefore a successful tail run is recognition at the same actual child tuple. -/
def ActualChildRun : Prop := ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter code tail childS childT childCert childParam next out : OTerm alpha),
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.path code s t cert parameter)) →
 Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code)) →
 Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam)) →
 Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)) →
 Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out)) →
 Nonempty (Derivation body Delta
  (graph1 InternalUnpair.left tail childCert ⊓
   graph4 (recognizes source leaf) (suc z) childS childT childCert childParam))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunTargets
