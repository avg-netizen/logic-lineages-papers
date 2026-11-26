module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
/-- Internal zero-accumulator correspondence to the unchanged original reverse. -/
def ZeroCorrespondence : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (raw out : OTerm alpha),
 Nonempty (Derivation body [] ((graph2 accumulated out raw z).iff
   (graph1 OriginalTypedArgumentObservations.reverse out raw)))
/-- Same arbitrary initial accumulator in both actual runs. All graph
arguments, numeric lists and observations remain object-language terms. -/
def AppendSingleton : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (front value singleton combined acc left right : OTerm alpha),
 Nonempty (Derivation body [] ((fields front value singleton combined acc left right).imp
 (graph2 InternalListCodec.consCode right value left)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorTargets
