module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion
/-- The actual raw deletion-row lookup, copied into an annotated child, strictly
reduces the unchanged fuel weight. Raw-job coordinates are literal graph witnesses. -/
def ActualDecrease : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent child parentRawJob childRawJob raw parameter row count cutoff W V : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRawJob parent)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget childRawJob child)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter)) →
 Nonempty (Derivation body Delta (lengthGraph count row)) →
 Nonempty (Derivation body Delta (Below cutoff count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup childRawJob cutoff row)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightTargets
