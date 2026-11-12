module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Actual bounded lookup in the literal annotated expansion decreases the actual
fuel weight. All raw numeric jobs are allowed. No source calibration, typedness,
child-decrease supplier, or runtime completion premise is supplied. -/
def ActualLookupDecrease : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (parent jobs count index child W V : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count jobs)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child)) →
 Nonempty (Derivation body Delta (InternalOriginalOrderSyntaxProof.ltF V W))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
