module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Dynamic length and actual append suffice. No supplied selector outputs and
no native reflection; all encoded lists are symbolic internal terms. -/
def ActualPartition : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
 (Delta : List (Formula alpha)) (count initialList suffix joined : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count initialList)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined initialList suffix)) →
 Nonempty (Derivation body Delta
   (graph2 OriginalClassContextAllPositionObserver.front initialList count joined ⊓
    graph2 InternalRawListRecursion.drop suffix count joined))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
