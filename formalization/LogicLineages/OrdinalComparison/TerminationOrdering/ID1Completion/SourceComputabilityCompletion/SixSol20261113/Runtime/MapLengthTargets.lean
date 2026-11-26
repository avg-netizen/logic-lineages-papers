module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermTickMapLengthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Unary original list-map preserves arbitrary internally quantified length,
without source admission, standard-count restriction, or a cell-value premise. -/
def ActualMapLength : Prop := ∀ (F : Program 1) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (count input output : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count input)) →
 Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) output input)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count output))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthTargets
