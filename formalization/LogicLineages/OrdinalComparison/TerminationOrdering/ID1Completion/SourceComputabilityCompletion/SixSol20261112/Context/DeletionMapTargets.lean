module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Genuine actual list-map/append fusion. The shared map parameter remains
an arbitrary internal arithmetic term. No map law or output equality premise. -/
def MapAppend : Prop := ∀ (F : Program 2) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (left right joined parameter mappedLeft mappedRight out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) F) mappedLeft left parameter)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) F) mappedRight right parameter)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mappedLeft mappedRight)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) F) out joined parameter))

/-- The whole ordered actual deletion-job map, not a supplied cell law or
native map calibration. The original packed type, raw term and parameter are
retained; all context lengths and per-cutoff witnesses must be internal.
No source validity, covariance, execution invariant or fixed-point premise. -/
def ActualOrderedMap : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw parameter jobs row : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)) →
  Nonempty (Derivation body Delta
    ((graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) row jobs typ).iff
      (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
