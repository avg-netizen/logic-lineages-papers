module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Complete actual map composition through the literal inherited job shell.
Q and the real parent type are fixed across the entire unchanged ordered row.
No supplied pointwise agreement, map-fusion law or runtime invariant. -/
def ActualScalarFusion : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (jobs typ annotated row : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) annotated jobs typ)) →
  Nonempty (Derivation body Delta
    ((graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) row annotated).iff
      (graph2 (InternalListMap.map (k := 1) (DeletionMapDefinitions.rawScalarFromJob Q)) row jobs typ)))
/-- The actual inherited annotated deletion-job scalar map computes the SAME
unchanged hereditary row at the original packed type/raw and parameter. The
whole original annotation-scan suffix identification remains a separate source
obligation; no such identification is assumed as a semantic premise here. -/
def ActualInheritedDeletionRow : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (input typ raw parameter jobs annotated row : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)) →
  Nonempty (Derivation body Delta
    (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) annotated jobs typ)) →
  Nonempty (Derivation body Delta
    ((graph1 (InternalListMap.map (k := 0) (ScheduledDeletionDefinitions.scalarFromJob Q)) row annotated).iff
      (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
