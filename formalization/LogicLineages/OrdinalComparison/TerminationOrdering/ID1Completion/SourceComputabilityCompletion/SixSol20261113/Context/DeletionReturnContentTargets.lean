module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261112.Context

/-- The actual deletion selector recovers semantic deletion observations from
an operationally reversed observation-map of the original inherited deletion
jobs. The scalar-map identification is NOT a premise. The untouched old/child
stack remainder is arbitrary; no recursive runtime correctness is asserted. -/
def ActualDeletionReturn : Prop := ∀ (Q : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (packed typ raw parameter jobs inherited forwardRow deletionPrefix childCount deletionCount remainder results actualRow : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)) →
  Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs jobs raw parameter)) →
  Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) inherited jobs typ)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (ChildContentDefinitions.observationFromJob Q)) forwardRow inherited)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix forwardRow)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount deletionPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results deletionPrefix remainder)) →
  Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.deletionRow actualRow childCount deletionCount results)) →
  Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) actualRow packed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentTargets
