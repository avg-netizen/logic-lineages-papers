module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionSelectorContentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof (symm)
open SixSol20261112.Context

theorem actual : DeletionReturnContentTargets.ActualDeletionReturn := by
  intro Q body alpha Delta packed typ raw parameter jobs inherited forwardRow deletionPrefix childCount deletionCount remainder results actualRow hp hj hi hm hr hl ha hs
  have hraw := InheritedObservationProof.forward Q jobs typ inherited forwardRow hi hm
  have hiff := DeletionMapProof.actualOrderedMap Q body alpha Delta packed typ raw parameter jobs forwardRow hp hj
  obtain ⟨hiff⟩ := hiff
  obtain ⟨hraw⟩ := hraw
  have hrow := Derivation.implicationElimination (Derivation.conjunctionLeft hiff) hraw
  obtain ⟨he⟩ := DeletionSelectorContentProof.actual forwardRow deletionPrefix childCount deletionCount remainder results actualRow hr hl ha hs
  exact outputTransport (OriginalHereditaryDeletionRows.rows Q) forwardRow actualRow
    (Fin.cons packed (Fin.cons parameter Fin.elim0)) ⟨symm he⟩ ⟨hrow⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionReturnContentProof
