module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open ScheduledDeletionSupportProof
open OriginalInternalJobDeletionLookupProof (bumpRename)
attribute [local irreducible] programGraph InternalPairing.pairing

theorem actualCell : ScheduledDeletionTargets.ActualCell := by
  intro Q arity body alpha Delta input typ raw parameter jobs count cutoff rawCell annotated value
    hi hjobs hcount hbound hlookup harity hdecor hv
  apply OriginalHereditaryInternalDeletionLookupProof.actualLookup body alpha Delta
    raw parameter jobs count cutoff rawCell _ hjobs hcount hbound hlookup
  intro beta j Theta window gamma erasedType deleted erased childParameter hTheta hp hlen hb hl hd he hcp hc
  simp only [graph3Rename]
  have hi := renameInto hi j Theta hTheta
  have harity := renameInto harity j Theta hTheta
  have hdecor := renameInto hdecor j Theta hTheta
  have hv := renameInto hv j Theta hTheta
  simp only [graph1Rename,graph2Rename,graph5Rename,bumpRename,
    GuardedSourceSyntaxProof.numeralRename] at hi harity hdecor hv
  exact ScheduledDeletionCoordinatesProof.atErasure Q arity
    (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j)
    (cutoff.relabel j) (rawCell.relabel j) (annotated.relabel j) (value.relabel j)
    window gamma erasedType deleted erased childParameter hi hp hl hd he hcp hc harity hdecor hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ScheduledDeletionProof.actualCell
