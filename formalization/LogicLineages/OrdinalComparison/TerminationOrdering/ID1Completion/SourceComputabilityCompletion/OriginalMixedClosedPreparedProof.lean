module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPreparedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedPreparedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPreparedProof
open UniformCertificateCompletion OriginalMixedClosedPrepared
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem closedTrace (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : ClosedTrace p H G W := by
 exact OriginalMixedClosedTraceTransportProof.actualRestrictedTransport H G (OriginalMixedPrepared.member p) W p.oldStep
  (OriginalMixedPrepared.prepared p H G W).window

theorem actualRetention : OriginalMixedClosedPreparedTargets.ActualRetention := by
 intro n arity p H G W P hp hH hG hW hP
 exact ⟨OriginalMixedPreparedProof.actualRetention n arity p H G W P hp hH hG hW hP,closedTrace p H G W⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPreparedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedPreparedProof
