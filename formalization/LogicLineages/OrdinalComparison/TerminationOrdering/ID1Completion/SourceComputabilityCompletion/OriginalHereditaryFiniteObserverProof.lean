module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverProof
open OriginalHereditaryFiniteObserver OriginalHereditaryFiniteObserverTargets

theorem allDepths : AllDepths := by
 intro R n arity symbols S c hS hR depth
 induction depth with
 | zero => exact hR
 | succ depth ih =>
   exact OriginalHereditaryObservationLayerNativeProof.sourcePreservation R (family R depth) n arity symbols S c hS hR ih

theorem calibratedDepths : CalibratedDepths := by
 intro n arity data hd c ctx hctx hS depth
 exact allDepths data.oldRepresentative n arity ctx.1.1 ctx.1.2 c hS
   (OriginalHereditaryObservationSourceRootProof.calibratedRepresentative n arity data hd c ctx hctx hS) depth

theorem selectedDepth : SelectedDepth := by
 intro R n arity symbols S c hS hR Gamma q r hq hr h
 have hp := NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity symbols S Gamma q r h
 have hs := NumberedPrimaryEquivalenceProof.primarySizePreservation (Fin n) arity Gamma q r hp
 rw [hs]
 exact allDepths R n arity symbols S c hS hR _ Gamma q r hq hr h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverProof
