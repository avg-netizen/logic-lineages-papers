module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
open OriginalHereditarySettledObserverDefinitions OriginalHereditarySettledObserverTargets
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteObserver OriginalHereditaryFiniteStability

theorem unfolding : Unfolding := by
 intro R n arity c s
 have hs := OriginalHereditaryFiniteStabilityProof.stable R n arity c s (weight s) (Nat.le_refl _)
 unfold settledValue
 rw [← hs]
 change value (OriginalHereditaryObservationLayer.layer R (family R (weight s))) c s = _
 exact OriginalHereditaryObservationLayerNativeProof.native R (family R (weight s)) _

theorem stepNormalization : StepNormalization := by
 intro R n arity c s t h
 exact OriginalHereditaryFiniteStabilityProof.settled R n arity c t (weight s)
   (Nat.le_of_lt (OriginalHereditaryNativeBoundProof.stepWeight h))

theorem uniformity : Uniformity := by
 intro R n arity symbols S c hS hR Gamma q r hq hr h
 exact OriginalHereditaryFiniteObserverProof.selectedDepth R n arity symbols S c hS hR Gamma q r hq hr h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
