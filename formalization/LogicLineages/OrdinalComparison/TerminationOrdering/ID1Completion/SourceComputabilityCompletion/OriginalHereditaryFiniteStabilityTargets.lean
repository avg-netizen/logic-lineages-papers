module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteObserver OriginalHereditaryFiniteStability
/-- One semantic layer depends only on genuinely smaller child/deletion states. -/
def LocalDependency : Prop := ∀ (R Q T : Program 2) n (arity : Fin n → Nat) c (s : State (Fin n) arity),
 StepAgreement Q T c s → value (OriginalHereditaryObservationLayer.layer R Q) c s =
   value (OriginalHereditaryObservationLayer.layer R T) c s
/-- Stabilization at the proven semantic weight. No source-class uniformity,
calibration, or runtime-evaluator correctness is assumed or asserted. -/
def Stable : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c (s : State (Fin n) arity) depth,
 weight s ≤ depth → value (family R (depth+1)) c s = value (family R depth) c s
/-- Any greater semantic depth agrees with the actual weight-selected depth. -/
def Settled : Prop := ∀ (R : Program 2) n (arity : Fin n → Nat) c (s : State (Fin n) arity) depth,
 weight s ≤ depth → value (family R depth) c s = value (family R (weight s)) c s
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityTargets
