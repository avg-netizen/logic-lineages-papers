module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafTargets
open OriginalSpineGuardLeaf
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full-output equality on EVERY raw input under only the original leaf's
native calibration. Malformed contexts, failed source/target/certificate
decoding and rejected inputs remain included. No fixed window, closure,
successful parsing or additional bottom-spine premise is assumed. -/
def ActualOriginalSpineGuardLeafRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4),
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ v : List.Vector Nat 4, evaluate (refined oldStep) v = evaluate oldStep v

/-- Direct arithmetic factor recovery for the concrete conjunction, for
ANY original leaf. Both the old accepting graph and the literal spine-guard
graph are proved consequences; no calibration or leaf-law oracle is supplied. -/
def ActualOriginalSpineGuardLeafInternalCases : Prop :=
  ∀ oldStep : Program 4,
    OriginalConstructorLeaf.OriginalFactor oldStep (refined oldStep) ∧
      LeafHasSpineGuard (refined oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafTargets
