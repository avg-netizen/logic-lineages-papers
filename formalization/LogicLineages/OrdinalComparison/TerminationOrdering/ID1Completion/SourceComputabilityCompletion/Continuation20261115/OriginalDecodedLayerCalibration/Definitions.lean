module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- The input answer list is deliberately ignored by the exact original decoder guard. -/
def nodeAccepted (n : Nat) : Program 3 :=
  .composition (OriginalDecodedDependencies.accepted n) ![.projection 0,.projection 2]
def windowAccepted (n : Nat) : Program 3 :=
  .composition (OriginalDecodedWindowValidity.window n) (fun _ : Fin 1 => .projection 2)
def guard (n : Nat) : Program 3 :=
  InternalAcceptance.conjunction (nodeAccepted n) (windowAccepted n)
/-- Existing concrete field/answer-slot AST, now at a fully specified guard.
No opaque field supplier is introduced. Invalid input remains Some0 = 1. -/
def layer (n : Nat) (arity : Fin n → Nat) : Program 3 :=
  ConcreteHeadMoveLayer.layer n arity (guard n)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration
