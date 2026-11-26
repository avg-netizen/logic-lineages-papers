module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def constant (k : Nat) : Program 3 :=
  match k with
  | 0 => InternalAcceptance.constantZero 3
  | k+1 => .composition .succ (fun _ : Fin 1 => constant k)
/-- Input order is exactly the numeric optional layer: [node,answers,window].
The answer list is never regenerated from a native decoded structure internally. -/
def rawSlot (k : Nat) : Program 3 :=
  .composition InternalRawListRecursion.lookup ![constant k,.projection 1]
def answer (k : Nat) : Program 3 :=
  LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (rawSlot k)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots
