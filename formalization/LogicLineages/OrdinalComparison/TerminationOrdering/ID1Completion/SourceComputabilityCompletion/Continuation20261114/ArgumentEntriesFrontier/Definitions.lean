module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
def dependency : Program 2 := .composition ArgumentEntriesChildren.children (fun _ : Fin 1 => .projection 0)
def rawChildren (raw : Nat) : List Nat :=
  if arityValue raw = 0 then [] else
  if arityValue raw = 2 then [firstValue raw,secondValue raw] else [firstValue raw]
def originalFrontier {n : Nat} (seed : NumberedAuxiliaryCoding.Code (Fin n)) :
    Nat → List (NumberedAuxiliaryCoding.Code (Fin n)) :=
  Nat.rec [seed] (fun _ nodes => nodes.flatMap NumberedSyntaxBoundsPrimrecSupportProof.children)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier
