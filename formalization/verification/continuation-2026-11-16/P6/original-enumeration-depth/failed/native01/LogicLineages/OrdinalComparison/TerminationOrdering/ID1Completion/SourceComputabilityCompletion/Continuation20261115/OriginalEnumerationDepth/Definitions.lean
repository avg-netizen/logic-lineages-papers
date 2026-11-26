module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumerationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- New explicit supplier for the original enumeration depth, not codeBounds size.
Fold actual ordered child depths with maximum; empty-child depth maximum is zero. -/
def collect : Program 1 := InternalRawListRecursion.listRec
  (OriginalRawSyntaxTransport.constant 0 0) OriginalBoundsRecombination.maximum
def rank : Program 2 := .projection 0
def dependency : Program 2 := ArgumentEntriesFrontier.dependency
/-- This validity guard is the actual original Code decoder check. -/
def accepted (n : Nat) : Program 3 :=
  .composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => .projection 0)
/-- Invalid code returns Some(0)=1. Valid code returns Some(1+max children),
hence TWO successor layers. These are independent depth-cache values. -/
def layer (n : Nat) : Program 3 := InternalAcceptance.branch (accepted n)
  (OriginalRawSyntaxTransport.constant 3 1)
  (.composition .succ (fun _ : Fin 1 => .composition .succ (fun _ : Fin 1 =>
    .composition collect (fun _ : Fin 1 => .projection 1))))
def graph (n : Nat) : Program 3 := ExchangeGraphRecursion.graph rank dependency (layer n)
def extract (n : Nat) : Program 2 := ExchangeSelectedRecursor.exchange rank dependency (layer n)
/-- Actual raw malformed totalization is zero, while every valid leaf has depth1. -/
def depth (n : Nat) : Program 1 := .composition (extract n)
  ![.projection 0,OriginalRawSyntaxTransport.constant 1 0]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth
