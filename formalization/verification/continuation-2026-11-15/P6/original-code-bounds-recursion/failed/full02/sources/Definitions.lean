module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- Exact raw code rank and original immediate-child dependency; no cache values
or argument-entry layer are reused. -/
def rank : Program 2 := .projection 0
def dependency : Program 2 := ArgumentEntriesFrontier.dependency
def accepted (n : Nat) : Program 3 :=
  .composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => .projection 0)
/-- Explicit totalization for the recursive evaluator only: invalid raw code
returns Some(0,0)=1; accepted code uses unchanged original recombine. -/
def layer (n : Nat) : Program 3 :=
  InternalAcceptance.branch (accepted n) (InternalLessThan.constantOne 3)
    (.composition (OriginalBoundsRecombination.recombine n) ![.projection 0,.projection 1])
def graph (n : Nat) : Program 3 := ExchangeGraphRecursion.graph rank dependency (layer n)
def extract (n : Nat) : Program 2 := ExchangeSelectedRecursor.exchange rank dependency (layer n)
/-- The unused auxiliary parameter is concretely zero. Output is the pair payload,
not Option encoding; malformed-code totalization therefore extracts zero. -/
def bounds (n : Nat) : Program 1 :=
  .composition (extract n) ![.projection 0,OriginalRawSyntaxTransport.constant 1 0]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion
