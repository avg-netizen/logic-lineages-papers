module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.EncodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Actual list-recursion inputs are [head,recursive result], without parameters. -/
def symbolStep (n : Nat) : Program 2 :=
  InternalAcceptance.conjunction
    (.composition InternalLessThan.ltTest ![.projection 0,constant 2 n]) (.projection 1)
/-- Literal original Encodable symbol-list validity. Empty list is accepted;
every occurrence, in its original order, is checked against the finite bound. -/
def symbols (n : Nat) : Program 1 :=
  InternalRawListRecursion.listRec (InternalLessThan.constantOne 0) (symbolStep n)
/-- Original product Window = List(Fin n) × List Ty. The type-list decoder's
all-raw totality is a proof duty, not an additional validity assumption. -/
def window (n : Nat) : Program 1 :=
  .composition (symbols n) (fun _ : Fin 1 => InternalUnpair.left)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity
