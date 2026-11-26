module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- Literal equality of the actual encoded-head field outputs. This is NOT
asserted to be raw headNumber equality on arbitrary malformed inputs. -/
def encodedEqual : Program 2 :=
  OriginalRawSyntaxTransport.sameOf
    (.composition OriginalHeadEncodingBridge.encodeHead (fun _ : Fin 1 => .projection 0))
    (.composition OriginalHeadEncodingBridge.encodeHead (fun _ : Fin 1 => .projection 1))
/-- Literal equality of actual head-result outputs; input order [target,source]
is retained at the recurrence endpoint. -/
def resultEqual : Program 2 :=
  OriginalRawSyntaxTransport.sameOf
    (.composition OriginalHeadResult.headResult (fun _ : Fin 1 => .projection 0))
    (.composition OriginalHeadResult.headResult (fun _ : Fin 1 => .projection 1))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence
