module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport
/-- Literal original decoder cutoff raw+1 and bound raw; final lookup retains index raw. -/
def table (n : Nat) : Program 1 := .composition (OriginalCodeDecoderTable.tableProgram n)
  ![succOf (.projection 0),.projection 0]
def check (n : Nat) : Program 1 := .composition InternalRawListRecursion.lookup
  ![.projection 0,table n]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard
