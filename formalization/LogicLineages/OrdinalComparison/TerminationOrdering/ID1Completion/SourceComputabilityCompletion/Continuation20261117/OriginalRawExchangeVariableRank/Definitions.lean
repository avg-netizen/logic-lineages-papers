module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Auxiliary measure wrapper only: original raw rank, packed with zero to use
an existing sum/max fold. It replaces no original exchange/primary program. -/
def rawRankCode : Program 1 := .composition InternalPairing.pairing
  ![OriginalRawSyntaxTransport.variableRankRaw,InternalAcceptance.constantZero 1]
def rankWeight : Program 1 := .composition rawRankCode (fun _ : Fin 1 => InternalUnpair.right)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank
