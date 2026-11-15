module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.AgreementDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Private parametric spelling of the frozen ordered standalone answer map. -/
def step (E : Program 2) : Program 3 :=
  .composition InternalListCodec.consCode ![.composition E ![.projection 0,.projection 2],.projection 1]
def orderedMap (E : Program 2) : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) (step E)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.MapDefinitions
