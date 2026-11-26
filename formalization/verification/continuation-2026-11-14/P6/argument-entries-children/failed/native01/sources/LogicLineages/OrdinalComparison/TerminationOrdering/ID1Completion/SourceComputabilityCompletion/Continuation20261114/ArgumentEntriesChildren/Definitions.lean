module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport InternalApplicationCertificateConstructors
def raw : Program 1 := .projection 0
def singleton : Program 1 := consOf (firstOf raw) (constant 1 0)
def double : Program 1 := consOf (firstOf raw) (consOf (secondOf raw) (constant 1 0))
/-- Exact original children order. Binary tail/second child stays at index1. -/
def children : Program 1 := InternalAcceptance.branch (arityOf raw) (constant 1 0)
  (InternalAcceptance.branch (sameOf (arityOf raw) (constant 1 2)) singleton double)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren
