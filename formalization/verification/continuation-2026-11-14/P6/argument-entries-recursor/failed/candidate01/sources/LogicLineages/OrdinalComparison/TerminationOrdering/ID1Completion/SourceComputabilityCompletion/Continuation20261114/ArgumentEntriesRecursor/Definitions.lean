module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def rank : Program 2 := .projection 0
def dependency : Program 2 := ArgumentEntriesFrontier.dependency
def layer : Program 3 := .composition ArgumentEntriesLayer.recombine ![.projection 0,.projection 1]
def graph : Program 3 := ExchangeGraphRecursion.graph rank dependency layer
def extract : Program 2 := ExchangeSelectedRecursor.exchange rank dependency layer
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor
