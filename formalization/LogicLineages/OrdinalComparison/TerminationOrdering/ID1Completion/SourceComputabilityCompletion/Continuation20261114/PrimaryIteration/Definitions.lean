module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Inputs [count,pool,initial-reached,parameter]. Fixed pool/parameter and
literal original expansion; only the recursively reached list changes. -/
def iterate (E : Program 3) : Program 4 :=
  .recursion (.projection (1 : Fin 3))
    (.composition (PrimaryExpansion.expand E) ![.projection 2,.projection 1,.projection 4])
/-- Inputs [count,pool,seed,parameter]. Original singleton seed, not an empty
reached list or a deduplicated candidate collection. -/
def run (E : Program 3) : Program 4 :=
  .composition (iterate E) ![.projection 0,.projection 1,
    .composition InternalListCodec.consCode ![.projection 2,InternalAcceptance.constantZero 4],
    .projection 3]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration
