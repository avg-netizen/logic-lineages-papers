module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact actual dependency membership, inputs [node,child,param]. No oracle. -/
def dependencyEdge (D : Program 2) : Program 3 :=
  .composition TwoSol20261113.CalibratedPrimary.Membership.contains
    ![.composition D ![.projection 0,.projection 2],.projection 1]
/-- An object-language existential node in the prior frontier, whose actual D
output contains child. The D output itself is bound by the composition graph. -/
def predecessor {alpha : Type} (D : Program 2)
    (frontier child param : InternalGraphComposition.OTerm alpha) :=
  PrimaryExpansionSoundness.sourceWitness (dependencyEdge D) frontier child param
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness
