module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual numeric membership in D(node,param), inputs [child,node,param].
This auxiliary observation does not replace the original frontier AST. -/
def dependencyMember (D : Program 2) : Program 3 :=
  .composition TwoSol20261113.CalibratedPrimary.Membership.contains
    ![.composition D ![.projection 1,.projection 2],.projection 0]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage
