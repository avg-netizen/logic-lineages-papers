module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottom
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- New standalone leaf; not the previously selected global final leaf. Both refinements capture the SAME original concrete source. -/
def source (H G : Program 1) (M W : Program 2) : Program 2 := OriginalUniverseDecoder.source H G M W
def leaf (H G : Program 1) (M W : Program 2) (oldStep : Program 4) : Program 4 :=
 OriginalTransparentMixedPathDefinitions.refined (source H G M W)
  (OriginalTransparentDirectBottom.refined (source H G M W) oldStep)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottom
