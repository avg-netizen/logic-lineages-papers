module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedChildTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Unconditional generic wrapper specialization at the literal NEW C.
The definition retains its actual accepted-parent and lambda/nonbottom domain;
actual child coordinates are generated internally, not assumed. -/
def ActualChildElimination : Prop := ∀ (H G : Program 1) (M W : Program 2)
 (oldStep : Program 4) (window : Program 1),
 OriginalHereditaryLambda.InternalChildElimination
  (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
/-- Both statements use the identical explicit C. This makes no identification
with an old final tuple, nor a claim about unrecognized source edges. -/
def ActualCoexistence : Prop := ActualChildElimination ∧
 OriginalMixedClosedTraceTargets.ActualClosedRestrictedTransport
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedChildTargets
