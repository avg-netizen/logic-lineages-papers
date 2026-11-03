module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleTargets
open Source Source.SourceMarkedSyntax RecursiveComparison SourceUnmarked MarkedSourceTransitivityCounterexample

def ActualExtendedSteps : Prop :=
  SourceExtendedComparison.Weak Nat arity above [] ⟨.ground,s⟩ ⟨.ground,t⟩ ∧
  SourceExtendedComparison.Weak Nat arity above [] ⟨.ground,t⟩ ⟨.ground,u⟩ ∧
  Unmarked Nat arity [] u

def ActualOriginalFailure : Prop := ¬ RecursiveComparison.Weak Nat arity above [] ⟨.ground,s⟩ ⟨.ground,u⟩

def ActualBroadTargetRefutation : Prop := ¬ SourceFinalTransitivityTargets.ActualUnmarkedFinalComposition

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSourceTransitivityCounterexampleTargets
