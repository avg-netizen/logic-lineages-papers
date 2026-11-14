module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Input order [source head,source base,target head,target base,symbols,types]. -/
def windowGuard (n : Nat) (arity : Fin n → Nat) : Program 6 :=
  .composition (OriginalHeadWindow.window n arity) ![.projection 0,.projection 4,.projection 5]
def sourceGuard (n : Nat) (arity : Fin n → Nat) : Program 6 :=
  .composition (OriginalSourceHeads.member n arity) ![.projection 2,.projection 4,.projection 5]
def classGuard : Program 6 := .composition OriginalHeadClass.equivalent ![.projection 0,.projection 2]
def permutationGuard : Program 6 := .composition OriginalArgumentPermutation.check ![.projection 1,.projection 3]
/-- Original left-associated four Boolean conjuncts, with actual component ASTs. -/
def headMove (n : Nat) (arity : Fin n → Nat) : Program 6 :=
  InternalAcceptance.conjunction
    (InternalAcceptance.conjunction (InternalAcceptance.conjunction (windowGuard n arity) (sourceGuard n arity)) classGuard)
    permutationGuard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove
