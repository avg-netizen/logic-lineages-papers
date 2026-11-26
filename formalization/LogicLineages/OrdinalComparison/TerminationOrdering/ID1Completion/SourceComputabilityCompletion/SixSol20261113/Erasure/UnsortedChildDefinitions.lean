module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ListSumBoundDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildDefinitions
inductive BaseSlot where
 | ordinary | numbered
def tag : BaseSlot → Nat
 | .ordinary => 4
 | .numbered => 5
def slot : BaseSlot → ObservationDescentDefinitions.ListSlot
 | .ordinary => .ordinaryBase
 | .numbered => .numberedBase
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.UnsortedChildDefinitions
