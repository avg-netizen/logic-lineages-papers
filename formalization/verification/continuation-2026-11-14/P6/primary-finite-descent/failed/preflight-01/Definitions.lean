module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
/-- Either membership has stabilized, or every elapsed round is charged
against the initial uncovered-occurrence budget. This is a formula only,
not a changed iteration or a new assumed invariant. -/
def budget {alpha : Type} (elapsed initialRemaining remaining out next : OTerm alpha) : Formula alpha :=
  PrimaryMonotonicity.included next out ⊔
    PrimaryUncoveredCount.bounded (InternalTagArithmeticSyntaxProof.add elapsed remaining) initialRemaining
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent
