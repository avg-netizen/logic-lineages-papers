module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundTargets
open OriginalHereditaryWorkBound
def SuccessorBounds : Prop := ∀ (Symbol : Type) (s : State Symbol),
  (successors s).length ≤ weight s + 2 ∧ ∀ t ∈ successors s, weight t < weight s
def PathBound : Prop := ∀ (Symbol : Type) (depth : Nat) (s t : State Symbol),
  Path depth s t → depth + weight t ≤ weight s
/-- Coarse bound counts all raw-node and all-deletion branches, not just path depth.
It does not measure sorting/decoding/Program execution steps of a future machine. -/
def WorkBound : Prop := ∀ (Symbol : Type) (s : State Symbol),
  totalWork s ≤ budget (weight s + 2) (weight s)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundTargets
