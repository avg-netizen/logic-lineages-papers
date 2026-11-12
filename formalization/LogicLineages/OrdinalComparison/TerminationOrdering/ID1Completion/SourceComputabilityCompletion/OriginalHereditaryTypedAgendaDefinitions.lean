module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaDefinitions
open OriginalHereditaryAgendaDefinitions OriginalHereditaryTypedJobDefinitions
def FrameTyped {n : Nat} (arity : Fin n → Nat) : Frame n → Prop
 | .visit a => Typed arity a
 | .returning a => Typed arity a
/-- Native agenda invariant, without any claim about result stack values. -/
def AgendaTyped {n : Nat} (arity : Fin n → Nat) (agenda : List (Frame n)) : Prop :=
 ∀ f ∈ agenda, FrameTyped arity f
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaDefinitions
