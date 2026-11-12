module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWork
open OriginalHereditaryAgendaDefinitions
/-- Exact original native agenda encoding; window c is retained in every job. -/
def jobNumber {n : Nat} (c : Nat) (a : Job n) : Nat :=
  OriginalHereditaryAnnotatedExpansion.jobNumber a.role a.typ (OriginalHereditaryExpansion.jobNumber c a.core)
def frameNumber {n : Nat} (c : Nat) : Frame n → Nat
 | .visit a => OriginalHereditaryVisitScheduler.visitNumber (jobNumber c a)
 | .returning a => OriginalHereditaryVisitScheduler.returnNumber (jobNumber c a)
     (OriginalHereditaryWorkBound.children a.core.context a.core.code).length a.core.context.length
def agendaNumber {n : Nat} (c : Nat) (agenda : List (Frame n)) :=
  NumberedMultisetNumeric.numbersNumber (agenda.map (frameNumber c))
def TypedFrame {n : Nat} (arity : Fin n → Nat) : Frame n → Prop
 | .visit a => OriginalHereditaryTypedJobDefinitions.Typed arity a
 | .returning a => OriginalHereditaryTypedJobDefinitions.Typed arity a
def TypedAgenda {n : Nat} (arity : Fin n → Nat) (agenda : List (Frame n)) :=
  ∀ f ∈ agenda, TypedFrame arity f

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWork
