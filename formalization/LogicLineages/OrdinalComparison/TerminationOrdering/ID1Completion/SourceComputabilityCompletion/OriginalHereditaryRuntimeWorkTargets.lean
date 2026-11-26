module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryRuntimeWork OriginalHereditaryAgendaDefinitions
/-- Exact decoration order, not merely forgotten raw cores. -/
def JobsEncoding : Prop := ∀ n c (a : Job n),
  (jobs c a).map (jobNumber c) =
    OriginalHereditaryAnnotatedExpansion.values a.role a.typ
      (NumberedLeastCodeRepresentative.codeNumber a.core.code)
      ((OriginalHereditaryWorkBound.successors a.core).map (OriginalHereditaryExpansion.jobNumber c))
/-- Actual executable one-step work projection, with arbitrary numeric result
stack. The agenda must be typed: malformed unsupported returns may stall.
No semantic result-stack invariant or full evaluator/fuel claim is made. -/
def StepWork : Prop := ∀ (R : Program 2) (n : Nat) (arity : Fin n → Nat) c
    (before after : List (Frame n)) (result : Nat),
  TypedAgenda arity before → Step c before after →
    (Nat.unpair (evaluate (OriginalHereditaryCombinedStep.step R)
      (List.Vector.ofFn ![Nat.pair (agendaNumber c before) result]))).1 = agendaNumber c after

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkTargets
