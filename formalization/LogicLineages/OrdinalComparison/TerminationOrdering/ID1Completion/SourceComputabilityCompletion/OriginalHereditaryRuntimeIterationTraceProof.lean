module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTraceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryRuntimeWork
open OriginalHereditaryRuntimeIterationDefinitions

theorem stepAt (R : Program 2) (n : Nat) (arity : Fin n → Nat) c
 (before after : List (Frame n)) state
 (ht : TypedAgenda arity before) (hs : Step c before after)
 (hw : (Nat.unpair state).1 = agendaNumber c before) :
 (Nat.unpair (tick R state)).1 = agendaNumber c after := by
 have h := OriginalHereditaryRuntimeWorkProof.stepWork R n arity c before after
   (Nat.unpair state).2 ht hs
 rw [← hw, Nat.pair_unpair] at h
 exact h

theorem traceWork : OriginalHereditaryRuntimeIterationTargets.TraceWork := by
 intro R n arity c count before after state ht hs hw
 induction hs generalizing state with
 | refl agenda => exact hw
 | @step k a b z hs tail ih =>
   have hb : TypedAgenda arity b :=
     OriginalHereditaryTypedAgendaProof.stepPreservation n arity c a b hs ht
   rw [Function.iterate_succ_apply]
   exact ih (tick R state) hb (stepAt R n arity c a b state ht hs hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTraceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTraceProof
