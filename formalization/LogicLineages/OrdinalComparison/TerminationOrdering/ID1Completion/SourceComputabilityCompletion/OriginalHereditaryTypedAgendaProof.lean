module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaProof
open OriginalHereditaryAgendaDefinitions OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryTypedAgendaDefinitions OriginalHereditaryTypedAgendaTargets

theorem stepPreservation : StepPreservation := by
 intro n arity c source target hs ht
 cases hs with
 | visit a suffix =>
   have ha : Typed arity a := ht (.visit a) (List.mem_cons_self)
   intro f hf
   rcases List.mem_append.mp hf with hchild | hrest
   · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hchild
     exact OriginalHereditaryTypedJobProof.expansionClosure n arity c a b ha hb
   · rcases List.mem_cons.mp hrest with rfl | hf
     · exact ha
     · exact ht f (List.mem_cons_of_mem _ hf)
 | returning a suffix =>
   intro f hf
   exact ht f (List.mem_cons_of_mem _ hf)

theorem tracePreservation : TracePreservation := by
 intro n arity c count source target h
 induction h with
 | refl agenda => exact fun h => h
 | step hs tail ih =>
   intro ht
   exact ih (stepPreservation n arity c _ _ hs ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedAgendaProof
