module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticListProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions

theorem listExecution (R : Program 2) {n : Nat} (arity : Fin n → Nat) c
 (cost : Job n → Nat) (xs : List (Job n))
 (each : ∀ a ∈ xs, ∀ suffix old, ∃ value, Expected arity R c a value ∧
   (tick R)^[cost a] (state c (.visit a :: suffix) old) = state c suffix (value :: old))
 (suffix : List (Frame n)) (old : List Nat) :
 ∃ values, List.Forall₂ (Expected arity R c) xs values ∧
 (tick R)^[(xs.map cost).sum] (state c (xs.map Frame.visit ++ suffix) old) =
 state c suffix (values.reverse ++ old) := by
 induction xs generalizing old with
 | nil => exact ⟨[],List.Forall₂.nil,rfl⟩
 | cons a xs ih =>
   obtain ⟨value,hv,he⟩ := each a List.mem_cons_self (xs.map Frame.visit ++ suffix) old
   obtain ⟨values,hvs,hes⟩ := ih (fun b hb => each b (List.mem_cons_of_mem a hb)) (value :: old)
   refine ⟨value :: values,List.Forall₂.cons hv hvs,?_⟩
   simp only [List.map_cons,List.sum_cons,List.cons_append]
   rw [Nat.add_comm (cost a),Function.iterate_add_apply,he,hes]
   simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticListProof
