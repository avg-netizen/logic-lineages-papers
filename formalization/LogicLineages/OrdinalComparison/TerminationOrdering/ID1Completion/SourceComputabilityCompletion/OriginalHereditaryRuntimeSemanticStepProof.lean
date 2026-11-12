module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticStepProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryRuntimeWork
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions
open OriginalHereditaryVisitScheduler (stateNumber)

theorem visit (R : Program 2) {n : Nat} (c : Nat) (a : Job n)
 (suffix : List (Frame n)) (old : List Nat) :
 tick R (state c (.visit a :: suffix) old) =
 state c ((jobs c a).map Frame.visit ++ .returning a :: suffix) old := by
 have h := OriginalHereditaryAnnotatedVisitNativeProof.visitSimulation n c a.role a.typ a.core
   (suffix.map (frameNumber c)) old
 have hj := OriginalHereditaryRuntimeWorkEncodingProof.jobsEncoding n c a
 dsimp only [state,stateNumber,List.map_cons,frameNumber,tick]
 rw [NumberedMultisetNumeric.numbersNumber]
 rw [OriginalHereditaryCombinedStepProof.visitDispatch]
 change _ = stateNumber (((jobs c a).map Frame.visit ++ .returning a :: suffix).map (frameNumber c)) old
 rw [← hj] at h
 have hm : (frameNumber (n:=n) c) ∘ (Frame.visit (n:=n)) = OriginalHereditaryVisitScheduler.visitNumber ∘ (jobNumber (n:=n) c) := rfl
 simp only [List.map_append,List.map_cons,List.map_map,frameNumber] at ⊢
 rw [hm]
 simpa only [jobNumber,stateNumber,NumberedMultisetNumeric.numbersNumber,List.map_map] using h

theorem returning (localReturn : OriginalHereditaryExpectedReturnTargets.LocalReturn)
 (R : Program 2) {n : Nat} (arity : Fin n → Nat) c (a : Job n)
 (values : List Nat) (suffix : List (Frame n)) (old : List Nat)
 (ha : OriginalHereditaryTypedJobDefinitions.Typed arity a)
 (hv : List.Forall₂ (OriginalHereditaryExpectedDefinitions.Expected arity R c) (jobs c a) values) :
 ∃ value, OriginalHereditaryExpectedDefinitions.Expected arity R c a value ∧
 tick R (state c (.returning a :: suffix) (values.reverse ++ old)) = state c suffix (value :: old) := by
 obtain ⟨value,hv,he⟩ := localReturn R n arity c a values (suffix.map (frameNumber c)) old ha hv
 refine ⟨value,hv,?_⟩
 dsimp only [tick,state,List.map_cons,stateNumber]
 rw [NumberedMultisetNumeric.numbersNumber]
 simp only [frameNumber]
 rw [OriginalHereditaryCombinedStepProof.returnDispatch]
 exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticStepProof
