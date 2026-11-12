module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkReturnProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryRuntimeWork OriginalHereditaryAgendaDefinitions
open OriginalHereditaryReturnStepEvaluationProof OriginalHereditaryReturnStepSupportProof
open OriginalHereditaryVisitScheduler (returnNumber)

theorem termPop (R : Program 2) (t q p a d tail result : Nat) :
    (Nat.unpair (evaluate (OriginalHereditaryReturnStep.step R)
      (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 0 t (Nat.pair q p)) a d tail result]))).1 = tail := by
  rw [termDispatch,popEvaluation,Nat.unpair_pair]

theorem listPop (R : Program 2) (q p a d tail result : Nat)
    (h : (Nat.unpair q).1 = 6 ∨ (Nat.unpair q).1 = 7) :
    (Nat.unpair (evaluate (OriginalHereditaryReturnStep.step R)
      (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result]))).1 = tail := by
  rw [listDispatch,listValueEvaluation]
  rcases h with h | h
  · rw [h,if_pos rfl,popEvaluation,Nat.unpair_pair]
  · rw [h,if_neg (by decide),if_pos rfl,popEvaluation,Nat.unpair_pair]

theorem returnWork (R : Program 2) {n : Nat} (arity : Fin n → Nat) (c : Nat)
    (a : Job n) (ha : OriginalHereditaryTypedJobDefinitions.Typed arity a) (tail result : Nat) :
    (Nat.unpair (evaluate (OriginalHereditaryCombinedStep.step R) (ofFn ![
      Nat.pair (1+Nat.pair (returnNumber (jobNumber c a)
        (OriginalHereditaryWorkBound.children a.core.context a.core.code).length a.core.context.length) tail) result]))).1 = tail := by
  rw [OriginalHereditaryCombinedStepProof.returnDispatch]
  have h := OriginalHereditaryTypedJobProof.returnShape n arity a ha
  rcases h with h | ⟨hrole,htyp,htag⟩
  · simp only [jobNumber,OriginalHereditaryExpansion.jobNumber,h]
    exact termPop R a.typ _ _ _ _ tail result
  · simp only [jobNumber,OriginalHereditaryExpansion.jobNumber,hrole,htyp]
    exact listPop R _ _ _ _ tail result htag

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkReturnProof
