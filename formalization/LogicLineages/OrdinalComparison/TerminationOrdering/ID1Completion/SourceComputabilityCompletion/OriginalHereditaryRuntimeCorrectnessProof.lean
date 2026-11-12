module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions

theorem exactExecution : OriginalHereditaryRuntimeCorrectnessTargets.ExactExecution :=
 OriginalHereditaryRuntimeSemanticProof.exactExecution OriginalHereditaryExpectedReturnProof.localReturn

theorem budgetExecution : OriginalHereditaryRuntimeCorrectnessTargets.BudgetExecution := by
 intro R n arity c a old ha
 obtain ⟨value,hv,he⟩ := exactExecution R n arity c a [] old ha
 refine ⟨value,hv,?_⟩
 rw [OriginalHereditaryRuntimeIterationCalibrationProof.calibration] at he ⊢
 have hbound : 2 * OriginalHereditaryWorkBound.totalWork a.core ≤ fuel a :=
   Nat.mul_le_mul_left 2 (OriginalHereditaryWorkBoundProof.workBound (Fin n) a.core)
 obtain ⟨extra,hextra⟩ := Nat.exists_eq_add_of_le hbound
 rw [hextra,Nat.add_comm (2 * OriginalHereditaryWorkBound.totalWork a.core) extra,
   Function.iterate_add_apply,he]
 apply OriginalHereditaryRuntimeIterationCompletionProof.emptyIterate
 simp only [state,OriginalHereditaryVisitScheduler.stateNumber,List.map_nil,
   NumberedMultisetNumeric.numbersNumber,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessProof
