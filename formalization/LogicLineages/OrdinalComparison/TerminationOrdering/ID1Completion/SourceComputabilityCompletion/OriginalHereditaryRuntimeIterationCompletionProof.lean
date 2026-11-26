module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCompletionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryRuntimeWork
open OriginalHereditaryRuntimeIterationDefinitions

theorem emptyFixed (R : Program 2) (state : Nat) (h : (Nat.unpair state).1 = 0) :
 tick R state = state := by
 have he := OriginalHereditaryCombinedStepProof.unsupportedIdentity.1 R (Nat.unpair state).2
 have hp : Nat.pair 0 (Nat.unpair state).2 = state := by
   calc
     Nat.pair 0 (Nat.unpair state).2 = Nat.pair (Nat.unpair state).1 (Nat.unpair state).2 := congrArg (fun x => Nat.pair x (Nat.unpair state).2) h.symm
     _ = state := Nat.pair_unpair state
 rw [hp] at he
 exact he

theorem emptyIterate (R : Program 2) (state count : Nat)
 (h : (Nat.unpair state).1 = 0) : (tick R)^[count] state = state := by
 induction count with
 | zero => rfl
 | succ count ih => rw [Function.iterate_succ_apply',ih,emptyFixed R state h]

theorem completion : OriginalHereditaryRuntimeIterationTargets.Completion := by
 intro R n arity c a result ha
 obtain ⟨count,he,hbound,htrace⟩ := OriginalHereditaryAgendaProof.boundedTrace n c a []
 have ht : TypedAgenda arity [.visit a] := by
   intro f hf
   rcases List.mem_singleton.mp hf with rfl
   exact ha
 have hw := OriginalHereditaryRuntimeIterationTraceProof.traceWork R n arity c count
   [.visit a] [] (Nat.pair (agendaNumber c [.visit a]) result) ht htrace (by simp only [Nat.unpair_pair])
 change (Nat.unpair ((tick R)^[count] (Nat.pair (agendaNumber c [.visit a]) result))).1 = 0 at hw
 rw [OriginalHereditaryRuntimeIterationCalibrationProof.calibration]
 have hb : count ≤ fuel a := hbound
 obtain ⟨extra,hextra⟩ := Nat.exists_eq_add_of_le hb
 rw [hextra, Nat.add_comm count extra, Function.iterate_add_apply]
 rw [emptyIterate R _ extra hw]
 exact hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCompletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCompletionProof
