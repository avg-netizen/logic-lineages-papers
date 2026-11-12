module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnAssemblySupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditarySettledObserverDefinitions
open OriginalHereditaryExpectedReturnSupportProof OriginalHereditaryWorkBound

theorem valuesUnique {n : Nat} (arity : Fin n → Nat) (R : Program 2) (c : Nat)
 (xs : List (Job n)) (vs ws : List Nat)
 (hv : List.Forall₂ (Expected arity R c) xs vs)
 (hw : List.Forall₂ (Expected arity R c) xs ws) : vs = ws := by
 induction hv generalizing ws with
 | nil => cases hw; rfl
 | cons h ht ih =>
   cases hw with
   | cons g gt => exact congrArg₂ List.cons
       (OriginalHereditaryExpectedUniquenessProof.deterministic n arity R c _ _ _ h g) (ih _ gt)

theorem decorateLength {n c : Nat} (a : Job n) (index : Nat) (ss : List (State (Fin n))) :
 (decorate c a index ss).length = ss.length := by
 induction ss generalizing index with
 | nil => rfl
 | cons s ss ih => exact congrArg Nat.succ (ih (index+1))

theorem termFrame (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (c : Nat) (q : Packed (Fin n) arity Gamma) :
 OriginalHereditaryRuntimeWork.frameNumber c (.returning (termJob q)) =
 OriginalHereditaryVisitScheduler.returnNumber (OriginalHereditaryReturnStep.termJob c q)
   (OriginalHereditaryReturnStep.termChildren Q c q).length Gamma.length := by
 have hc : (children Gamma (termCode q.2)).length = (OriginalHereditaryReturnStep.termChildren Q c q).length := by
   obtain ⟨tau,q⟩ := q
   cases q <;> rfl
 simp only [OriginalHereditaryRuntimeWork.frameNumber,OriginalHereditaryRuntimeWork.jobNumber,
   termJob,OriginalHereditaryExpansion.jobNumber,OriginalHereditaryReturnStep.termJob,
   OriginalTypedDecoderReconstructionLocalProof.contextNumber,hc]

theorem argumentFrame (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
 OriginalHereditaryRuntimeWork.frameNumber c (.returning (argumentJob args)) =
 OriginalHereditaryVisitScheduler.returnNumber (OriginalHereditaryReturnStep.argumentJob c args)
   (OriginalHereditaryReturnStep.argumentChildren Q c args).length Gamma.length := by
 have hc : (children Gamma (argumentsCode args)).length = (OriginalHereditaryReturnStep.argumentChildren Q c args).length := by
   cases args <;> rfl
 simp only [OriginalHereditaryRuntimeWork.frameNumber,OriginalHereditaryRuntimeWork.jobNumber,
   argumentJob,OriginalHereditaryExpansion.jobNumber,OriginalHereditaryReturnStep.argumentJob,
   OriginalTypedDecoderReconstructionLocalProof.contextNumber,hc]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnAssemblySupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnAssemblySupportProof
