module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepArgumentsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedAuxiliaryCoding
open OriginalHereditaryReturnStep OriginalHereditaryReturnStepSupportProof OriginalHereditaryReturnStepEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem argumentsReturn : OriginalHereditaryReturnStepTargets.ArgumentsReturn := by
  intro R Q n arity Gamma types c args deletions agenda old hd
  rw [← hd,stateCons,argumentJob,listDispatch,listValueEvaluation]
  have hb : (argumentChildren Q c args).length ≤ 2 := by cases args <;> simp [argumentChildren]
  have hc := OriginalHereditaryResultStackProgramProof.calibration (argumentChildren Q c args) deletions old hb
  dsimp only at hc
  cases args with
  | nil =>
    simp only [argumentsCode,codeNumber,Nat.unpair_pair,ite_true]
    rw [popEvaluation,constantEvaluation,hc.2.2.2]
    rfl
  | @cons Gamma tau types q args =>
    simp only [argumentsCode,codeNumber,Nat.unpair_pair,show (7 : Nat) ≠ 6 by decide,ite_false,ite_true]
    rw [popEvaluation,argumentsEvaluation,hc.1,hc.2.1,hc.2.2.2]
    have hr := OriginalHereditaryReturnNativeProof.argumentsConsSubstitution Q n arity Gamma c tau types q args
    have hs0 : (argumentChildren Q c (.cons q args)).getD 0 0 = OriginalHereditaryReturn.scalar Q c ⟨tau,q⟩ := rfl
    have hs1 : (argumentChildren Q c (.cons q args)).getD 1 0 =
      numbersNumber (OriginalRootObservation.argumentValues Q c args) := rfl
    rw [hs0,hs1]
    simp only [argumentsCode,codeNumber] at hr
    rw [hr]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepArgumentsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepArgumentsProof
