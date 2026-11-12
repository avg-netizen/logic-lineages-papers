module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryReturnStep
open OriginalHereditaryVisitScheduler (stateNumber returnNumber)
open OriginalHereditaryReturnStepEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalTypedDecoderEvaluationSupportProof

theorem stateCons (j a d : Nat) (agenda outputs : List Nat) :
    stateNumber (returnNumber j a d :: agenda) outputs =
      input j a d (numbersNumber agenda) (numbersNumber outputs) := rfl

theorem termChildrenBound (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) (q : Packed (Fin n) arity Gamma) : (termChildren Q c q).length ≤ 2 := by
  obtain ⟨tau,q⟩ := q
  cases q <;> simp [termChildren]

theorem termChildrenSlots (Q : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (c : Nat) (q : Packed (Fin n) arity Gamma) :
    ((termChildren Q c q).getD 0 0,(termChildren Q c q).getD 1 0) = OriginalHereditaryReturn.slots Q c q := by
  obtain ⟨tau,q⟩ := q
  cases q <;> rfl

theorem listValueEvaluation (q p a d tail result : Nat) :
    evaluate listStep (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result]) =
    if (Nat.unpair q).1 = 6 then
      evaluate (pop (OriginalRawSyntaxTransport.constant 1 0))
        (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result])
    else if (Nat.unpair q).1 = 7 then
      evaluate (pop argumentsValue)
        (ofFn ![input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result])
    else input (OriginalHereditaryAnnotatedExpansion.jobNumber 1 0 (Nat.pair q p)) a d tail result := by
  simp only [listStep,ifSameEvaluation,leftOfEvaluation,constantEvaluation,
    (metadata 1 0 q p a d tail result).2.2,
    OriginalHereditaryVisitSchedulerEvaluationProof.projectionEvaluation,
    List.Vector.get_ofFn,Matrix.cons_val_zero]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepSupportProof
