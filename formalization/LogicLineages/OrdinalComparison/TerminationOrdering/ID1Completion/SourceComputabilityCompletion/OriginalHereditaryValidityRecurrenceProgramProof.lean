module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceNumericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceProgramProof
open OriginalHereditaryValidity OriginalHereditaryValidityEvaluationSupportProof
open OriginalHereditaryValidityEvaluationBoundedProof
open OriginalHereditaryValidityRecurrenceNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exposed node AST reads the literal root of the original singleton
initial machine state, including both raw selectors and the full parameter. -/
theorem nodeCheckInitialEvaluation (oldSource oldTarget member : Program 2)
    (value parameter : Nat) :
    evaluate (nodeCheck oldSource oldTarget member)
        (List.Vector.ofFn ![initialValue value parameter]) =
      nodeCheckValue
        (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
        value parameter := by
  simp [nodeCheckEvaluation, currentRawEvaluation, currentParameterEvaluation,
    currentFrameEvaluation, workEvaluation, initialValue]

/-- Calibration transports the native result to the SAME validator Program;
no internal object-language consequence is inferred from this numeric fact. -/
theorem actualOriginalHereditaryProgramRecurrence :
    OriginalHereditaryValidityRecurrenceTargets.ActualOriginalHereditaryProgramRecurrence := by
  intro oldSource oldTarget member value parameter
  have h := actualOriginalHereditaryValidatorRecurrence
    (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
    (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
    (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
    value parameter
  simpa only [validatorEvaluation, nodeCheckInitialEvaluation, List.Vector.get_ofFn,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h.2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceProgramProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceProgramProof
