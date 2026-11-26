module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectLeastProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalVariablesProof
open Source OriginalFunctionNeutrality OriginalVariableObject UniformCertificateCompletion

/-- Calibration of the literal input to the final variable refinement.
Every prior guard is retained, with no new input selection. -/
theorem beforeVariableCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity
      (OriginalNeutralLeaf.refineInputs
        (OriginalConstructorShape.refineInputs (refineInputs p))) := by
  have hn := OriginalFunctionNeutralityInputProof.refinedInputsCalibrated n arity p hp
  have hs := OriginalConstructorShapeInputProof.refinedInputsCalibrated
    n arity (refineInputs p) hn
  exact OriginalNeutralLeafProof.refinedInputsCalibrated
    n arity (OriginalConstructorShape.refineInputs (refineInputs p)) hs

/-- The two original Object laws use the same final source and computability
programs at every closed source window, after one global input choice. -/
theorem finalVariableLaws (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) :
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    VariableCertificateBottom (GlobalSourcePackage.source (finalInputs p))
      (GlobalSourcePackage.computability (finalInputs p)) context ∧
    VariableLeast (GlobalSourcePackage.source (finalInputs p))
      (GlobalSourcePackage.computability (finalInputs p)) context := by
  let q := OriginalNeutralLeaf.refineInputs
    (OriginalConstructorShape.refineInputs (refineInputs p))
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    beforeVariableCalibrated n arity p hp
  exact ⟨OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom
      n arity q hq symbols S table hS,
    OriginalVariableObjectLeastProof.actualOriginalVariableObjectLeast
      n arity q hq symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalVariablesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityFinalVariablesProof
