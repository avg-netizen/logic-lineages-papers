module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionTargets
open Source UniformCertificateCompletion OriginalVariableObject

/-- Choose the original input tuple before every finite source window and
ambient context. The same final once-refined source retains its full original
calibration and certificate/downward package, and proves both Object-variable
laws internally. No source-specific compatibility or leastness field is an
input to this selection. -/
def ActualOriginalVariableObjectGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := OriginalVariableRepresentative.refineInputs p
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSelectionTargets
