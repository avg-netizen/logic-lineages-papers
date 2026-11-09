module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectTargets
open Source UniformCertificateCompletion OriginalVariableObject

/-- ONE original global Inputs choice precedes every finite window. Use the
SAME final once-refined tuple as the accepted full fold/quotient/path laws.
Native input calibration is the paid original contract, not an internal
reflection principle. Shared Gamma is a CONCLUSION, bound internally. -/
def ActualOriginalVariableObjectCertificateBottom : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let r := OriginalVariableRepresentative.refineInputs p
  let src := GlobalSourcePackage.source r
  let comp := GlobalSourcePackage.computability r
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  VariableCertificateBottom src comp (OrdinaryArithmeticQuotient.contextCode symbols S table)

/-- Original Object variable-I bridge at arbitrary finite type and Delta.
No tau-in-S premise, replacement source predicate, independent Gamma-specific
Program selection or assumed arrow/neutral computability is introduced. -/
def ActualOriginalVariableObjectLeast : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p →
  let r := OriginalVariableRepresentative.refineInputs p
  let src := GlobalSourcePackage.source r
  let comp := GlobalSourcePackage.computability r
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  VariableLeast src comp (OrdinaryArithmeticQuotient.contextCode symbols S table)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectTargets
