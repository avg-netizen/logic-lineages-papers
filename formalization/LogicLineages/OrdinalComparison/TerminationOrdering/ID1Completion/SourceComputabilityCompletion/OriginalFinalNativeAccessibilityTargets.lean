module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityTargets
open UniformCertificateCompletion OriginalFinalNativeAccessibility

def ActualOriginalCanonicalCarrierAccessibility : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), CanonicalAccessibility n arity

def ActualOriginalContextObjectAccessibility : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ObjectAccessibility n arity

/-- The only tuple hypothesis is its ORIGINAL input calibration. -/
def ActualOriginalFinalStandardLeastMembership : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → StandardLeastMembership n arity p

def ActualOriginalFinalClosedFormulaTruth : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → ClosedFormulaTruth n arity p

def ActualOriginalFinalNativeProperties : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
  GlobalSourcePackage.InputsCalibrated n arity p → Properties n arity p

/-- No caller-chosen calibration, rank, window, context or final tuple. This
native standard-model endpoint DOES NOT discharge internal lem:id1. -/
def ActualOriginalFinalNativeGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityTargets
