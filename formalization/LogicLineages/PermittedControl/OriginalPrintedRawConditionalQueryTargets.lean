module
public import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriverTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitTerminal (observe)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedRawFamilyFrontend (Args encodeInput familyCode)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open ActualBitFamilyRawDriver (BoundProgram HighProgram solve)
open ActualBitFamilyRawSemanticDriver (TypedHigh Certified)

noncomputable def result (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (p : Args) : Option Bool := (familyCode p).map (solve f bound high)

/-- This universal statement ranges only over successful observations.
An error is not a successful false observation. -/
def EverySuccessfulObservation (f : Nat → Nat) (gs : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Prop :=
  ∀ (base : Nat → Nat) (b : Bool), observe f base gs (.rows p) = .ok b → b = positive

def ExactOriginalRawConditionalQuery : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (bound : BoundProgram) (high : HighProgram) (children : TypedHigh),
    Certified f B bound high children →
    ∀ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula),
      Topological known gs → PlainPreparedFormula p → ∀ positive : Bool,
        ((result f bound high (encodeInput known gs p positive) = some true) ↔
          HasSuccessfulObservation f gs p positive) ∧
        ((result f bound high (encodeInput known gs p positive) = some false) ↔
          ¬ HasSuccessfulObservation f gs p positive) ∧
        ((result f bound high (encodeInput known gs p (!positive)) = some false) ↔
          EverySuccessfulObservation f gs p positive)

def ExactOriginalRawQueryFailure : Prop :=
  ∀ (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram) (p : Args),
    result f bound high p = none ↔ familyCode p = none

def OriginalRawConditionalQueryEffectivity : Prop :=
  ∀ (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram),
    Computable f → Computable bound → Computable high → Computable (result f bound high)

def FullOriginalRawConditionalQuery : Prop :=
  ExactOriginalRawConditionalQuery ∧ ExactOriginalRawQueryFailure ∧
    OriginalRawConditionalQueryEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawConditionalQuery
