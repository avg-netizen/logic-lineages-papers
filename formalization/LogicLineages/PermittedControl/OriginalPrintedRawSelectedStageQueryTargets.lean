module
public import LogicLineages.PermittedControl.OriginalPrintedRawStageQueryTargets
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQuery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate Topological)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedRawFamilyFrontend (encodeInput)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open OriginalPrintedRawConditionalQuery (EverySuccessfulObservation)
open OriginalPrintedRawStageQuery (HighAtStage result ExactOriginalRawStageFailure)
open ActualBitFamilyRawDriver (HighProgram)
open ActualBitFamilyRawSemanticDriver (TypedHigh)

/-- Exactly the printed successful-domain query for a fixed selected
control and its actual threshold. The encoder is not a raw validator. -/
def ForControl (f : Nat → Nat) (B : Nat) : Prop :=
  (∀ (high : HighProgram) (children : TypedHigh), HighAtStage f B high children →
    ∀ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula),
      Topological known gs → PlainPreparedFormula p → ∀ positive : Bool,
        (result f B high (encodeInput known gs p positive) = some true ↔
          HasSuccessfulObservation f gs p positive) ∧
        (result f B high (encodeInput known gs p positive) = some false ↔
          ¬ HasSuccessfulObservation f gs p positive) ∧
        (result f B high (encodeInput known gs p (!positive)) = some false ↔
          EverySuccessfulObservation f gs p positive)) ∧
  ∀ high : HighProgram, Computable high → Computable (result f B high)

def ExactOriginalRawSelectedStageQuery : Prop :=
  ForControl factorialControl 0 ∧ ∀ b : Nat, ForControl (nearControl b) (b + 1)

def FullOriginalRawSelectedStageQuery : Prop :=
  ExactOriginalRawSelectedStageQuery ∧ ExactOriginalRawStageFailure

end LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQuery
