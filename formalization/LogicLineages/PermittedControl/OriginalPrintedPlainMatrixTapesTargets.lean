module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets
public import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixTapes
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNormalization (Holds)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open HeterogeneousSignedMatrixSlice (Snapshot)
open ActualReadChargeIteration (ReadState)
open OriginalMixedTerminalTest (Test)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalMatrixActualReadTape (guardedStates)

/-- The actual original normalized graph together with its original
terminal polarity gives exactly the read-state tape for every emitted
row. The canonical positive prefix is identical at either polarity. -/
def ExactPrintedPlainMatrixTapes : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ positive : Bool,
    (Holds f θ (circuit known gates p) ∧ (Test.rows p).atPolarity positive θ) ↔
      ∃ (suffix : Snapshot) (states : List ReadState),
        guardedStates f θ (matrix known gates p) (passingList θ (circuit known gates p) ++ suffix)
          states ∧ OriginalPlainTerminalMatrix.accepts p positive suffix

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixTapes
