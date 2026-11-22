module
public import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixTargets
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalTargets
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNormalization (normalized Holds)
open OriginalPrintedCircuitNormalizedTerminal (exterior)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows HitRows sliceRows)
open HeterogeneousSignedMatrixLowStrips (branches)

noncomputable def circuit (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) :=
  normalized (exterior known (.rows p)) gates

noncomputable def matrix (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) : List Row :=
  OriginalNormalizedCircuitMatrix.rowsList (circuit known gates p) ++
    OriginalPlainTerminalMatrix.rows p

/-- Whole infinite slices, not a finite bank. Every original and hidden
coordinate other than the chosen original input remains as supplied by ρ.
The inherited guard and positive computational prefix do not change polarity. -/
def ExactPrintedPlainInfiniteLow : Prop :=
  ∀ (f ρ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ (rank bound : Nat), rank ∈ known → ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
      (∃ a : Nat, a < bound ∧ let θ := Function.update ρ rank a
        prior θ ∧ Holds f θ (circuit known gates p) ∧
          (OriginalMixedTerminalTest.Test.rows p).atPolarity positive θ) ↔
      ∃ branch residual,
        branch ∈ branches f rank bound (matrix known gates p) ∧ HitRows branch.2 residual ∧
        let θ := Function.update ρ rank branch.1
        prior θ ∧ ∃ testValues : Snapshot,
          actualRows f θ residual
            (OriginalNormalizedCircuitMatrix.passingList θ (circuit known gates p) ++ testValues) ∧
          OriginalPlainTerminalMatrix.accepts p positive testValues

def ExactPrintedPlainResidualOperands : Prop :=
  ∀ (f : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (rank a : Nat) (residual : List Row),
    HitRows (sliceRows f rank a (matrix known gates p)) residual →
    residual.map Prod.fst = (matrix known gates p).map Prod.fst ∧
    residual.map (fun r => r.2.2) =
      (matrix known gates p).map (fun r => SignedRowCoordinateSlice.untouched rank r.2.2)

def FullOriginalPrintedPlainMatrixInfiniteLow : Prop :=
  ExactPrintedPlainInfiniteLow ∧ ExactPrintedPlainResidualOperands

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLow
