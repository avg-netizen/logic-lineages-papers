module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixProjectedSupportTargets
public import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top table formula replay safeMinimum)
open OriginalMatrixLinearLowerTable (TopLinear)
open OriginalMatrixLowDimension (supportSet dimension)
open OriginalPrintedPlainMatrixProjectedSupport (argumentNames)
open OriginalProjectedMatrixSemantics (availabilityRows MatrixAccepts)
open OriginalProjectedMatrixDecode (decode)
open PreparedProjection (PlainPreparedFormula eliminatePreparedFormula)
open ActualFiniteOrderBranches (guard realized)
open HeterogeneousSignedMatrixSlice (Row)

/-- Close the exact existing initial already-linear projection back
into actual finite weighted row language. The used output formula and
unchanged lower table are exactly the returned packet, not arbitrary
caller-provided matrix rows. -/
def ExactOriginalResidualMatrixClosure : Prop :=
  ∀ (f θ : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      TopLinear (top branch) (renamed known gates p branch) →
      ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
        (∀ z : Nat, prior (replay θ known gates p branch z) ↔ prior θ) →
        let ranked := renamed known gates p branch
        let ops := table known gates p branch
        let bound := safeMinimum B θ known gates p branch
        let output := eliminatePreparedFormula (formula known gates p branch bound positive)
        ∃ rows : List Row, decode ops output = some rows ∧
          supportSet (availabilityRows ops ++ rows) = argumentNames ops ∧
          dimension (availabilityRows ops ++ rows) < dimension ranked ∧
          ((prior θ ∧ MatrixAccepts f (realized θ branch) ops output true rows) ↔
            ∃ z : Nat, bound ≤ z ∧ prior (replay θ known gates p branch z) ∧
              SourceAccepts f (replay θ known gates p branch z) known gates p positive)

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixResidualClosure
