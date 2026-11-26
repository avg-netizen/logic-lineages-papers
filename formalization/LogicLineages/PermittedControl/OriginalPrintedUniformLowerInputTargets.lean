module
public import LogicLineages.PermittedControl.ActualRankChartPrototypeTargets
public import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedUniformLowerInput
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalMatrixDenseRanks (support)
open ActualFiniteOrderBranches (Pattern)
open ActualLowerRankChartRows (LowerChartCondition)
open ActualRankChartPrototype (Consistent readWithin seed)
open OriginalPrintedRankedLiteralHigh (cutoff)
open OriginalPrintedHighResidual (guardedRows GuardedAccepts)
open OriginalPrintedUniformHighResidual (outcomes)
open OriginalMatrixLowDimension (supportSet dimension)

/-- Uniform high programs apply to arbitrary genuine lower raw values,
not just the lower coordinates of an independently supplied old source
valuation. Outside-support data is explicit and never changed. -/
def ExactOriginalPrintedUniformLowerInput : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (known : List Nat) (gates : List Gate) (p : NormalForm.Formula), PlainPreparedFormula p →
      ∀ (positive : Bool) (branch : Pattern),
        branch ∈ branches known gates p → 0 < branch.1 → Consistent branch →
        ∀ (lower outside : Nat → Nat),
          let C := cutoff B known gates p positive
          let names := support (matrix known gates p)
          let raw := readWithin names branch lower outside
          LowerChartCondition C (top branch) lower →
          ∀ prior : (Nat → Nat) → Prop,
            let minimum := seed C branch lower
            (∀ z : Nat, minimum ≤ z → (prior (raw z) ↔ prior (raw minimum))) →
            ((prior (raw minimum) ∧ ∃ out ∈ outcomes B known gates p positive branch,
                GuardedAccepts f lower C (top branch) out) ↔
              ∃ z : Nat, minimum ≤ z ∧ prior (raw z) ∧ SourceAccepts f (raw z) known gates p positive)

end LogicLineages.PermittedControl.OriginalPrintedUniformLowerInput
