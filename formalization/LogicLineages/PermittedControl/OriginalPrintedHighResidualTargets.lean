module
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets
public import LogicLineages.PermittedControl.ActualLowerRankChartRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedHighResidual
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open ActualFiniteOrderBranches (Pattern guard realized)
open OriginalRankedLiteralClauseHigh (highPackets)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum rankedFamily PaidSupport)
open OriginalPrintedTerminalBitClauses (ClauseHolds)
open ActualLowerRankChartRows (lowerChart LowerChartCondition)
open ActualGreatestRouteResidual (Residual lowerFamily LowerMatrix rows)
open OriginalMatrixLowDimension (supportSet dimension)
open HeterogeneousSignedMatrixSlice (Row)

noncomputable def outcomes (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (branch : Pattern) : List Residual :=
  let family := rankedFamily known gates p positive branch
  lowerFamily (top branch) (chartMinimum B θ known gates p positive branch)
    (highPackets branch.1 (top branch) family)

def guardedRows (C greatest : Nat) (out : Residual) : List Row :=
  (lowerChart C greatest).map Prod.fst ++ rows out

def GuardedAccepts (f ρ : Nat → Nat) (C greatest : Nat) (out : Residual) : Prop :=
  ClauseHolds f ρ (lowerChart C greatest) ∧ LowerMatrix f ρ out

def ExactOriginalDenseLowerChart : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      (∀ rank ≤ top branch, rank ∈ supportSet (renamed known gates p branch)) ∧
      (PaidSupport B θ known gates p positive →
        LowerChartCondition (cutoff B known gates p positive) (top branch) (realized θ branch))

/-- Keep both the true lower-chart guard and the actual table domain of
the chosen residual, with unchanged positional Boolean terminal bits. -/
def ExactOriginalPrintedHighResidual : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      PlainPreparedFormula p → ∀ (positive : Bool), PaidSupport B θ known gates p positive →
      ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      ∀ prior : (Nat → Nat) → Prop,
        let C := cutoff B known gates p positive
        let minimum := chartMinimum B θ known gates p positive branch
        let rs := outcomes B θ known gates p positive branch
        (∀ z : Nat, minimum ≤ z → (prior (replay θ known gates p branch z) ↔ prior θ)) →
        (∀ out ∈ rs, supportSet (guardedRows C (top branch) out) ⊆
            (supportSet (renamed known gates p branch)).erase (top branch) ∧
          dimension (guardedRows C (top branch) out) < dimension (renamed known gates p branch)) ∧
        ((prior θ ∧ ∃ out ∈ rs, GuardedAccepts f (realized θ branch) C (top branch) out) ↔
          ∃ z : Nat, minimum ≤ z ∧ prior (replay θ known gates p branch z) ∧
            SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def FullOriginalPrintedHighResidual : Prop :=
  ExactOriginalDenseLowerChart ∧ ExactOriginalPrintedHighResidual

end LogicLineages.PermittedControl.OriginalPrintedHighResidual
