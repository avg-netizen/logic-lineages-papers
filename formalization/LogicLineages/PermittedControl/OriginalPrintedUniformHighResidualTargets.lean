module
public import LogicLineages.PermittedControl.OriginalPrintedHighResidualTargets
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum rankedFamily PaidSupport)
open OriginalPrintedHighResidual (guardedRows GuardedAccepts)
open ActualFiniteOrderBranches (Pattern guard realized)
open ActualGreatestRouteResidual (lowerFamily Residual LowerMatrix)
open ActualSymbolicPredecessorProjection (prepend)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open OriginalRankedLiteralClauseHigh (highPackets)
open OriginalMatrixLowDimension (supportSet dimension)

noncomputable def candidates (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern) : List Packet :=
  (highPackets branch.1 (top branch) (rankedFamily known gates p positive branch)).map (prepend (top branch))

/-- The high residual compiler takes no baseline. The original preceding
rank is retained as a symbolic bare operand, not a bound numeral. -/
noncomputable def outcomes (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern) : List Residual :=
  lowerFamily (top branch) (cutoff B known gates p positive) (candidates known gates p positive branch)

def ExactUniformHighProjectionTransport : Prop :=
  ∀ (f θ : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (branch : Pattern),
    ((∃ out ∈ outcomes B known gates p positive branch, LowerMatrix f (realized θ branch) out) ↔
      ∃ q ∈ highPackets branch.1 (top branch) (rankedFamily known gates p positive branch),
        LowerHolds f (realized θ branch) (top branch) (project (chartMinimum B θ known gates p positive branch) q))

def ExactOriginalPrintedUniformHighResidual : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      PlainPreparedFormula p → ∀ (positive : Bool), PaidSupport B θ known gates p positive →
      ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      ∀ prior : (Nat → Nat) → Prop,
        let C := cutoff B known gates p positive
        let minimum := chartMinimum B θ known gates p positive branch
        let rs := outcomes B known gates p positive branch
        (∀ z : Nat, minimum ≤ z → (prior (replay θ known gates p branch z) ↔ prior θ)) →
        (∀ out ∈ rs, supportSet (guardedRows C (top branch) out) ⊆
            (supportSet (renamed known gates p branch)).erase (top branch) ∧
          dimension (guardedRows C (top branch) out) < dimension (renamed known gates p branch)) ∧
        ((prior θ ∧ ∃ out ∈ rs, GuardedAccepts f (realized θ branch) C (top branch) out) ↔
          ∃ z : Nat, minimum ≤ z ∧ prior (replay θ known gates p branch z) ∧
            SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def FullOriginalPrintedUniformHighResidual : Prop :=
  ExactUniformHighProjectionTransport ∧ ExactOriginalPrintedUniformHighResidual

end LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
