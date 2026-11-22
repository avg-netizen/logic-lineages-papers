module
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedNewCutoffLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedRankedLiteralHigh (cutoff)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalMatrixDenseRanks (support)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalPlainTerminalMatrix (accepts)
open OriginalMatrixLowDimension (dimension supportSet)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows HitRows)
open HeterogeneousSignedMatrixLowStrips (Branch branches)

def Residual (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (rs : List Row) : Prop :=
  ∃ suffix : Snapshot, actualRows f θ rs (passingList θ (circuit known gates p) ++ suffix) ∧
    accepts p positive suffix

def LowAt (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (prior : (Nat → Nat) → Prop) (name : Nat) : Prop :=
  let source := matrix known gates p
  let bound := cutoff B known gates p positive
  ∃ branch ∈ branches f name bound source, ∃ rs,
    branch.1 = θ name ∧ HitRows branch.2 rs ∧
    supportSet rs = (supportSet source).erase name ∧ dimension rs < dimension source ∧
    prior θ ∧ Residual f θ known gates p positive rs

def ExactPrintedNewCutoffLowAt : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (positive : Bool) (prior : (Nat → Nat) → Prop) (name : Nat),
      name ∈ support (matrix known gates p) → θ name < cutoff B known gates p positive →
        (prior θ ∧ SourceAccepts f θ known gates p positive ↔ LowAt f B θ known gates p positive prior name)

/-- At any literal original/hidden support name, every old coordinate
other than the chosen name remains unbounded, with unchanged prior
and shared exact original Boolean/graph snapshot. -/
def ExactPrintedNewCutoffLowStrips : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (positive : Bool) (prior : (Nat → Nat) → Prop) (name : Nat),
      let source := matrix known gates p
      let bound := cutoff B known gates p positive
      name ∈ support source →
      ((∃ a : Nat, a < bound ∧ let θ := Function.update ρ name a
          prior θ ∧ SourceAccepts f θ known gates p positive) ↔
        ∃ branch ∈ branches f name bound source, ∃ rs,
          HitRows branch.2 rs ∧ supportSet rs = (supportSet source).erase name ∧
          dimension rs < dimension source ∧
          let θ := Function.update ρ name branch.1
          prior θ ∧ Residual f θ known gates p positive rs)

def FullOriginalPrintedNewCutoffLow : Prop :=
  ExactPrintedNewCutoffLowAt ∧ ExactPrintedNewCutoffLowStrips

end LogicLineages.PermittedControl.OriginalPrintedNewCutoffLow
