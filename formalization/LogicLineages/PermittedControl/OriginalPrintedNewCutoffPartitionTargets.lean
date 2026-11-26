module
public import LogicLineages.PermittedControl.OriginalPrintedNewCutoffLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts branches)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalMatrixDenseRanks (support)
open ActualFiniteOrderBranches (Pattern guard realized)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalRankedLiteralClauseHigh (highPackets)
open OriginalPrintedRankedLiteralHigh (cutoff PaidSupport rankedFamily chartMinimum)
open OriginalPrintedNewCutoffLow (LowAt)

def HasLow (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (prior : (Nat → Nat) → Prop) : Prop :=
  ∃ name ∈ support (matrix known gates p), θ name < cutoff B known gates p positive ∧
    LowAt f B θ known gates p positive prior name

def HighAt (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (prior : (Nat → Nat) → Prop) : Prop :=
  support (matrix known gates p) ≠ [] ∧ PaidSupport B θ known gates p positive ∧ prior θ ∧
    ∃ branch ∈ branches known gates p, (guard branch).eval θ ∧
      ∃ q ∈ highPackets branch.1 (top branch) (rankedFamily known gates p positive branch),
        PacketHolds f (realized θ branch) (top branch) (realized θ branch (top branch)) q

def ZeroAt (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (prior : (Nat → Nat) → Prop) : Prop :=
  support (matrix known gates p) = [] ∧ prior θ ∧ SourceAccepts f θ known gates p positive

def ExactActualGreatestPaysChart : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool), support (matrix known gates p) ≠ [] → PaidSupport B θ known gates p positive →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      let z := realized θ branch (top branch)
      0 < branch.1 ∧ chartMinimum B θ known gates p positive branch ≤ z ∧
        replay θ known gates p branch z = θ

/-- Exact decomposition at the new typed cutoff. No ranking or phantom
top payment is made in the separate genuinely zero-support branch. -/
def ExactOriginalPrintedNewCutoffPartition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      PlainPreparedFormula p →
      ∀ (positive : Bool) (prior : (Nat → Nat) → Prop),
        ((prior θ ∧ SourceAccepts f θ known gates p positive) ↔
          HasLow f B θ known gates p positive prior ∨ HighAt f B θ known gates p positive prior ∨
            ZeroAt f θ known gates p positive prior)

def FullOriginalPrintedNewCutoffPartition : Prop :=
  ExactActualGreatestPaysChart ∧ ExactOriginalPrintedNewCutoffPartition

end LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
