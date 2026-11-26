module
public import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts branches)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalMatrixDenseRanks (support renameRow)
open ActualFiniteOrderBranches (Pattern guard rename realized)
open OriginalPrintedTerminalBitClauses (BitRow clauses)
open OriginalRankedLiteralClauseHigh (familyNeed rankedPredecessor OriginalSetup SourceFamily highPackets)

noncomputable def rankedFamily (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) (branch : Pattern) : List (List BitRow) :=
  let ren := renameRow (rename branch)
  clauses ((OriginalNormalizedCircuitMatrix.rowsList (circuit known gates p)).map ren)
    ((OriginalPlainTerminalMatrix.rows p).map ren) p positive

/-- True source static cutoff over the full literal typed ranked family.
It is independent of any existing numerical valuation or realized branch. -/
noncomputable def cutoff (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool) : Nat :=
  (branches known gates p).foldr (fun branch n =>
    max (familyNeed B branch.1 (rankedFamily known gates p positive branch)) n) 0

noncomputable def chartMinimum (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (branch : Pattern) : Nat :=
  max (cutoff B known gates p positive) (rankedPredecessor (top branch) (realized θ branch))

def PaidSupport (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Prop :=
  ∀ name ∈ support (matrix known gates p), cutoff B known gates p positive ≤ θ name

def ExactRankedOriginalBoolSource : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p → ∀ (positive : Bool) (branch : Pattern),
      branch ∈ branches known gates p → (guard branch).eval θ → ∀ z : Nat,
        (SourceAccepts f (replay θ known gates p branch z) known gates p positive ↔
          SourceFamily f (Function.update (realized θ branch) (top branch) z)
            (rankedFamily known gates p positive branch))

def ExactOriginalChartFunding : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (positive : Bool), PaidSupport B θ known gates p positive →
    ∀ (branch : Pattern), branch ∈ branches known gates p → (guard branch).eval θ →
      let family := rankedFamily known gates p positive branch
      OriginalSetup B branch.1 (top branch) (realized θ branch) family ∧
      ∀ z : Nat, chartMinimum B θ known gates p positive branch ≤ z →
        OriginalRankedLiteralClauseHigh.highMinimum B branch.1 (top branch) (realized θ branch) family ≤ z ∧
        PaidSupport B (replay θ known gates p branch z) known gates p positive ∧
        (guard branch).eval (replay θ known gates p branch z)

/-- Exactly the whole named original computational graph and Boolean
suffix of this initial dense branch, with the actual branch minimum.
The exterior prior remains outside and needs explicit replay. -/
def ExactOriginalPrintedRankedHighProjection : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
    ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
      PlainPreparedFormula p → ∀ (positive : Bool), PaidSupport B θ known gates p positive →
      ∀ (branch : Pattern), branch ∈ branches known gates p → (guard branch).eval θ → 0 < branch.1 →
      ∀ prior : (Nat → Nat) → Prop,
        let minimum := chartMinimum B θ known gates p positive branch
        let family := rankedFamily known gates p positive branch
        (∀ z : Nat, minimum ≤ z → (prior (replay θ known gates p branch z) ↔ prior θ)) →
        ((prior θ ∧ ∃ q ∈ highPackets branch.1 (top branch) family,
           LowerHolds f (realized θ branch) (top branch) (project minimum q)) ↔
         ∃ z : Nat, minimum ≤ z ∧ prior (replay θ known gates p branch z) ∧
           SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def FullOriginalPrintedRankedLiteralHigh : Prop :=
  ExactRankedOriginalBoolSource ∧ ExactOriginalChartFunding ∧ ExactOriginalPrintedRankedHighProjection

end LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
