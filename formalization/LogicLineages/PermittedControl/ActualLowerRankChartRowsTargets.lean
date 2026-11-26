module
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets
public import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualLowerRankChartRows
open HeterogeneousSignedMatrixSlice (Row)
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds)
open ActualRankedNormalizationSyntax (LowerStrict)

def fundRow (B i : Nat) : BitRow := ((.nonnegative,-(B : Int),[(1,.coordinate i)]),true)

def risingRow (i : Nat) : BitRow :=
  ((.positive,0,[(1,.coordinate (i+1)),(-1,.coordinate i)]),true)

/-- Every constraint is a positive linear row on the unchanged genuine
lower raw ranks. Top=0 produces no row or phantom preceding coordinate. -/
def lowerChart (B top : Nat) : List BitRow :=
  ((List.range top).map (fundRow B)) ++ ((List.range (top-1)).map risingRow)

def LowerChartCondition (B top : Nat) (ρ : Nat → Nat) : Prop :=
  (∀ i < top, B ≤ ρ i) ∧ LowerStrict ρ top

def ExactLowerRankChartRows : Prop :=
  ∀ (f ρ : Nat → Nat) (B top : Nat),
    (ClauseHolds f ρ (lowerChart B top) ↔ LowerChartCondition B top ρ) ∧
    ∀ row ∈ lowerChart B top, row.2 = true ∧ ∀ t ∈ row.1.2.2, t.2.rank < top

end LogicLineages.PermittedControl.ActualLowerRankChartRows
