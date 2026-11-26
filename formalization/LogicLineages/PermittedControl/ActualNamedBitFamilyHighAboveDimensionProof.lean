module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveTargets
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof
import LogicLineages.PermittedControl.ActualBitFamilyHighUniformProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesProof
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
open ActualGuardedResidualBitFamily (Family exactGuardedResidualUnion)
open ActualBitFamilyLowSlices (coordinates coordinateClause originalRows dimension)
open ActualFiniteOrderBranches (Pattern exactPatternEnumeration)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedHighResidual (guardedRows)
open ActualGreatestRouteResidual (Residual rows exactActualLowerRouteFamily)
open OriginalRankedLiteralClauseHigh (highPackets)
open ActualSymbolicPredecessorProjection (prepend)
open ActualLowerRankChartRows (lowerChart exactLowerRankChartRows)
open OriginalMatrixLowDimension (supportSet)

open ActualBitFamilyHigh (ranked amendedShapes)
open ActualNamedBitFamilyHigh (exactNamedCharts checkedLength)

private theorem guardedBelow (C greatest : Nat) (out : Residual)
    (lower : ∀ k ∈ supportSet (rows out), k < greatest) :
    ∀ k ∈ supportSet (guardedRows C greatest out), k < greatest := by
  intro k used
  obtain ⟨r,member,ranked⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
  rcases List.mem_append.mp member with chart | residual
  · obtain ⟨row,atChart,rfl⟩ := List.mem_map.mp chart
    obtain ⟨term,seen,rfl⟩ := List.mem_map.mp ranked
    exact ((exactLowerRankChartRows (fun _ => 0) (fun _ => 0) C greatest).2 row atChart).2 term seen
  · exact lower k (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨r,residual,ranked⟩))

theorem exactAboveHighDimension : ExactAboveHighDimension := by
  intro C family names supplied result member
  obtain ⟨p,listed,rfl⟩ := List.mem_map.mp member
  let greatest := top p
  let qs := (highPackets p.1 greatest (ranked p family)).map (prepend greatest)
  let childFamily := child C family p
  have good := (exactNamedCharts names p).mp listed
  have width : p.1 ≤ dimension family := by
    have chart := ((exactPatternEnumeration names p).mp good.1).1
    rw [← checkedLength family names supplied]
    exact chart
  have core := (exactActualLowerRouteFamily (fun _ => 0) (fun _ => 0) greatest C qs (amendedShapes p family)).1
  have source := (exactGuardedResidualUnion (fun _ => 0) (fun _ => 0) C greatest (outputs C family p)).1
  have scope (k : Nat) (inUnion : k ∈ coordinates childFamily) : k < greatest := by
    obtain ⟨clause,member,atClause⟩ := (coordinateClause childFamily k).mp inUnion
    obtain ⟨out,used,exactOut⟩ := source clause member
    change clause.map Prod.fst = guardedRows C greatest out at exactOut
    change k ∈ supportSet (clause.map Prod.fst) at atClause
    rw [exactOut] at atClause
    exact guardedBelow C greatest out (core out used) k atClause
  have subset : coordinates childFamily ⊆ Finset.range greatest :=
    fun k member => Finset.mem_range.mpr (scope k member)
  have bound : dimension childFamily ≤ greatest := by
    simpa only [Finset.card_range] using Finset.card_le_card subset
  have lower : greatest < p.1 := by
    have pos := good.2.1
    change p.1-1 < p.1
    omega
  exact ⟨scope,bound.trans_lt (lower.trans_le width)⟩

end LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
