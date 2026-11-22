module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDenseRanksTargets
import LogicLineages.PermittedControl.ActualCoordinateRankChartProof
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDenseRanks
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows exactPlainTerminalSuffix)
open OriginalMatrixDenseRanks (support denseRows exactDenseMatrix)
open ActualCoordinateRankChart (rankValue exactDenseRankChart)
open HeterogeneousSignedMatrixSlice (Snapshot)

theorem exactPrintedDenseRankedMatrix : ExactPrintedDenseRankedMatrix := by
  intro f θ known gates p plain positive
  let original := matrix known gates p
  let gs := circuit known gates p
  have chart := exactDenseRankChart θ (support original)
  have dm := exactDenseMatrix f θ original
  have gate := exactNormalizedCircuitRows f θ gs
  have split (xs : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p)
      (passingList θ gs) xs gate.1
  refine ⟨chart.1,chart.2.2.2,?_,?_⟩
  · intro row hrow t ht
    have h : t.2.rank < ActualCoordinateRankChart.size θ (support original) :=
      dm.2.2.2.1 t.2.rank
        (List.mem_flatMap.mpr ⟨row,hrow,List.mem_map.mpr ⟨t,ht,rfl⟩⟩)
    change t.2.rank < ActualCoordinateRankChart.size θ (support original) ∧
      t.2.rank ≤ ActualCoordinateRankChart.size θ (support original) - 1
    exact ⟨h,by omega⟩
  · constructor
    · rintro ⟨graph,test⟩
      obtain ⟨xs,actual,accepted⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp test
      have whole := (split xs).mpr ⟨gate.2.mpr graph,actual⟩
      exact ⟨xs,(dm.2.2.2.2 _).mpr whole,accepted⟩
    · rintro ⟨xs,actual,accepted⟩
      obtain ⟨fields,test⟩ := (split xs).mp ((dm.2.2.2.2 _).mp actual)
      exact ⟨gate.2.mp fields,(exactPlainTerminalSuffix f θ p plain positive).mpr ⟨xs,test,accepted⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDenseRanks
