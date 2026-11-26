module
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionTargets
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsSemanticsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLowDimension
open HeterogeneousSignedMatrixSlice (Row residualRowsExact)
open HeterogeneousSignedMatrixLowStrips (exactBranch)
open OriginalMatrixDenseRanks (support)
open MixedSameRankResidue (WeightedOperand)
open SignedRowCoordinateSlice (untouched)

private def flatten (tss : List (List WeightedOperand)) : List Nat :=
  tss.flatMap (List.map (fun t => t.2.rank))

private theorem supportFlatten (rows : List Row) :
    flatten (rows.map (fun r => r.2.2)) = support rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      change r.2.2.map (fun t => t.2.rank) ++ flatten (rows.map (fun row => row.2.2)) =
        r.2.2.map (fun t => t.2.rank) ++ support rows
      rw [ih]

private theorem termRanks (rank : Nat) (ts : List WeightedOperand) :
    (untouched rank ts).map (fun t => t.2.rank) =
      (ts.map (fun t => t.2.rank)).filter (fun k => decide (k ≠ rank)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      by_cases eq : t.2.rank = rank
      · simpa [untouched,eq] using ih
      · simpa [untouched,eq] using congrArg (List.cons t.2.rank) ih

private theorem flatUntouched (rank : Nat) (rows : List Row) :
    flatten (rows.map (fun r => untouched rank r.2.2)) =
      (support rows).filter (fun k => decide (k ≠ rank)) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      change (untouched rank r.2.2).map (fun t => t.2.rank) ++
          flatten (rows.map (fun row => untouched rank row.2.2)) =
        (r.2.2.map (fun t => t.2.rank) ++ support rows).filter (fun k => decide (k ≠ rank))
      rw [List.filter_append,termRanks,ih]

theorem exactResidualSupportErase : ExactResidualSupportErase := by
  intro f rank a source residual hits
  obtain ⟨tests,terms⟩ := residualRowsExact f rank a source residual hits
  have names : support residual = (support source).filter (fun k => decide (k ≠ rank)) := by
    rw [← supportFlatten residual,terms,flatUntouched]
  refine ⟨tests,terms,names,?_⟩
  unfold supportSet
  rw [names]
  apply Finset.ext
  intro k
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_erase,and_comm]

theorem exactLowFamilyDimension : ExactLowFamilyDimension := by
  intro f rank bound source used branch member residual hits
  have eq := ((exactBranch f rank bound source branch).mp member).2
  rw [eq] at hits
  have erase := (exactResidualSupportErase f rank branch.1 source residual hits).2.2.2
  refine ⟨erase,?_⟩
  change (supportSet residual).card < (supportSet source).card
  rw [erase]
  exact Finset.card_erase_lt_of_mem (List.mem_toFinset.mpr used)

end LogicLineages.PermittedControl.OriginalMatrixLowDimension
