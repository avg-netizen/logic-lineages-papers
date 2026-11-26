module
public import LogicLineages.PermittedControl.OriginalPrintedHighResidualTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedHighResidual
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixDenseRanks (support renameRow renameTerm)
open OriginalMatrixLowDimension (supportSet)
open ActualFiniteOrderBranches (rename realized exactPatternEnumeration exactBranchRealization)
open ActualLowerRankChartRows (LowerChartCondition)
open OriginalPrintedRankedLiteralHigh (cutoff)
open HeterogeneousSignedMatrixSlice (Row)
open MixedSameRankResidue (WeightedOperand)

private theorem renamedSupport (tag : Nat → Nat) (rs : List Row) :
    support (rs.map (renameRow tag)) = (support rs).map tag := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have one :
        ((r.2.2.map (renameTerm tag)).map (fun t => t.2.rank)) =
          ((r.2.2.map (fun t => t.2.rank)).map tag) := by
      simp only [List.map_map]
      apply congrArg (fun u : WeightedOperand → Nat => r.2.2.map u)
      funext t
      rcases t with ⟨w,op⟩
      cases op <;> rfl
    change ((r.2.2.map (renameTerm tag)).map (fun t => t.2.rank)) ++
        support (rs.map (renameRow tag)) =
      (((r.2.2.map (fun t => t.2.rank)) ++ support rs).map tag)
    rw [ih,List.map_append,one]

theorem exactOriginalDenseLowerChart : ExactOriginalDenseLowerChart := by
  intro B θ known gates p positive branch member ordered nonempty
  let source := matrix known gates p
  let names := support source
  obtain ⟨_,keys,_,onto⟩ := (exactPatternEnumeration names branch).mp member
  obtain ⟨strict,slots,_⟩ := exactBranchRealization θ names branch member ordered
  have existsRaw (rank : Nat) (bounded : rank ≤ top branch) :
      ∃ name ∈ names, rename branch name = rank ∧ realized θ branch rank = θ name := by
    have within : rank < branch.1 := by
      change rank ≤ branch.1-1 at bounded
      omega
    obtain ⟨e,used,atRank⟩ := onto rank within
    have original : e.1 ∈ names := by
      rw [← keys]
      exact List.mem_map.mpr ⟨e,used,rfl⟩
    have real := slots e used
    refine ⟨e.1,original,real.1.trans atRank,?_⟩
    rw [← atRank]
    exact real.2
  refine ⟨?_,?_⟩
  · intro rank bounded
    obtain ⟨name,used,tag,_⟩ := existsRaw rank bounded
    apply List.mem_toFinset.mpr
    change rank ∈ support (source.map (renameRow (rename branch)))
    rw [renamedSupport]
    exact List.mem_map.mpr ⟨name,used,tag⟩
  · intro paid
    refine ⟨?_,fun i j lt _ => strict lt⟩
    intro rank lt
    obtain ⟨name,used,_,value⟩ := existsRaw rank lt.le
    rw [value]
    exact paid name used

end LogicLineages.PermittedControl.OriginalPrintedHighResidual
