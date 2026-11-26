module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTapeProof
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranches
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows exactPlainTerminalSuffix)
open OriginalMatrixDenseRanks (support renameTerm renameRow exactRenamedOperand exactRenamedMatrix)
open ActualFiniteOrderBranches (rename realized actualPattern exactActualBranchCoverage exactBranchRealization)
open HeterogeneousSignedMatrixSlice (Snapshot)

theorem exactPrintedOrderBranch : ExactPrintedOrderBranch := by
  intro f θ known gates p plain positive branch member checked
  let original := matrix known gates p
  let gs := circuit known gates p
  obtain ⟨strict,_,ties⟩ := exactBranchRealization θ (support original) branch member checked
  have transport := exactRenamedMatrix f θ (realized θ branch) (rename branch) original
    (fun n hn => (ties n hn).2)
  have gate := exactNormalizedCircuitRows f θ gs
  have split (xs : Snapshot) :=
    AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p)
      (passingList θ gs) xs gate.1
  refine ⟨strict,?_,?_⟩
  · intro row hrow t ht
    change row ∈ original.map (renameRow (rename branch)) at hrow
    obtain ⟨r,hr,hEq⟩ := List.mem_map.mp hrow
    subst row
    change t ∈ r.2.2.map (renameTerm (rename branch)) at ht
    obtain ⟨u,hu,hTerm⟩ := List.mem_map.mp ht
    subst t
    have src : u.2.rank ∈ support original :=
      List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨u,hu,rfl⟩⟩
    have eq := (exactRenamedOperand f θ (realized θ branch) (rename branch) u.2
      (ties _ src).2).1
    have hlt : rename branch u.2.rank < branch.1 := (ties _ src).1
    change (OriginalMatrixDenseRanks.renameOperand (rename branch) u.2).rank < branch.1 ∧
      (OriginalMatrixDenseRanks.renameOperand (rename branch) u.2).rank ≤ branch.1 - 1
    rw [eq]
    exact ⟨hlt,by omega⟩
  · constructor
    · rintro ⟨graph,polarity⟩
      obtain ⟨xs,rs,accepted⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp polarity
      exact ⟨xs,(transport _).mpr ((split xs).mpr ⟨gate.2.mpr graph,rs⟩),accepted⟩
    · rintro ⟨xs,ranked,accepted⟩
      obtain ⟨graph,rs⟩ := (split xs).mp ((transport _).mp ranked)
      exact ⟨gate.2.mp graph,(exactPlainTerminalSuffix f θ p plain positive).mpr ⟨xs,rs,accepted⟩⟩

theorem exactPrintedOrderBranchesCover : ExactPrintedOrderBranchesCover := by
  intro f θ known gates p plain prior positive
  constructor
  · rintro ⟨hp,source⟩
    let names := support (matrix known gates p)
    let branch := actualPattern θ names
    obtain ⟨member,checked⟩ := exactActualBranchCoverage θ names
    have branchExact := exactPrintedOrderBranch f θ known gates p plain positive branch member checked
    exact ⟨branch,member,checked,hp,branchExact.2.2.mp source⟩
  · rintro ⟨branch,member,guard,priorAt,order⟩
    have branchExact := exactPrintedOrderBranch f θ known gates p plain positive branch member guard
    exact ⟨priorAt,branchExact.2.2.mpr order⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranches
