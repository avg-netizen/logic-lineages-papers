module
public import LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartitionTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
open ActualFiniteOrderBranches (Entry rename realized exactPatternEnumeration exactBranchRealization)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalPrintedPlainMatrixLinearProjection (top replay updatedTies)
open OriginalMatrixDenseRanks (support)
open OriginalRankedLiteralClauseHigh (rankedPredecessor)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum)

theorem exactActualGreatestPaysChart : ExactActualGreatestPaysChart := by
  intro B θ known gates p positive nonempty paid branch member ordered z
  let names := support (matrix known gates p)
  let greatest := top branch
  let base := realized θ branch
  obtain ⟨_,keys,bounds,onto⟩ := (exactPatternEnumeration names branch).mp member
  obtain ⟨strict,slots,ties⟩ := exactBranchRealization θ names branch member ordered
  have width : 0 < branch.1 := by
    cases h : branch.2 with
    | nil =>
      apply False.elim
      exact nonempty (keys.symm.trans (by rw [h]; rfl))
    | cons e es =>
      have present : e ∈ branch.2 := by
        rw [h]
        exact List.mem_cons_self
      exact (Nat.zero_le e.2).trans_lt (bounds e present)
  have chosen : greatest < branch.1 := by
    change branch.1 - 1 < branch.1
    omega
  obtain ⟨e,found,atGreatest⟩ := onto greatest chosen
  have named : e.1 ∈ names := by
    rw [← keys]
    exact List.mem_map.mpr ⟨e,found,rfl⟩
  have fromSupport : cutoff B known gates p positive ≤ z := by
    change cutoff B known gates p positive ≤ realized θ branch greatest
    rw [← atGreatest,(slots e found).2]
    exact paid e.1 named
  have pred : rankedPredecessor greatest base ≤ z := by
    by_cases empty : greatest = 0
    · simp [rankedPredecessor,empty]
    · rw [rankedPredecessor,if_neg empty]
      have lt : greatest-1 < greatest := by omega
      exact Nat.succ_le_of_lt (strict lt)
  refine ⟨width,max_le fromSupport pred,?_⟩
  funext name
  by_cases memberName : name ∈ names
  · have actual := updatedTies θ known gates p branch member ordered z name memberName
    change Function.update base greatest (base greatest) (rename branch name) =
      replay θ known gates p branch z name at actual
    rw [Function.update_eq_self] at actual
    exact actual.symm.trans (ties name memberName).2
  · have no : ¬ (name ∈ support (matrix known gates p) ∧ rename branch name = top branch) :=
      fun pair => memberName pair.1
    simp only [replay,if_neg no]

end LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
