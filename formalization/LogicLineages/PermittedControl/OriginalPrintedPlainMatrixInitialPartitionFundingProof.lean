module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartitionTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesEnumerateProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
open ActualFiniteOrderBranches (Entry exactPatternEnumeration exactBranchRealization)

theorem exactActualRankZeroFunding : ExactActualRankZeroFunding := by
  intro B θ known gates p large branch member checked
  obtain ⟨_,keys,bounds,onto⟩ := (exactPatternEnumeration (names known gates p) branch).mp member
  have hpos : 0 < branch.1 := by
    cases h : branch.2 with
    | nil =>
        have empty : branch.2.map Prod.fst = [] := by simp only [h,List.map_nil]
        exact (large.1 (keys.symm.trans empty)).elim
    | cons e es =>
        have present : e ∈ branch.2 := by
          simpa only [h] using (List.mem_cons_self : e ∈ e :: es)
        exact (Nat.zero_le e.2).trans_lt (bounds e present)
  obtain ⟨e,present,zero⟩ := onto 0 hpos
  have namePresent : e.1 ∈ names known gates p := by
    rw [← keys]
    exact List.mem_map.mpr ⟨e,present,rfl⟩
  have real := (exactBranchRealization θ (names known gates p) branch member checked).2.1 e present
  rw [← zero,real.2]
  exact large.2 e.1 namePresent

theorem exactThreeStrata : ExactThreeStrata := by
  intro B θ known gates p
  classical
  refine ⟨?_,?_,?_,fun h => h.1⟩
  · by_cases small : HasSmall B θ known gates p
    · exact Or.inl small
    · by_cases empty : names known gates p = []
      · exact Or.inr (Or.inr empty)
      · refine Or.inr (Or.inl ⟨empty,?_⟩)
        intro name member
        exact Nat.le_of_not_gt (fun below => small ⟨name,member,below⟩)
  · rintro ⟨name,member,below⟩ large
    exact (not_lt_of_ge (large.2 name member)) below
  · rintro ⟨name,member,_⟩ empty
    rw [empty] at member
    cases member

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
