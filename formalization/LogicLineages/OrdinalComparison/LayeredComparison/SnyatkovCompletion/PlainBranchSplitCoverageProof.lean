module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitSmallProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchEliminationProof
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
open NormalForm PlainBranchSplit PlainLinearCleanup

theorem branchSoundness : PlainBranchSplitTargets.BranchSoundness := by
  intro p hp q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  rintro ⟨ν, h⟩
  obtain ⟨n, _, _, hn⟩ := (MaximalPlainBranchProof.actualExistentialBranch i p hp ν).mp h
  exact ⟨Function.update ν i n, hn⟩

theorem exhaustiveCoverage : PlainBranchSplitTargets.ExhaustiveCoverage := by
  classical
  intro p hp
  constructor
  · rintro ⟨ν, hv⟩
    by_cases hsmall : ∀ i ∈ p.variables, ν i < MaximalPlainBranch.cutoff p
    · exact Or.inl (all_small_complete p ν hsmall hv)
    · push_neg at hsmall
      obtain ⟨j, hj, hlarge⟩ := hsmall
      have hnonempty : p.variables.toFinset.Nonempty := ⟨j, List.mem_toFinset.mpr hj⟩
      obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image p.variables.toFinset ν hnonempty
      have himem : i ∈ p.variables := List.mem_toFinset.mp hi
      have hcut : MaximalPlainBranch.cutoff p ≤ ν i :=
        le_trans hlarge (hmax j (List.mem_toFinset.mpr hj))
      refine Or.inr ⟨MaximalPlainBranch.eliminate i p, List.mem_map.mpr ⟨i, himem, rfl⟩, ν, ?_⟩
      apply (MaximalPlainBranchProof.actualExistentialBranch i p hp ν).mpr
      refine ⟨ν i, hcut, ?_, ?_⟩
      · simpa only [Function.update_eq_self] using
          (fun j hj => hmax j (List.mem_toFinset.mpr hj))
      · simpa only [Function.update_eq_self] using hv
  · rintro (hsmall | ⟨q, hq, hsat⟩)
    · exact smallSoundness p ((actualSmallEvaluation p).mp hsmall)
    · exact branchSoundness p hp q hq hsat

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
