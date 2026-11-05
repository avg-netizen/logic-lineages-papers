module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitCoverageProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
open NormalForm PlainBranchSplit PlainLinearCleanup

theorem actualStep : PlainBranchSplitTargets.ActualStep := by
  intro p hp
  exact (PlainLinearCleanupProof.actualSatisfiabilityCleanup p).symm.trans
    (exhaustiveCoverage (cleanup p) (PlainLinearCleanupProof.preservePlain p hp))

theorem strictFrontierDecrease : PlainBranchSplitTargets.StrictFrontierDecrease := by
  intro p q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have hn : i ∈ PlainBranchProvenance.nonlinearNames (cleanup p) := by
    by_contra hn
    have ht : LinearRows.isLinear i (cleanup p) = true := by
      apply (PlainBranchProvenanceProof.exactLinearityDetection i (cleanup p)).mpr
      intro s hs he
      apply hn
      exact (PlainBranchProvenanceProof.mem_nonlinearNames _ i).mpr ⟨s, hs, he⟩
    rw [PlainLinearCleanupProof.noLinearNames p i hi] at ht
    cases ht
  have h := PlainBranchProvenanceProof.strictNameDecrease i (cleanup p) hn
  rw [PlainLinearCleanupProof.exactNonlinearNames p] at h
  exact h

theorem preservePlain : PlainBranchSplitTargets.PreservePlain := by
  intro p hp q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  exact PlainBranchProvenanceProof.preservePlain i (cleanup p)
    (PlainLinearCleanupProof.preservePlain p hp)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchSplitProof
