module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchEliminationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainProof
open NormalForm SingleNamePlain

theorem exactFragmentTest : SingleNamePlainTargets.ExactFragmentTest := by
  intro i p
  simp only [admissible, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]

theorem actualExistentialElimination : SingleNamePlainTargets.ActualExistentialElimination := by
  intro i p hp ν
  obtain ⟨hplain, hnames⟩ := (exactFragmentTest i p).mp hp
  change (BoundedRows.bounded i (MaximalPlainBranch.cutoff p) p).eval ν ∨
    (MaximalPlainBranch.eliminate i p).eval ν ↔ _
  rw [BoundedRowsSemanticProof.actualBoundedElimination,
    MaximalPlainBranchProof.actualExistentialBranch i p hplain ν]
  constructor
  · rintro (⟨n, _, hn⟩ | ⟨n, _, _, hn⟩) <;> exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    by_cases hc : n < MaximalPlainBranch.cutoff p
    · exact Or.inl ⟨n, hc, hn⟩
    · refine Or.inr ⟨n, Nat.le_of_not_gt hc, ?_, hn⟩
      intro j hj
      simpa only [hnames j hj, Function.update_self] using (Nat.le_refl n)

theorem actualUniversalElimination : SingleNamePlainTargets.ActualUniversalElimination := by
  intro i p hp ν
  have hneg : admissible i (.negative p) = true := hp
  change (¬(existsEliminate i (.negative p)).eval ν) ↔ _
  rw [actualExistentialElimination i (.negative p) hneg ν]
  simp only [Formula.eval, not_exists, not_not]

private theorem exists_removed (i : Nat) (p : Formula) : i ∉ (existsEliminate i p).variables := by
  intro h
  rcases List.mem_append.mp h with h | h
  · have hh := (BoundedRowsSemanticProof.exactBoundedSupport i (MaximalPlainBranch.cutoff p) p i).mp h
    exact hh.2.1 rfl
  · exact MaximalPlainBranchProof.exactRemovedName i p h

theorem exactRemovedName : SingleNamePlainTargets.ExactRemovedName :=
  fun i p => ⟨exists_removed i p, exists_removed i (.negative p)⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainProof
