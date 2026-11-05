module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchContextProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
open NormalForm MaximalPlainBranch

theorem actualExistentialBranch : MaximalPlainBranchTargets.ActualExistentialBranch := by
  intro i p hp ν
  unfold eliminate
  rw [LinearRowsSemanticProof.actualLinearElimination i (framed i p)
    (literalContextualLinearity i p hp) ν]
  apply exists_congr
  intro n
  change ((frame i p).eval (Function.update ν i n) ∧
    (compile i p).eval (Function.update ν i n)) ↔ _
  have hf := literalFrame i p (Function.update ν i n)
  simp only [Function.update_self] at hf
  rw [hf]
  constructor
  · rintro ⟨⟨hc, hm⟩, hv⟩
    exact ⟨hc, hm, (actualContextualCompilation i p hp (Function.update ν i n)
      (by simpa only [Function.update_self] using hc)
      (by simpa only [Function.update_self] using hm)).mp hv⟩
  · rintro ⟨hc, hm, hv⟩
    exact ⟨⟨hc, hm⟩, (actualContextualCompilation i p hp (Function.update ν i n)
      (by simpa only [Function.update_self] using hc)
      (by simpa only [Function.update_self] using hm)).mpr hv⟩

theorem exactRemovedName : MaximalPlainBranchTargets.ExactRemovedName := by
  intro i p hi
  have h := (LinearRowsSupportProof.exactOutputSupport i (framed i p) i).mp hi
  exact h.1 rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
