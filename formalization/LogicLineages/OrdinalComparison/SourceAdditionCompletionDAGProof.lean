module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open SourceSortCompletion

theorem dag_correct (k : Nat) :
    (binaryDAG k).gates ≤ 2 * (Nat.log2 k + 1) ∧
    ∀ y : Nat, (binaryDAG k).Run y ↔ y = k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 2
    · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;>
        simp [binaryDAG, BinaryDAG.gates, BinaryDAG.Run]
    · have hdiv : k / 2 < k := Nat.div_lt_self (by omega) (by omega)
      have child := ih (k / 2) hdiv
      have hn : k >>> 1 ≠ 0 := by simp only [Nat.shiftRight_eq_div_pow]; omega
      have hlog : Nat.log2 k = Nat.log2 (k / 2) + 1 := by
        simpa only [Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.succ_eq_add_one] using
          Nat.log2_eq_succ_log2_shiftRight hn
      have hrem := Nat.mod_add_div k 2
      rw [binaryDAG, dif_neg hk]
      split_ifs with hmod
      · constructor
        · simp only [BinaryDAG.gates]
          omega
        · intro y
          simp only [BinaryDAG.Run, child.2, add_values]
          constructor
          · rintro ⟨x, rfl, hy⟩
            omega
          · intro hy
            exact ⟨k / 2, rfl, by omega⟩
      · constructor
        · simp only [BinaryDAG.gates]
          omega
        · intro y
          simp only [BinaryDAG.Run, child.2, add_values]
          constructor
          · rintro ⟨x, z, rfl, hz, hy⟩
            omega
          · intro hy
            exact ⟨k / 2, 2 * (k / 2), rfl, by omega, by omega⟩

end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
