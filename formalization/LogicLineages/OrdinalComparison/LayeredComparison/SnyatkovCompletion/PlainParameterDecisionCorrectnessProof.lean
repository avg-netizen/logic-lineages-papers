module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDecisionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
open NormalForm PlainParameterDecision

theorem exactDecisionDomains : PlainParameterDecisionTargets.ExactDecisionDomains := by
  intro xs values p
  have hn : MaximalPlainBranch.isPlain (.negative p) = MaximalPlainBranch.isPlain p := rfl
  by_cases hp : MaximalPlainBranch.isPlain p = true
  · simp [decideExists, decideForall, hn, hp]
  · simp [decideExists, decideForall, hn, hp, Bool.eq_false_iff.mpr hp]

theorem existsDecision_correct (xs values : List Nat) (p : Formula)
    (hp : MaximalPlainBranch.isPlain p = true) (b : Bool) :
    decideExists xs values p = some b ↔ (existsPrefix (valuation values) xs p ↔ b = true) := by
  have hs := (PlainFrontierProof.actualDecision (frame xs values p) (preservePlain xs values p hp)).trans
    (actualParameterizedExistential xs values p)
  simp only [decideExists, if_pos hp, Option.some.injEq]
  cases hc : PlainFrontier.answer (frame xs values p) <;> cases b <;> simp_all

theorem forallDecision_correct (xs values : List Nat) (p : Formula)
    (hp : MaximalPlainBranch.isPlain p = true) (b : Bool) :
    decideForall xs values p = some b ↔ (forallPrefix (valuation values) xs p ↔ b = true) := by
  classical
  have hn : MaximalPlainBranch.isPlain (.negative p) = true := hp
  have hs := (existsDecision_correct xs values (.negative p) hn
    (PlainFrontier.answer (frame xs values (.negative p)))).mp (by simp [decideExists, hn])
  have hnot : forallPrefix (valuation values) xs p ↔
      PlainFrontier.answer (frame xs values (.negative p)) = false := by
    rw [forallPrefix_not_exists]
    simpa only [Bool.not_eq_true] using not_congr hs
  simp only [decideForall, decideExists, if_pos hn, Option.map_some]
  cases hc : PlainFrontier.answer (frame xs values (.negative p)) <;> cases b <;> simp_all

theorem actualDecisions : PlainParameterDecisionTargets.ActualDecisions :=
  fun xs values p hp b => ⟨existsDecision_correct xs values p hp b, forallDecision_correct xs values p hp b⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionProof
