module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphPlainnessProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDecisionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
open CommonLayerSyntax SourceBooleanGraph

theorem exactDecisionDomain : SourceBooleanGraphTargets.ExactDecisionDomain := by
  intro p
  by_cases h : test p = true
  · simp [decideExists, decideForall, test, h]
  · simp [decideExists, decideForall, test, h, Bool.eq_false_iff.mpr h]

theorem actualExistentialDecision : SourceBooleanGraphTargets.ActualExistentialDecision := by
  intro p hp b
  have hs := (PlainFrontierProof.actualDecision (compile p) (plainCompiledMatrix p (start p))).trans
    (actualSatisfiabilityTranslation p hp)
  simp only [decideExists, if_pos hp, Option.some.injEq]
  cases hb : PlainFrontier.answer (compile p) <;> cases b <;> simp_all

theorem actualUniversalDecision : SourceBooleanGraphTargets.ActualUniversalDecision := by
  classical
  intro p hp b
  have hneg : test (.negative p) = true := hp
  have hs := (actualExistentialDecision (.negative p) hneg
    (PlainFrontier.answer (compile (.negative p)))).mp (by simp [decideExists, hneg])
  have hnot : (∀ ν : Nat → Nat, p.eval ν) ↔ PlainFrontier.answer (compile (.negative p)) = false := by
    have hn := not_congr hs
    simpa only [SourceFormula.eval, not_exists, not_not, Bool.not_eq_true] using hn
  simp only [decideForall, decideExists, if_pos hneg, Option.map_some]
  cases hc : PlainFrontier.answer (compile (.negative p)) <;> cases b <;> simp_all

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphProof
