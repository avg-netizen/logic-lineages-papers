module
public import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedWindowNumeralGraphTargets

theorem exact_NumeralGraph : NumeralGraph := by
  intro n p v body α Γ
  obtain ⟨d⟩ := ID1Completion.InternalNumeralEvaluationProof.actualOriginalNumeralEvaluation body n p v α
  exact ⟨ID1Completion.InternalCalculus.Derivation.weakening (by simp) d⟩

#print axioms exact_NumeralGraph
end LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
