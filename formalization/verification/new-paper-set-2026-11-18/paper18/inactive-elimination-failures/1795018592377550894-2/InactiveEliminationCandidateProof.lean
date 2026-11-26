module
public import LogicLineages.StandardControlCurrent.InactiveEliminationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationCandidateProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination

/-- Positivity is derived from the literal product, including the empty formula. -/
theorem period_positive (u : LinearRows.UnitFormula) : 0 < LinearRows.period u := by
  unfold LinearRows.period
  induction u.atoms with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (by cases a <;> simp [LinearRows.UnitAtom.period]) ih

/-- The actual finite list contains rows, not values chosen at a valuation. -/
theorem candidate_formula (u : LinearRows.UnitFormula) :
    LinearRows.unitEliminate u =
      BoundedRows.any ((candidates u).map (LinearRows.instantiate (LinearRows.guarded u))) := by
  simp only [LinearRows.unitEliminate, candidates, List.map_flatMap, List.map_map,
    Function.comp_def]

theorem candidateCompleteness : InactiveEliminationTargets.CandidateCompleteness := by
  intro u ν
  refine ⟨period_positive u, ?_⟩
  rw [← LinearRowsSemanticProof.actualUnitElimination u ν, candidate_formula,
    BoundedRowsSemanticProof.any_eval]
  simp only [List.mem_map, exists_exists_and_eq_and]
end LogicLineages.StandardControlCurrent.InactiveEliminationCandidateProof
