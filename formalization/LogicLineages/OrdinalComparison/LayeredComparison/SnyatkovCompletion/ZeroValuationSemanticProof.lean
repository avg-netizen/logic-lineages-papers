module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
open NormalForm ZeroValuation

theorem actualRowProjection : ZeroValuationTargets.ActualRowProjection := by
  intro r ν
  simp only [projectRow, rowValue, BoundedRows.valueAt, List.map_nil, List.sum_nil, add_zero]

theorem exactConstantProjection : ZeroValuationTargets.ExactConstantProjection := by
  intro p
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq => simp only [project, Formula.variables, ihp, ihq, List.nil_append]
  | disjunction p q ihp ihq => simp only [project, Formula.variables, ihp, ihq, List.nil_append]

private theorem atom_eval (a : Atom) (ν : Nat → Nat) :
    (projectAtom a).eval ν ↔ a.eval (fun _ => 0) := by
  cases a with
  | nonnegative r =>
      change (0 ≤ rowValue (projectRow r) ν) ↔ (0 ≤ rowValue r (fun _ => 0))
      rw [actualRowProjection r ν]
  | divisible m r =>
      change (((m + 1 : Nat) : Int) ∣ rowValue (projectRow r) ν) ↔
        (((m + 1 : Nat) : Int) ∣ rowValue r (fun _ => 0))
      rw [actualRowProjection r ν]

theorem actualProjection : ZeroValuationTargets.ActualProjection := by
  intro p ν
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact atom_eval a ν
  | negative p ih => exact not_congr ih
  | conjunction p q ihp ihq => exact and_congr ihp ihq
  | disjunction p q ihp ihq => exact or_congr ihp ihq

theorem actualZeroEvaluator : ZeroValuationTargets.ActualZeroEvaluator := by
  intro p
  have hc := (ClosedLinearProof.exactConstantMatrixTest (project p)).mpr (exactConstantProjection p)
  exact (ClosedLinearProof.actualConstantEvaluator (project p) hc (fun _ => 0)).trans
    (actualProjection p (fun _ => 0))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
