module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
open NormalForm SourceRows ClosedLinear

theorem exactConstantMatrixTest : ClosedLinearTargets.ExactConstantMatrixTest := by
  intro p
  induction p with
  | truth => simp [constantMatrix, LinearRows.atoms, Formula.variables]
  | falsity => simp [constantMatrix, LinearRows.atoms, Formula.variables]
  | atom a => simp [constantMatrix, LinearRows.atoms, Formula.variables, rowVariables]
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [constantMatrix, LinearRows.atoms, List.all_append, Bool.and_eq_true,
        Formula.variables, List.append_eq_nil_iff] using and_congr ihp ihq
  | disjunction p q ihp ihq =>
      simpa only [constantMatrix, LinearRows.atoms, List.all_append, Bool.and_eq_true,
        Formula.variables, List.append_eq_nil_iff] using and_congr ihp ihq

private theorem constantAtom_correct (a : Atom) (h : a.row.2 = []) (ν : Nat → Nat) :
    constantAtom a = true ↔ a.eval ν := by
  cases a with
  | nonnegative row =>
      simp only [Atom.row] at h
      simp [constantAtom, Atom.eval, rowValue, h]
  | divisible m row =>
      simp only [Atom.row] at h
      simp only [constantAtom, decide_eq_true_eq, Atom.eval, rowValue, h,
        List.map_nil, List.sum_nil, Int.add_zero]
      rw [Int.natCast_dvd, Nat.dvd_iff_mod_eq_zero]

theorem actualConstantEvaluator : ClosedLinearTargets.ActualConstantEvaluator := by
  intro p
  induction p with
  | truth => intro _ ν; simp [evaluateConstants, Formula.eval]
  | falsity => intro _ ν; simp [evaluateConstants, Formula.eval]
  | atom a =>
      intro h ν
      have hh : a.row.2 = [] := by simpa [constantMatrix, LinearRows.atoms] using h
      exact constantAtom_correct a hh ν
  | negative p ih =>
      intro h ν
      change (!evaluateConstants p) = true ↔ ¬p.eval ν
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact not_congr (ih h ν)
  | conjunction p q ihp ihq =>
      intro h ν
      have hh : constantMatrix p = true ∧ constantMatrix q = true := by
        simpa [constantMatrix, LinearRows.atoms] using h
      simpa only [evaluateConstants, Formula.eval, Bool.and_eq_true] using
        and_congr (ihp hh.1 ν) (ihq hh.2 ν)
  | disjunction p q ihp ihq =>
      intro h ν
      have hh : constantMatrix p = true ∧ constantMatrix q = true := by
        simpa [constantMatrix, LinearRows.atoms] using h
      simpa only [evaluateConstants, Formula.eval, Bool.or_eq_true] using
        or_congr (ihp hh.1 ν) (ihq hh.2 ν)

theorem eliminated_constant (p : QFormula) :
    constantMatrix (QuantifiedLinear.eliminate p) = p.variables.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  rw [exactConstantMatrixTest]
  simp only [List.isEmpty_iff]
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have he := (QuantifiedLinearProof.exactFreeVariableSupport p i).mpr hi
    simpa [h] using he
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have he := (QuantifiedLinearProof.exactFreeVariableSupport p i).mp hi
    simpa [h] using he

theorem exactDecisionDomain : ClosedLinearTargets.ExactDecisionDomain := by
  intro p
  simp only [decideClosed, eliminated_constant]
  split <;> simp_all

theorem actualClosedDecision : ClosedLinearTargets.ActualClosedDecision := by
  intro p hadm hclosed ν answer
  have hc : constantMatrix (QuantifiedLinear.eliminate p) = true := by
    rw [eliminated_constant, hclosed]
    rfl
  have he : evaluateConstants (QuantifiedLinear.eliminate p) = true ↔ p.eval ν :=
    (actualConstantEvaluator _ hc ν).trans
      (QuantifiedLinearProof.actualQuantifierElimination p hadm ν)
  simp only [decideClosed, hadm, hc, Bool.and_self, if_true, Option.some.injEq]
  rw [Bool.eq_iff_iff, he]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
