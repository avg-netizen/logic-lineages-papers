module
public import LogicLineages.PermittedControl.InverseComparisonPreparedRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.InverseComparisonPreparedRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem greaterEval (c : Int) (ν : Nat → Nat) :
    (greaterMinusParameter c).eval ν ↔ 0 ≤ c + (ν 0 : Int) - (ν 1 : Int) := by
  simp [greaterMinusParameter,NormalForm.Formula.eval,NormalForm.Atom.eval,
    NormalForm.rowValue,NormalForm.Summand.term,Term.value,sub_eq_add_neg,add_assoc]

private theorem parameterEval (c : Int) (ν : Nat → Nat) :
    (parameterMinusGreater c).eval ν ↔ 0 ≤ c + (ν 1 : Int) - (ν 0 : Int) := by
  simp [parameterMinusGreater,NormalForm.Formula.eval,NormalForm.Atom.eval,
    NormalForm.rowValue,NormalForm.Summand.term,Term.value,sub_eq_add_neg,add_assoc]

theorem actualInverseRows : ActualInverseRows := by
  intro sign wanted valueP valueQ ν range positive table
  rcases (show sign = 0 ∨ sign = 1 ∨ sign = 2 by omega) with rfl | rfl | rfl
  · obtain ⟨less,unequal,greater⟩ := table.2.2 rfl
    simp only [emitFormula,Nat.reduceEq,↓reduceIte,greaterEval,parameterEval,
      NormalForm.Formula.eval,numericalComparison]
    split_ifs <;> omega
  · obtain ⟨less,equal,greater⟩ := table.1 rfl
    simp only [emitFormula,Nat.reduceEq,↓reduceIte,equalRows,greaterEval,parameterEval,
      NormalForm.Formula.eval,numericalComparison]
    split_ifs <;> omega
  · obtain ⟨less,unequal,greater⟩ := table.2.1 rfl
    simp only [emitFormula,Nat.reduceEq,↓reduceIte,greaterEval,parameterEval,
      NormalForm.Formula.eval,numericalComparison]
    split_ifs <;> omega

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
