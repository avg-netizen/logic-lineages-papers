module
public import LogicLineages.PermittedControl.InverseComparisonPreparedRowsTargets
import LogicLineages.PermittedControl.InverseComparisonPreparedRowsCodeProof

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

private theorem comparisonCodes (p q : Nat) :
    (numericalComparison p q = 0 ↔ p < q) ∧
    (numericalComparison p q = 1 ↔ p = q) ∧
    (numericalComparison p q = 2 ↔ q < p) ∧ numericalComparison p q ≤ 2 := by
  rcases lt_trichotomy p q with lower | rfl | upper
  · have notUpper : ¬q < p := not_lt_of_ge lower.le
    simp [numericalComparison,lower,ne_of_lt lower,notUpper]
  · simp [numericalComparison]
  · have notLower : ¬p < q := not_lt_of_ge upper.le
    simp [numericalComparison,upper,ne_of_gt upper,notLower]

theorem actualInverseRows : ActualInverseRows := by
  intro sign wanted valueP valueQ ν range positive table
  obtain ⟨isLess,isEqual,isGreater,codeRange⟩ := comparisonCodes valueP valueQ
  by_cases valid : wanted ≤ 2
  · have outcomes : wanted = 0 ∨ wanted = 1 ∨ wanted = 2 := by omega
    rcases (show sign = 0 ∨ sign = 1 ∨ sign = 2 by omega) with rfl | rfl | rfl
    · obtain ⟨lower,unequal,upper⟩ := table.2.2 rfl
      rcases outcomes with rfl | rfl | rfl
      · change (greaterMinusParameter 0).eval ν ↔ numericalComparison valueP valueQ = 0
        rw [greaterEval,isLess,upper]
        omega
      · change False ↔ numericalComparison valueP valueQ = 1
        rw [isEqual]
        exact ⟨False.elim,fun h => unequal h.symm⟩
      · change (parameterMinusGreater (-1)).eval ν ↔ numericalComparison valueP valueQ = 2
        rw [parameterEval,isGreater,lower]
        omega
    · obtain ⟨lower,equal,upper⟩ := table.1 rfl
      rcases outcomes with rfl | rfl | rfl
      · change (greaterMinusParameter (-1)).eval ν ↔ numericalComparison valueP valueQ = 0
        rw [greaterEval,isLess,upper]
        omega
      · change (greaterMinusParameter 0).eval ν ∧ (parameterMinusGreater 0).eval ν ↔
          numericalComparison valueP valueQ = 1
        have same : valueP = valueQ ↔ ν 0 = ν 1 := ⟨fun h => equal.mp h.symm,fun h => (equal.mpr h).symm⟩
        rw [greaterEval,parameterEval,isEqual,same]
        omega
      · change (parameterMinusGreater (-1)).eval ν ↔ numericalComparison valueP valueQ = 2
        rw [parameterEval,isGreater,lower]
        omega
    · obtain ⟨lower,unequal,upper⟩ := table.2.1 rfl
      rcases outcomes with rfl | rfl | rfl
      · change (greaterMinusParameter (-1)).eval ν ↔ numericalComparison valueP valueQ = 0
        rw [greaterEval,isLess,upper]
        omega
      · change False ↔ numericalComparison valueP valueQ = 1
        rw [isEqual]
        exact ⟨False.elim,fun h => unequal h.symm⟩
      · change (parameterMinusGreater 0).eval ν ↔ numericalComparison valueP valueQ = 2
        rw [parameterEval,isGreater,lower]
        omega
  · rw [formulaInvalid sign wanted (Or.inr (lt_of_not_ge valid))]
    change False ↔ numericalComparison valueP valueQ = wanted
    exact ⟨False.elim,fun equality => valid (equality ▸ codeRange)⟩

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
