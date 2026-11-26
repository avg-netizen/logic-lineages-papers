module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodeProof
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open LayeredComparison.SnyatkovCompletion

theorem nonnegative_code (r : Row) :
    Code.nonnegative r = Formula.encode (.atom (.nonnegative r)) := rfl

theorem rowEquation_code (r : Row) :
    Code.rowEquation r = Formula.encode (rowEquation r) := rfl

theorem positiveFold_code (xs : List Nat) :
    xs.foldr (fun i p => LinearRows.Code.conjunction (Code.nonnegative (positiveRow i)) p) 0 =
      Formula.encode (xs.foldr
        (fun i p => .conj (.atom (.nonnegative (positiveRow i))) p) .top) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldr_cons]
      rw [ih]
      rfl

theorem positiveFrame_code (n : Nat) :
    Code.positiveFrame n = Formula.encode (positiveFrame n) := positiveFold_code (List.range n)

theorem rowEquations_code (rs : List Row) :
    Code.rowEquations rs = Formula.encode (rowEquations rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [Code.rowEquations,rowEquations,List.foldr_cons,
        LinearRows.Code.conjunction,Formula.encode,← rowEquation_code] at ih ⊢
      rw [ih]

theorem badSign_code (mode : Nat) (r : Row) :
    Code.badSign mode r = Formula.encode (badSignFormula mode r) := by
  unfold Code.badSign badSignFormula
  split_ifs <;> rfl

theorem failedPositive_code (flag : Bool) :
    Code.failedPositive flag = Formula.encode (failedPositive flag) := by
  cases flag <;> rfl

theorem literalCodeCalibration : Targets.LiteralCodeCalibration := by
  intro p
  simp only [Code.matrix,matrix,LinearRows.Code.conjunction,Code.disjunction,
    Formula.encode,← positiveFrame_code,← rowEquations_code,← failedPositive_code,← badSign_code]

#print axioms nonnegative_code
#print axioms rowEquation_code
#print axioms positiveFold_code
#print axioms positiveFrame_code
#print axioms rowEquations_code
#print axioms badSign_code
#print axioms failedPositive_code
#print axioms literalCodeCalibration

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.CodeProof
