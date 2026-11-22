module
public import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedInput PreparedTableTied)
open HeterogeneousSignedMatrixSlice (Row actualRows)
open SignedRowGuardedTest (Test)
open OriginalMatrixLinearLowerTable (TopLinear lowerTable preparedRow)

def testFormula (test : Test) (row : NormalForm.Row) : NormalForm.Formula :=
  match test with
  | .equalZero => .conjunction (.atom (.nonnegative row))
      (.atom (.nonnegative (LinearRows.rowScale (-1) row)))
  | .nonnegative => .atom (.nonnegative row)
  | .positive => .atom (.nonnegative (row.1 - 1,row.2))
  | .congruence m => .atom (.divisible (m-1) row)

noncomputable def rowFormula (top : Nat) (ops : List LowerOperand) (row : Row) : NormalForm.Formula :=
  testFormula row.1 (preparedRow top ops row)

def choosePolarity (p : NormalForm.Formula) (positive : Bool) : NormalForm.Formula :=
  if positive then p else .negative p

def ExactLinearRowFormula : Prop :=
  ∀ (f ρ : Nat → Nat) (top : Nat) (rows : List Row), TopLinear top rows →
  ∀ row ∈ rows,
    let ops := lowerTable top rows
    let p := rowFormula top ops row
    PreparedInput ops p ∧
    (row.1.Admitted → ∀ (ν : Nat → Nat), PreparedTableTied f top ρ ops ν →
      ∀ (z : Nat) (positive : Bool),
        ((choosePolarity p positive).eval (Function.update ν 0 z) ↔
          ∃ v : Int, actualRows f (Function.update ρ top z) [row] [(v,positive)]))

end LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
