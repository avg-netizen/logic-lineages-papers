module
public import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaTargets
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof
import LogicLineages.PermittedControl.OriginalMatrixLinearLowerTableRowProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsAlgebraProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (PlainPreparedRow)
open SignedRowGuardedTest (Test)
open OriginalMatrixLinearLowerTable (lowerTable preparedRow exactLinearPreparedRow)

private theorem testAt (test : Test) (row : NormalForm.Row) (ν : Nat → Nat) (adm : test.Admitted) :
    (testFormula test row).eval ν ↔ test.Holds (NormalForm.rowValue row ν) := by
  cases test with
  | equalZero =>
      change (0 ≤ NormalForm.rowValue row ν ∧ 0 ≤ NormalForm.rowValue (LinearRows.rowScale (-1) row) ν) ↔
        NormalForm.rowValue row ν = 0
      rw [LinearRowsSemanticProof.rowScale_value]
      omega
  | nonnegative => rfl
  | positive =>
      let sum : Int := (row.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum
      change 0 ≤ row.1 - 1 + sum ↔ 0 < row.1 + sum
      omega
  | congruence m =>
      have nonzero : 0 < m := adm
      have hm : m-1+1 = m := by omega
      change (((m-1+1 : Nat) : Int) ∣ NormalForm.rowValue row ν) ↔
        (m : Int) ∣ NormalForm.rowValue row ν
      rw [hm]

private theorem polarizedAt (test : Test) (row : NormalForm.Row) (ν : Nat → Nat) (adm : test.Admitted)
    (positive : Bool) :
    (choosePolarity (testFormula test row) positive).eval ν ↔
      test.atPolarity positive (NormalForm.rowValue row ν) := by
  cases positive with
  | true => exact testAt test row ν adm
  | false => exact not_congr (testAt test row ν adm)

theorem exactLinearRowFormula : ExactLinearRowFormula := by
  intro f ρ top rows lin row member
  let ops := lowerTable top rows
  let lowered := preparedRow top ops row
  have compiled := exactLinearPreparedRow f ρ top rows lin row member
  have plain : PlainPreparedRow lowered := by
    intro s hs
    obtain ⟨term,_,rfl⟩ := List.mem_map.mp hs
    exact ⟨_,rfl⟩
  refine ⟨safeTest ops row.1 lowered plain compiled.1,?_⟩
  intro adm ν fit z positive
  let v := NormalForm.rowValue lowered (Function.update ν 0 z)
  have test :
      (choosePolarity (rowFormula top ops row) positive).eval (Function.update ν 0 z) ↔
        row.1.atPolarity positive v :=
    polarizedAt row.1 lowered (Function.update ν 0 z) adm positive
  constructor
  · intro h
    exact ⟨v,adm,(compiled.2 ν fit z v).mpr rfl,test.mp h,True.intro⟩
  · rintro ⟨w,_,value,pol,_⟩
    have same : v = w := (compiled.2 ν fit z w).mp value
    exact test.mpr (same.symm ▸ pol)

end LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
