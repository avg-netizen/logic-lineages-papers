module
public import LogicLineages.PermittedControl.ActualBitFamilyRawClosedTargets
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawClosed
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open ActualBitFamilyLowSlices (originalRows wantedBits)
open ActualBitFamilyExistentialLow (closedClause closed exactBitFamilyClosed)
open HeterogeneousSignedMatrixSlice (encodeTest encodeRow)
open OriginalPrintedZeroSupport (admitted bit closedCell closedSnapshot)
open OriginalPrintedTerminalBitClauses (BitRow)
open SignedRowGuardedTest (Test)

private theorem literalAdmission (t : Test) : admittedCode (encodeTest t) = admitted t := by
  cases t <;> simp [admittedCode,encodeTest,admitted]

private theorem literalTest (t : Test) (x : Int) : testCode (encodeTest t,x) = bit t x := by
  cases t with
  | equalZero => rfl
  | nonnegative =>
    apply Bool.eq_iff_iff.mpr
    change (decide (x.sign = 0) || decide (x.sign = 1)) = true ↔ decide (0 ≤ x) = true
    simp only [Bool.or_eq_true,decide_eq_true_eq,Int.sign_eq_zero_iff_zero,Int.sign_eq_one_iff_pos]
    omega
  | positive =>
    change decide (x.sign = 1) = decide (0 < x)
    simp only [Int.sign_eq_one_iff_pos]
  | congruence m =>
    apply Bool.eq_iff_iff.mpr
    change decide (x.natAbs % m = 0) = true ↔ decide (x % (m : Int) = 0) = true
    simp only [decide_eq_true_eq,← Nat.dvd_iff_mod_eq_zero,← Int.dvd_iff_emod_eq_zero]
    rw [← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]

private theorem literalRow (r : BitRow) :
    rowCode (encodeBitRow r) =
      match closedCell r.1 with
      | none => false
      | some v => decide (v.2 = r.2) := by
  rcases r with ⟨⟨t,c,terms⟩,want⟩
  simp only [rowCode,encodeBitRow,encodeRow,literalAdmission,literalTest]
  cases terms with
  | nil => cases h : admitted t <;> simp [closedCell,h]
  | cons a as => simp [closedCell]

theorem rawClauseCalibration (clause : List BitRow) :
    clauseCode (clause.map encodeBitRow) = closedClause clause := by
  induction clause with
  | nil => rfl
  | cons r rs ih =>
    change (rowCode (encodeBitRow r) && clauseCode (rs.map encodeBitRow)) = closedClause (r :: rs)
    rw [literalRow,ih]
    cases hb : closedCell r.1 <;> cases ht : closedSnapshot (originalRows rs) <;>
      simp only [originalRows] at ht <;>
      simp [closedClause,originalRows,wantedBits,closedSnapshot,hb,ht,bind,pure,
        List.cons.injEq,Bool.decide_and]

theorem exactClosedRawCalibration : ExactClosedRawCalibration := by
  refine ⟨rawClauseCalibration,?_⟩
  intro family
  induction family with
  | nil => rfl
  | cons c cs ih =>
    change (clauseCode (c.map encodeBitRow) || closedCode (encodeFamily cs)) =
      (closedClause c || closed cs)
    rw [rawClauseCalibration,ih]

theorem exactClosedRawTruth : ExactClosedRawTruth := by
  intro f family zero
  rw [exactClosedRawCalibration.2 family]
  exact exactBitFamilyClosed f family zero

end LogicLineages.PermittedControl.ActualBitFamilyRawClosed
