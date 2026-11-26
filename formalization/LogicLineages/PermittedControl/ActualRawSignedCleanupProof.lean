module
public import LogicLineages.PermittedControl.ActualRawSignedCleanupTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawSignedCleanup
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (WeightedOperand encodeWeighted)
open ActualRawSignedStaticCeiling (encodeSyntax)
open ActualEffectiveTerminalSignBound (shortLengthCode)
open ActualShortCountCleanup (shortLength)
open ActualSymbolicZeroSuccessor (SyntaxState cleanSyntax cleanupShift)
open ActualInitialSignedCountCleanup (cleanup)

theorem shortCalibration (op : LowerOperand) : shortLengthCode op.code = shortLength op := by
  cases op <;> rfl

theorem retainCalibration (terms : List WeightedOperand) :
    retainCode (terms.map encodeWeighted) = (cleanSyntax terms).map encodeWeighted := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
      change (encodeWeighted t :: ts.map encodeWeighted).filter
          (fun u => decide (shortLengthCode u.2 = 0)) =
        ((t :: ts).filter (fun u => decide (shortLength u.2 = 0))).map encodeWeighted
      have one : shortLengthCode (encodeWeighted t).2 = shortLength t.2 := shortCalibration t.2
      simp only [List.filter_cons,one]
      cases h : decide (shortLength t.2 = 0) with
      | false =>
        simp only [h,Bool.false_eq_true,if_false]
        exact ih
      | true =>
        simp only [h,if_pos rfl]
        exact congrArg (List.cons (encodeWeighted t)) ih

theorem shiftCalibration (terms : List WeightedOperand) :
    shiftCode (terms.map encodeWeighted) = cleanupShift terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    change t.1 * (shortLengthCode t.2.code : Int) + shiftCode (ts.map encodeWeighted) =
      t.1 * (shortLength t.2 : Int) + cleanupShift ts
    rw [shortCalibration,ih]

theorem cleanupCalibration (s : SyntaxState) :
    cleanupCode (encodeSyntax s) = encodeSyntax (cleanup s) := by
  unfold cleanupCode encodeSyntax cleanup
  rw [shiftCalibration,retainCalibration]

theorem exactRawInitialCleanup : ExactRawInitialCleanup :=
  ⟨shortCalibration,retainCalibration,shiftCalibration,cleanupCalibration⟩

end LogicLineages.PermittedControl.ActualRawSignedCleanup
