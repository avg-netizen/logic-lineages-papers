module
public import LogicLineages.PermittedControl.SelectedLeadingSignCutoffTargets
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffMagnitudeProof
import LogicLineages.PermittedControl.SelectedNonlinearImageBoundsGrowthProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedLeadingSignCutoff

theorem actualLeadingSign : ActualLeadingSign := by
  intro f B selected z C K K₀ L R E tail leading nonzero decomposition error
  have rawLog := SelectedNonlinearImageBounds.rawCoordinateLogBound f B selected z C leading
  have cutoffLog := tail.trans rawLog
  have strict : 2 * E.natAbs < C :=
    (Nat.mul_le_mul_left 2 error).trans_lt (absoluteErrorBelowHalf K K₀ C cutoffLog)
  have magnitude : (2 : Int) * (E.natAbs : Int) < (C : Int) := by exact_mod_cast strict
  have upper : E ≤ (E.natAbs : Int) := Int.le_natAbs
  have lower : -E ≤ (E.natAbs : Int) := Int.neg_le_natAbs
  have margin : -(C : Int) < 2*E ∧ 2*E < (C : Int) := by
    constructor <;> omega
  have cNonnegative : 0 ≤ (C : Int) := by omega
  have positiveRow (h : 0 < L) : 0 < R := by
    have unit : (1 : Int) ≤ L := by omega
    have dominates : (C : Int) ≤ L*(C : Int) := by
      simpa using mul_le_mul_of_nonneg_right unit cNonnegative
    omega
  have negativeRow (h : L < 0) : R < 0 := by
    have unit : L ≤ (-1 : Int) := by omega
    have dominates : L*(C : Int) ≤ -(C : Int) := by
      simpa using mul_le_mul_of_nonneg_right unit cNonnegative
    omega
  rcases lt_trichotomy L 0 with negative | zero | positive
  · have sign := negativeRow negative
    omega
  · exact (nonzero zero).elim
  · have sign := positiveRow positive
    omega

end LogicLineages.PermittedControl.SelectedLeadingSignCutoff
