module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsCodeProof
open NormalForm (Summand Formula)
open PlainWindowRows

theorem plusGuard_calibration (i j : Nat) (e k : Int) (c code : Nat) :
    Code.plusGuard (Code.input i j e k c code) = (plusGuard i j e k c).encode := by
  change FiniteBranchRows.Code.conjunction
    (FiniteBranchRows.Code.guardedLe (Summand.phi j k).data (Summand.phi i e).data 1)
    (FiniteBranchRows.Code.guardedLe (Summand.phi i e).data (Summand.phi j k).data c) = _
  simp only [FiniteBranchRowsCodeProof.guardedLe_calibration]
  rfl

theorem minusGuard_calibration (i j : Nat) (e k : Int) (c code : Nat) :
    Code.minusGuard (Code.input i j e k c code) = (minusGuard i j e k c).encode := by
  change FiniteBranchRows.Code.conjunction
    (FiniteBranchRows.Code.guardedLe (Summand.phi i e).data (Summand.phi j k).data 1)
    (FiniteBranchRows.Code.guardedLe (Summand.phi j k).data (Summand.phi i e).data c) = _
  simp only [FiniteBranchRowsCodeProof.guardedLe_calibration]
  rfl

theorem plusSubstitute_calibration (i j : Nat) (e k : Int) (c d : Nat) (p : Formula) :
    Code.plusSubstitute (Code.input i j e k c p.encode) d =
      (plusSubstitute i j e k d p).encode :=
  NestedRowsCodeProof.substitute_calibration i j k ((d : Int) - e) p

theorem minusSubstitute_calibration (i j : Nat) (e k : Int) (c d : Nat) (p : Formula) :
    Code.minusSubstitute (Code.input i j e k c p.encode) d =
      (minusSubstitute i j e k d p).encode :=
  NestedRowsCodeProof.substitute_calibration i j (k - (d : Int)) (-e) p

theorem plusCases_calibration (i j : Nat) (e k : Int) (c : Nat) (p : Formula) :
    Code.plusCases (Code.input i j e k c p.encode) = (plusCases i j e k c p).encode := by
  unfold Code.plusCases plusCases
  rw [← BoundedRowsCodeProof.any_calibration]
  apply congrArg BoundedRows.Code.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  change Code.plusSubstitute
    (Code.input i j e k c (FiniteBranchRows.Code.conjunction
      (Code.plusGuard (Code.input i j e k c p.encode)) p.encode)) d = _
  rw [plusGuard_calibration]
  exact plusSubstitute_calibration i j e k c d (.conjunction (plusGuard i j e k c) p)

theorem minusCases_calibration (i j : Nat) (e k : Int) (c : Nat) (p : Formula) :
    Code.minusCases (Code.input i j e k c p.encode) = (minusCases i j e k c p).encode := by
  unfold Code.minusCases minusCases
  rw [← BoundedRowsCodeProof.any_calibration]
  apply congrArg BoundedRows.Code.any
  rw [List.map_map]
  apply List.map_congr_left
  intro d hd
  change Code.minusSubstitute
    (Code.input i j e k c (FiniteBranchRows.Code.conjunction
      (Code.minusGuard (Code.input i j e k c p.encode)) p.encode)) d = _
  rw [minusGuard_calibration]
  exact minusSubstitute_calibration i j e k c d (.conjunction (minusGuard i j e k c) p)

theorem literalBranchCodeCalibration : PlainWindowRowsTargets.LiteralBranchCodeCalibration :=
  fun i j e k c p => ⟨plusCases_calibration i j e k c p, minusCases_calibration i j e k c p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsCodeProof
