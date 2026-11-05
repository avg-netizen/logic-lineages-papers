module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsCodeProof
open NormalForm (Summand Formula)
open HyperBranchRows

theorem closeGuard_calibration (i j : Nat) (e h k l : Int) (c code : Nat) :
    Code.closeGuard (HyperWindowCode.input i j e h k l c code) =
      (closeGuard i j e h k l c).encode := by
  change FiniteBranchRows.Code.conjunction
    (FiniteBranchRows.Code.guardedLe (Summand.hyperPhi j k l).data (Summand.hyperPhi i e h).data 1)
    (FiniteBranchRows.Code.guardedLe (Summand.hyperPhi i e h).data (Summand.hyperPhi j k l).data c) = _
  simp only [FiniteBranchRowsCodeProof.guardedLe_calibration]
  rfl

theorem indexEquality_calibration (i j : Nat) (e h k l : Int) (c code : Nat) :
    Code.indexEquality (HyperWindowCode.input i j e h k l c code) =
      (indexEquality i j e k).encode := rfl

theorem leftCases_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) :
    Code.leftCases (HyperWindowCode.input i j e h k l c p.encode) =
      (leftCases i j e h k l c p).encode := by
  change BoundedRows.Code.bounded i (HyperWindow.leftBound e h l)
    (FiniteBranchRows.Code.conjunction
      (Code.closeGuard (HyperWindowCode.input i j e h k l c p.encode)) p.encode) = _
  rw [closeGuard_calibration]
  exact BoundedRowsCodeProof.bounded_calibration i (HyperWindow.leftBound e h l)
    (.conjunction (closeGuard i j e h k l c) p)

theorem rightCases_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) :
    Code.rightCases (HyperWindowCode.input i j e h k l c p.encode) =
      (rightCases i j e h k l c p).encode := by
  change BoundedRows.Code.bounded j (HyperWindow.rightBound h k l c)
    (FiniteBranchRows.Code.conjunction
      (Code.closeGuard (HyperWindowCode.input i j e h k l c p.encode)) p.encode) = _
  rw [closeGuard_calibration]
  exact BoundedRowsCodeProof.bounded_calibration j (HyperWindow.rightBound h k l c)
    (.conjunction (closeGuard i j e h k l c) p)

theorem equalCases_calibration (i j : Nat) (e h k l : Int) (c : Nat) (p : Formula) :
    Code.equalCases (HyperWindowCode.input i j e h k l c p.encode) =
      (equalCases i j e h k l c p).encode := by
  change SignedRows.Code.substitute i j (k - e)
    (FiniteBranchRows.Code.conjunction
      (Code.indexEquality (HyperWindowCode.input i j e h k l c p.encode))
      (FiniteBranchRows.Code.conjunction
        (Code.closeGuard (HyperWindowCode.input i j e h k l c p.encode)) p.encode)) = _
  rw [indexEquality_calibration, closeGuard_calibration]
  exact SignedRowsCodeProof.substitute_calibration i j (k - e)
    (.conjunction (indexEquality i j e k) (.conjunction (closeGuard i j e h k l c) p))

theorem literalBranchCodeCalibration : HyperBranchRowsTargets.LiteralBranchCodeCalibration :=
  fun i j e h k l c p => ⟨leftCases_calibration i j e h k l c p,
    rightCases_calibration i j e h k l c p, equalCases_calibration i j e h k l c p⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsCodeProof
