module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
open NormalForm

theorem allLinear_calibration (names : List Nat) (p : Formula) :
    LinearBlock.Code.allLinear names p.encode = LinearBlock.allLinear names p := by
  simp only [LinearBlock.Code.allLinear, LinearBlock.allLinear,
    LinearRowsCodeProof.isLinear_calibration]

theorem eliminate_calibration (names : List Nat) (p : Formula) :
    LinearBlock.Code.eliminate names p.encode = (LinearBlock.eliminate names p).encode := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      change LinearRows.Code.eliminate i (LinearBlock.Code.eliminate names p.encode) = _
      rw [ih, LinearRowsCodeProof.eliminate_calibration]
      rfl

theorem literalCodeCalibration : LinearBlockTargets.LiteralCodeCalibration :=
  ⟨allLinear_calibration, eliminate_calibration⟩

theorem allLinear_primitive : Primrec₂ LinearBlock.Code.allLinear := by
  have hp : Primrec₂ (fun code i : Nat => LinearRows.Code.isLinear i code) :=
    LinearRowsCodeProof.isLinear_primitive.comp Primrec.snd Primrec.fst
  exact (LinearRowsCodeProof.listAll_primitive hp).comp Primrec.snd Primrec.fst

theorem eliminate_primitive : Primrec₂ LinearBlock.Code.eliminate := by
  have hs : Primrec (fun p : (List Nat × Nat) × (Nat × Nat) =>
      LinearRows.Code.eliminate p.2.1 p.2.2) :=
    LinearRowsCodeProof.eliminate_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst Primrec.snd hs.to₂

theorem actualNumericPrograms : LinearBlockTargets.ActualNumericPrograms :=
  ⟨allLinear_primitive, eliminate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
