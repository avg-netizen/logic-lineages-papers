module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
open NormalForm (Row Atom Formula Summand rowData)
open MaximalPlainPrograms

theorem ownIndices_calibration (i : Nat) (r : Row) :
    Code.ownIndices i (rowData r) = MaximalPlainRows.ownIndices i r := by
  unfold Code.ownIndices MaximalPlainRows.ownIndices
  rw [ShiftedInputProgramsProof.occurrences_calibration, ShiftedInputProgramsProof.inputs_calibration]

theorem activeGuard_calibration (i : Nat) (r : Row) :
    Code.activeGuard i (rowData r) = (MaximalPlainRows.activeGuard i r).encode := by
  unfold Code.activeGuard MaximalPlainRows.activeGuard
  rw [ownIndices_calibration, ← InactivePhiProgramsProof.any_calibration]
  apply congrArg InactivePhiPrograms.Code.any
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k _
  rw [ShiftedInputProgramsProof.literalGuardPrograms.2.1 r k 0]
  rfl

theorem literalActiveGuard : MaximalPlainProgramsTargets.LiteralActiveGuard :=
  fun i r => ⟨ownIndices_calibration i r, activeGuard_calibration i r⟩

private theorem residueSplit_calibration (i m : Nat) (xs : List (Int × Summand)) :
    Code.residueSplit i m (xs.map (fun a => (a.1, a.2.data))) =
      ((MaximalPlainRows.residueSplit i m xs).1,
        (MaximalPlainRows.residueSplit i m xs).2.map (fun a => (a.1, a.2.data))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      simp only [List.map_cons, Code.residueSplit, MaximalPlainRows.residueSplit,
        List.foldr_cons] at ih ⊢
      rw [ih]
      cases s with
      | «variable» j => simp [Summand.data]
      | hyperPhi j e f => simp [Summand.data]
      | phi j e => by_cases hj : j = i <;> simp [Summand.data, hj]

theorem literalResidueData : MaximalPlainProgramsTargets.LiteralResidueData := by
  intro i m r
  unfold Code.residueRow MaximalPlainRows.residueRow rowData
  rw [residueSplit_calibration]

theorem nonnegative_calibration (i : Nat) (r : Row) :
    Code.nonnegative i (rowData r) = (MaximalPlainRows.nonnegative i r).encode := by
  unfold Code.nonnegative MaximalPlainRows.nonnegative
  have hi := InactivePhiProgramsProof.literalCompiler i (.nonnegative r)
  change InactivePhiPrograms.Code.compileAtom i (0, 0, rowData r) = _ at hi
  rw [hi, activeGuard_calibration,
    ShiftedInputProgramsProof.literalGuardPrograms.2.2 r 0,
    ShiftedInputProgramsProof.literalGuardPrograms.2.2 r 1]
  rfl

theorem cutoff_calibration (a : Atom) : Code.cutoff a.data = MaximalPlainRows.cutoff a := by
  cases a with
  | nonnegative r =>
      change PlainPhiDominance.Code.threshold (rowData r) = PlainPhiDominance.threshold r
      exact PlainPhiDominanceProof.threshold_calibration r
  | divisible m r =>
      simp only [Code.cutoff, Atom.data, show (1 : Nat) ≠ 0 by decide, if_false,
        MaximalPlainRows.cutoff, PlainPhiDominanceProof.shiftMass_calibration]

theorem compileAtom_calibration (i : Nat) (a : Atom) :
    Code.compileAtom i a.data = (MaximalPlainRows.compileAtom i a).encode := by
  cases a with
  | nonnegative r => exact nonnegative_calibration i r
  | divisible m r =>
      simp only [Code.compileAtom, Atom.data, show (1 : Nat) ≠ 0 by decide, if_false,
        MaximalPlainRows.compileAtom]
      rw [literalResidueData i (m + 1) r]
      rfl

theorem literalCutoffCompiler : MaximalPlainProgramsTargets.LiteralCutoffCompiler :=
  fun i a => ⟨cutoff_calibration a, compileAtom_calibration i a⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
