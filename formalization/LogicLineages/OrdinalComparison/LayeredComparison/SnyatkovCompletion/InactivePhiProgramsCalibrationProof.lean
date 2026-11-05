module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
open NormalForm InactivePhiPrograms

private theorem kept_calibration (xs : List (Int × Summand)) (mask : List Bool) :
    Code.keptItems mask (xs.map (fun a => (a.1, a.2.data))) =
      (InactivePhiRows.keptItems mask xs).map (fun a => (a.1, a.2.data)) := by
  induction xs generalizing mask with
  | nil => cases mask <;> rfl
  | cons a xs ih =>
      cases mask with
      | nil => rfl
      | cons b bs =>
          cases b <;> simpa [Code.keptItems, InactivePhiRows.keptItems] using ih bs

private theorem dropped_calibration (xs : List (Int × Summand)) (mask : List Bool) :
    Code.droppedItems mask (xs.map (fun a => (a.1, a.2.data))) =
      (InactivePhiRows.droppedItems mask xs).map (fun a => (a.1, a.2.data)) := by
  induction xs generalizing mask with
  | nil => cases mask <;> rfl
  | cons a xs ih =>
      cases mask with
      | nil => rfl
      | cons b bs =>
          cases b <;> simpa [Code.droppedItems, InactivePhiRows.droppedItems] using ih bs

theorem remaining_calibration (r : Row) (mask : List Bool) :
    Code.remaining (rowData r) mask = rowData (InactivePhiRows.remaining r mask) := by
  unfold Code.remaining InactivePhiRows.remaining rowData
  rw [kept_calibration]

theorem droppedRow_calibration (r : Row) (mask : List Bool) :
    Code.dropped (rowData r) mask = rowData (InactivePhiRows.dropped r mask) := by
  unfold Code.dropped InactivePhiRows.dropped rowData
  rw [dropped_calibration]

theorem onlyPhi_calibration (r : Row) : Code.onlyPhi (rowData r) = InactivePhiRows.onlyPhi r := by
  simp only [Code.onlyPhi, InactivePhiRows.onlyPhi, rowData, List.all_map, Function.comp_def]
  apply congrArg (fun f : Int × Summand → Bool => r.2.all f)
  funext a
  rcases a with ⟨w, s⟩
  cases s <;> rfl

theorem literalPartitionData : InactivePhiProgramsTargets.LiteralPartitionData :=
  fun r mask => ⟨remaining_calibration r mask, droppedRow_calibration r mask, onlyPhi_calibration r⟩

theorem admissible_calibration (i : Nat) (r : Row) (mask : List Bool) :
    Code.admissible i (rowData r) mask = InactivePhiRows.admissible i r mask := by
  unfold Code.admissible InactivePhiRows.admissible
  rw [remaining_calibration, droppedRow_calibration, onlyPhi_calibration,
    LinearRowsCodeProof.rowLinear_calibration]
  simp only [rowData, List.length_map]

theorem masks_calibration (i : Nat) (r : Row) :
    Code.masks i (rowData r) = InactivePhiRows.masks i r := by
  unfold Code.masks InactivePhiRows.masks
  have hlen : (rowData r).2.length = r.2.length := by simp only [rowData, List.length_map]
  rw [hlen]
  apply congrArg (fun f : List Bool → Bool => (CommonHeadLargeGuards.masks r.2.length).filter f)
  funext mask
  exact admissible_calibration i r mask

theorem literalAdmissibleMasks : InactivePhiProgramsTargets.LiteralAdmissibleMasks :=
  fun i r => ⟨admissible_calibration i r, masks_calibration i r⟩

theorem guard_calibration (r : Row) (mask : List Bool) :
    Code.guard (rowData r) mask = (InactivePhiRows.guard r mask).encode := by
  unfold Code.guard InactivePhiRows.guard
  rw [droppedRow_calibration]
  exact ShiftedInputProgramsProof.literalGuardPrograms.1 _

theorem withRow_calibration (a : Atom) (r : Row) :
    Code.withRow a.data (rowData r) = (InactivePhiRows.withRow a r).data := by
  cases a <;> rfl

theorem literalGuardAndAtomCodes : InactivePhiProgramsTargets.LiteralGuardAndAtomCodes :=
  ⟨guard_calibration, withRow_calibration⟩

theorem any_calibration (ps : List Formula) :
    Code.any (ps.map Formula.encode) = (BoundedRows.any ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [Code.any, List.map_cons, List.foldr_cons, BoundedRows.any,
        Formula.encode, ShiftedInputPrograms.Code.disjunction] at ih ⊢
      rw [ih]

private theorem atom_row (a : Atom) : a.data.2.2 = rowData a.row := by cases a <;> rfl

theorem literalCompiler : InactivePhiProgramsTargets.LiteralCompiler := by
  intro i a
  unfold Code.compileAtom InactivePhiRows.compileAtom
  rw [atom_row, masks_calibration, ← any_calibration]
  apply congrArg Code.any
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro mask _
  rw [guard_calibration, remaining_calibration, withRow_calibration]
  rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
