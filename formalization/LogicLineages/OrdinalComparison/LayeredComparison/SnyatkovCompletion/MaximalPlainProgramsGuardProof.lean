module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsCompilerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
open MaximalPlainPrograms

theorem ownIndices_primitive : Primrec₂ Code.ownIndices := by
  let A := Nat × NormalForm.Code.RowData
  have hl : Primrec (fun p : A => List.range (ShiftedInputPrograms.Code.occurrences p.2).length) :=
    Primrec.list_range.comp (Primrec.list_length.comp
      (ShiftedInputProgramsProof.occurrences_primitive.comp Primrec.snd))
  have hv : Primrec (fun p : A × Nat =>
      ((ShiftedInputPrograms.Code.inputs p.1.2).getD p.2 (0, 0)).1) :=
    Primrec.fst.comp ((Primrec.list_getD (0, 0)).comp
      (ShiftedInputProgramsProof.inputs_primitive.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have hp : Primrec (fun p : A × Nat =>
      ((ShiftedInputPrograms.Code.inputs p.1.2).getD p.2 (0, 0)).1 == p.1.1) :=
    Primrec.beq.comp hv (Primrec.fst.comp Primrec.fst)
  exact (InactivePhiProgramsProof.filterWith_primitive hp.to₂).comp Primrec.id hl

private theorem zeroBlock_primitive : Primrec (fun p : NormalForm.Code.RowData × Nat =>
    ShiftedInputPrograms.Code.block p.1 p.2 0) := by
  have ha : Primrec (fun p : NormalForm.Code.RowData × Nat => (p.1, p.2, (0 : Int))) :=
    Primrec.fst.pair (Primrec.snd.pair (Primrec.const (0 : Int)))
  have h := ShiftedInputProgramsProof.block_primitive.comp ha
  apply h.of_eq
  intro p
  rfl

private theorem negativeZeroBlock_primitive : Primrec (fun p : NormalForm.Code.RowData × Nat =>
    ShiftedInputPrograms.Code.negative (ShiftedInputPrograms.Code.block p.1 p.2 0)) :=
  ShiftedInputProgramsProof.negative_primitive.comp zeroBlock_primitive

private theorem ownBlocks_primitive : Primrec (fun p : Nat × NormalForm.Code.RowData =>
    (Code.ownIndices p.1 p.2).map (fun k =>
      ShiftedInputPrograms.Code.negative (ShiftedInputPrograms.Code.block p.2 k 0))) := by
  have he : Primrec (fun p : (Nat × NormalForm.Code.RowData) × Nat =>
      ShiftedInputPrograms.Code.negative (ShiftedInputPrograms.Code.block p.1.2 p.2 0)) := by
    have ha : Primrec (fun p : (Nat × NormalForm.Code.RowData) × Nat => (p.1.2, p.2)) :=
      (Primrec.snd.comp Primrec.fst).pair Primrec.snd
    have h := negativeZeroBlock_primitive.comp ha
    apply h.of_eq
    intro p
    rfl
  have h := Primrec.list_map ownIndices_primitive he.to₂
  apply h.of_eq
  intro p
  rfl

theorem activeGuard_primitive : Primrec₂ Code.activeGuard := by
  have h := InactivePhiProgramsProof.any_primitive.comp ownBlocks_primitive
  apply h.of_eq
  intro p
  rfl

theorem actualGuardPrograms : MaximalPlainProgramsTargets.ActualGuardPrograms :=
  ⟨ownIndices_primitive, activeGuard_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
