module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsRecursionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainProof
open NormalForm (Formula)
open SingleNamePlain
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem admissible_calibration (i : Nat) (p : Formula) : Code.admissible i p.encode = admissible i p := by
  simp only [Code.admissible, admissible, MaximalPlainBranchProgramsProof.isPlain_calibration,
    MaximalPlainBranchProgramsProof.variables_calibration]

theorem existsEliminate_calibration (i : Nat) (p : Formula) :
    Code.existsEliminate i p.encode = (existsEliminate i p).encode := by
  unfold Code.existsEliminate existsEliminate
  rw [MaximalPlainBranchProgramsProof.cutoff_calibration,
    BoundedRowsCodeProof.bounded_calibration, MaximalPlainBranchProgramsProof.eliminate_calibration]
  rfl

theorem forallEliminate_calibration (i : Nat) (p : Formula) :
    Code.forallEliminate i p.encode = (forallEliminate i p).encode := by
  change ShiftedInputPrograms.Code.negative (Code.existsEliminate i (Formula.negative p).encode) = _
  rw [existsEliminate_calibration]
  rfl

theorem literalCodeCalibration : SingleNamePlainTargets.LiteralCodeCalibration :=
  fun i p => ⟨admissible_calibration i p, existsEliminate_calibration i p, forallEliminate_calibration i p⟩

attribute [local irreducible] MaximalPlainBranchPrograms.Code.isPlain
  MaximalPlainBranchPrograms.Code.variables MaximalPlainBranchPrograms.Code.cutoff
  MaximalPlainBranchPrograms.Code.eliminate BoundedRows.Code.bounded

theorem admissible_primitive : Primrec₂ Code.admissible := by
  have hp : Primrec₂ (fun i j : Nat => j == i) := Primrec.beq.comp Primrec.snd Primrec.fst
  have hn := (LinearRowsCodeProof.listAll_primitive hp).comp Primrec.fst
    (MaximalPlainBranchProgramsProof.variables_primitive.comp Primrec.snd)
  exact Primrec.and.comp (MaximalPlainBranchProgramsProof.isPlain_primitive.comp Primrec.snd) hn

theorem existsEliminate_primitive : Primrec₂ Code.existsEliminate := by
  have ha : Primrec (fun p : Nat × Nat => (p.1, MaximalPlainBranchPrograms.Code.cutoff p.2)) :=
    Primrec.fst.pair (MaximalPlainBranchProgramsProof.cutoff_primitive.comp Primrec.snd)
  have hb : Primrec (fun p : Nat × Nat =>
      BoundedRows.Code.bounded p.1 (MaximalPlainBranchPrograms.Code.cutoff p.2) p.2) :=
    BoundedRowsCodeProof.bounded_primitive.comp ha Primrec.snd
  exact ShiftedInputProgramsProof.disjunction_primitive.comp hb MaximalPlainBranchProgramsProof.eliminate_primitive

attribute [local irreducible] Code.existsEliminate

theorem forallEliminate_primitive : Primrec₂ Code.forallEliminate :=
  ShiftedInputProgramsProof.negative_primitive.comp
    (existsEliminate_primitive.comp Primrec.fst (ShiftedInputProgramsProof.negative_primitive.comp Primrec.snd))

theorem actualNumericPrograms : SingleNamePlainTargets.ActualNumericPrograms :=
  ⟨admissible_primitive, existsEliminate_primitive, forallEliminate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainProof
