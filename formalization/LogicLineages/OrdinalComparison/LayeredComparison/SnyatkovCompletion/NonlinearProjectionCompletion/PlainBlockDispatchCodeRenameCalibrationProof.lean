module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeFormulaCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode

theorem renameItem_calibration (i j : Nat) (s : NormalForm.Summand) :
    renameItem i j s.data = (PlainBlockSplit.renameSummand i j s).data := by
  cases s <;> rfl
#print axioms renameItem_calibration

theorem renameRow_calibration (i j : Nat) (r : BlockRows.Row) :
    renameRow i j (BlockRowSubstitutionCode.rowData r) =
      BlockRowSubstitutionCode.rowData (PlainBlockSplit.renameRow i j r) := by
  simp only [renameRow, BlockRowSubstitutionCode.rowData, PlainBlockSplit.renameRow,
    List.map_map, Function.comp_def, renameItem_calibration]
#print axioms renameRow_calibration

theorem renameEncodedAtom_calibration (i j : Nat) (a : BlockRows.Atom) :
    renameEncodedAtom i j (Encodable.encode (BlockFormulaSubstitutionCode.atomData a)) =
      Encodable.encode (BlockFormulaSubstitutionCode.atomData (match a with
        | .nonnegative r => .nonnegative (PlainBlockSplit.renameRow i j r)
        | .divisible m r => .divisible m (PlainBlockSplit.renameRow i j r))) := by
  simp only [renameEncodedAtom, BlockFormulaSubstitutionCodeProof.decode_atomData]
  cases a <;> simp only [BlockFormulaSubstitutionCode.atomData, renameRow_calibration]
#print axioms renameEncodedAtom_calibration

theorem rename_calibration (i j : Nat) (p : BlockRows.Formula) :
    rename i j (BlockFormulaSubstitutionCode.formulaCode p) =
      BlockFormulaSubstitutionCode.formulaCode (PlainBlockSplit.rename i j p) := by
  change LinearRows.Code.mapAtoms (renameEncodedAtom i j) (BlockFormulaSubstitutionCode.formulaCode p) = _
  induction p with
  | truth =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.rename,
        Nat.reduceEqDiff, reduceIte] using
        BlockFormulaSubstitutionCodeProof.map_step (renameEncodedAtom i j) 0 0 (by decide)
  | falsity =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.rename,
        Nat.reduceEqDiff, reduceIte] using
        BlockFormulaSubstitutionCodeProof.map_step (renameEncodedAtom i j) 0 1 (by decide)
  | atom a =>
      change LinearRows.Code.mapAtoms (renameEncodedAtom i j)
        (6 * Encodable.encode (BlockFormulaSubstitutionCode.atomData a) + 2) = _
      rw [BlockFormulaSubstitutionCodeProof.map_step _ _ 2 (by decide)]
      simp only [Nat.reduceEqDiff, reduceIte, renameEncodedAtom_calibration]
      cases a <;> rfl
  | negative p hp =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.rename,
        Nat.reduceEqDiff, reduceIte, hp] using
        BlockFormulaSubstitutionCodeProof.map_step (renameEncodedAtom i j)
          (BlockFormulaSubstitutionCode.formulaCode p) 3 (by decide)
  | conjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.rename,
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (renameEncodedAtom i j)
          (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p) (BlockFormulaSubstitutionCode.formulaCode q)) 4 (by decide)
  | disjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, PlainBlockSplit.rename,
        Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (renameEncodedAtom i j)
          (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p) (BlockFormulaSubstitutionCode.formulaCode q)) 5 (by decide)
#print axioms rename_calibration

theorem literalRenameCalibration : PlainBlockDispatchCodeTargets.LiteralRenameCalibration := ⟨renameItem_calibration, renameRow_calibration, rename_calibration⟩
#print axioms literalRenameCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
