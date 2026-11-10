module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTokenCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode

theorem liftRow_calibration (table : List TiedLinear.Token) (x : Nat) (r : BlockRows.Row) :
    liftRow (table.map tokenData) x (BlockRowSubstitutionCode.rowData r) =
      NormalForm.rowData (TiedLinear.liftRow table x r) := by
  simp only [liftRow, BlockRowSubstitutionCode.rowData, TiedLinear.liftRow,
    NormalForm.rowData, List.map_cons, List.map_map, Function.comp_def,
    NormalForm.Summand.data, variableItem]
  change (0, (1, variableItem (tokenName (table.map tokenData) x (tokenData (.parameter r.1.1)))) ::
    (-1, variableItem (tokenName (table.map tokenData) x (tokenData (.parameter r.1.2)))) ::
    r.2.map (fun a => (a.1, variableItem (tokenName (table.map tokenData) x (tokenData (.occurrence a.2)))))) = _
  simp only [tokenName_calibration, variableItem]
#print axioms liftRow_calibration

theorem liftAtom_calibration (table : List TiedLinear.Token) (x : Nat) (a : BlockRows.Atom) :
    liftAtom (table.map tokenData) x (BlockFormulaSubstitutionCode.atomData a) =
      (TiedLinear.liftAtom table x a).data := by
  cases a with
  | nonnegative r =>
      exact congrArg (fun d : NormalForm.Code.RowData => ((0, 0, d) : NormalForm.Code.AtomData))
        (liftRow_calibration table x r)
  | divisible m r =>
      exact congrArg (fun d : NormalForm.Code.RowData => ((1, m, d) : NormalForm.Code.AtomData))
        (liftRow_calibration table x r)
#print axioms liftAtom_calibration

theorem liftEncodedAtom_calibration (table : List TiedLinear.Token) (x : Nat) (a : BlockRows.Atom) :
    liftEncodedAtom (table.map tokenData) x (Encodable.encode (BlockFormulaSubstitutionCode.atomData a)) =
      Encodable.encode (TiedLinear.liftAtom table x a).data := by
  unfold liftEncodedAtom
  rw [BlockFormulaSubstitutionCodeProof.decode_atomData, liftAtom_calibration]
#print axioms liftEncodedAtom_calibration

theorem literalLiftCalibration : TiedLinearCodeTargets.LiteralLiftCalibration := by
  intro table x p
  change LinearRows.Code.mapAtoms (liftEncodedAtom (table.map tokenData) x)
    (BlockFormulaSubstitutionCode.formulaCode p) = (TiedLinear.liftFormula table x p).encode
  induction p with
  | truth =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x) 0 0 (by decide)
  | falsity =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x) 0 1 (by decide)
  | atom a =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode,
        liftEncodedAtom_calibration table x a] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x)
          (Encodable.encode (BlockFormulaSubstitutionCode.atomData a)) 2 (by decide)
  | negative p hp =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode, hp] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x)
          (BlockFormulaSubstitutionCode.formulaCode p) 3 (by decide)
  | conjunction p q hp hq =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode,
        Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x)
          (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p) (BlockFormulaSubstitutionCode.formulaCode q)) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [BlockFormulaSubstitutionCode.formulaCode, TiedLinear.liftFormula, NormalForm.Formula.encode,
        Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (liftEncodedAtom (table.map tokenData) x)
          (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p) (BlockFormulaSubstitutionCode.formulaCode q)) 5 (by decide)
#print axioms literalLiftCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
