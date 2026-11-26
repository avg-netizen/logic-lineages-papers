module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeRowCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
open PlainBlockProjectionCode

theorem formula_step (n tag : Nat) (ht : tag < 6) :
    formula (6 * n + tag) =
      if tag = 0 then 0
      else if tag = 1 then 1
      else if tag = 2 then atom (BlockFormulaSubstitutionCode.decodeAtom n)
      else if tag = 3 then WindowCode.negative (formula n)
      else 8 * Nat.pair (formula n.unpair.1) (formula n.unpair.2) + (tag + 2) := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [formula, hm, hd]
#print axioms formula_step

theorem literalFormulaCompilation : PlainBlockProjectionCodeTargets.LiteralFormulaCompilation := by
  intro p
  induction p with
  | truth =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, BlockRows.Formula.compile,
        Matrix.encode, Nat.reduceEqDiff, reduceIte] using formula_step 0 0 (by decide)
  | falsity =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, BlockRows.Formula.compile,
        Matrix.encode, Nat.reduceEqDiff, reduceIte] using formula_step 0 1 (by decide)
  | atom a =>
      change formula (6 * Encodable.encode (BlockFormulaSubstitutionCode.atomData a) + 2) = _
      rw [formula_step _ 2 (by decide)]
      simp only [Nat.reduceEqDiff, reduceIte, BlockFormulaSubstitutionCodeProof.decode_atomData]
      exact literalAtomCalibration a
  | negative p hp =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, BlockRows.Formula.compile,
        Matrix.encode, Nat.reduceEqDiff, reduceIte, WindowCode.negative, hp] using
        formula_step (BlockFormulaSubstitutionCode.formulaCode p) 3 (by decide)
  | conjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, BlockRows.Formula.compile,
        Matrix.encode, Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, hp, hq] using
        formula_step (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p)
          (BlockFormulaSubstitutionCode.formulaCode q)) 4 (by decide)
  | disjunction p q hp hq =>
      simpa only [BlockFormulaSubstitutionCode.formulaCode, BlockRows.Formula.compile,
        Matrix.encode, Nat.reduceEqDiff, reduceIte, Nat.unpair_pair, hp, hq] using
        formula_step (Nat.pair (BlockFormulaSubstitutionCode.formulaCode p)
          (BlockFormulaSubstitutionCode.formulaCode q)) 5 (by decide)
#print axioms literalFormulaCompilation

theorem any_calibration (ps : List Matrix) :
    WindowCode.any (ps.map Matrix.encode) = (Matrix.any ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change WindowCode.disjunction p.encode (WindowCode.any (ps.map Matrix.encode)) =
        WindowCode.disjunction p.encode (Matrix.any ps).encode
      rw [ih]
#print axioms any_calibration

theorem literalReadoutCalibration : PlainBlockProjectionCodeTargets.LiteralReadoutCalibration := by
  intro states
  unfold readout
  rw [← any_calibration]
  simp only [List.map_map, Function.comp_def, PlainBlockDispatchCode.stateData]
  apply congrArg WindowCode.any
  apply List.map_congr_left
  intro s hs
  exact literalFormulaCompilation s.2
#print axioms literalReadoutCalibration

theorem literalProjectorCalibration : PlainBlockProjectionCodeTargets.LiteralProjectorCalibration := by
  intro bound p
  change readout (PlainBlockDispatchCode.run bound.length
    ([(bound, p)].map PlainBlockDispatchCode.stateData)) = _
  rw [PlainBlockDispatchCodeProof.literalRunCalibration, literalReadoutCalibration]
  rfl
#print axioms literalProjectorCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
