module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
open BlockFormulaSubstitutionCode

theorem literalAtomCalibration : BlockFormulaSubstitutionCodeTargets.LiteralAtomCalibration := by
  intro i replacement a
  cases a with
  | nonnegative row =>
      exact congrArg (fun d : BlockRowSubstitutionCode.RowData => ((0, 0, d) : AtomData))
        (BlockRowSubstitutionCodeProof.literalRowCalibration i replacement row)
  | divisible modulus row =>
      exact congrArg (fun d : BlockRowSubstitutionCode.RowData => ((1, modulus, d) : AtomData))
        (BlockRowSubstitutionCodeProof.literalRowCalibration i replacement row)
#print axioms literalAtomCalibration

theorem decode_atomData (a : BlockRows.Atom) :
    decodeAtom (Encodable.encode (atomData a)) = atomData a := by
  simp only [decodeAtom, Encodable.encodek, Option.getD_some]
#print axioms decode_atomData

theorem literalEncodedAtomCalibration :
    BlockFormulaSubstitutionCodeTargets.LiteralEncodedAtomCalibration := by
  intro i replacement a
  unfold encodedAtom
  rw [decode_atomData, literalAtomCalibration]
#print axioms literalEncodedAtomCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
