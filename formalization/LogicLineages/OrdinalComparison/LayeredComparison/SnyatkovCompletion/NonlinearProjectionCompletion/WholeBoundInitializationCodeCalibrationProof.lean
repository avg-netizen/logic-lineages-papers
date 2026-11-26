module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeFormulaCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProof
open WholeBoundInitializationCode

theorem entries_calibration (bound : List Nat) (positive negative : Term)
    (es : List (Int × NormalForm.Summand)) :
    entries bound positive.encode negative.encode (es.map (fun a => (a.1, a.2.data))) =
      BlockRowSubstitutionCode.rowData (WholeBoundInitialization.entries bound positive negative es) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      change step bound (a.1, a.2.data)
        (entries bound positive.encode negative.encode (es.map (fun a => (a.1, a.2.data)))) = _
      rw [ih]
      conv_rhs => rw [WholeBoundInitialization.entries]
      unfold step
      simp only [BlockRowSubstitutionCodeProof.item_name]
      by_cases h : bound.contains a.2.name = true
      · simp only [if_pos h, BlockRowSubstitutionCode.rowData, List.map_cons] <;> rfl
      · simp only [if_neg h, BlockRowSubstitutionCode.rowData,
          NormalFormCodeProof.item_term, WindowCode.add, WindowCode.multiply, Term.encode] <;> rfl
#print axioms entries_calibration

theorem literalRowCalibration : WholeBoundInitializationCodeTargets.LiteralRowCalibration := by
  intro bound r
  exact entries_calibration bound (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2
#print axioms literalRowCalibration

theorem literalAtomCalibration : WholeBoundInitializationCodeTargets.LiteralAtomCalibration := by
  intro bound a
  cases a with
  | nonnegative row =>
      exact congrArg (fun d : RowData => ((0, 0, d) : AtomData))
        (literalRowCalibration bound row)
  | divisible modulus row =>
      exact congrArg (fun d : RowData => ((1, modulus, d) : AtomData))
        (literalRowCalibration bound row)
#print axioms literalAtomCalibration

theorem decode_atomData (a : NormalForm.Atom) :
    decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [decodeAtom, Encodable.encodek, Option.getD_some]
#print axioms decode_atomData

theorem encodedAtom_calibration (bound : List Nat) (a : NormalForm.Atom) :
    encodedAtom bound (Encodable.encode a.data) =
      Encodable.encode (BlockFormulaSubstitutionCode.atomData (WholeBoundInitialization.atom bound a)) := by
  unfold encodedAtom
  rw [decode_atomData, literalAtomCalibration bound a]
#print axioms encodedAtom_calibration

theorem literalFormulaCalibration : WholeBoundInitializationCodeTargets.LiteralFormulaCalibration := by
  intro bound p
  change LinearRows.Code.mapAtoms (encodedAtom bound) p.encode =
    BlockFormulaSubstitutionCode.formulaCode (WholeBoundInitialization.«initialize» bound p)
  induction p with
  | truth =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound) 0 0 (by decide)
  | falsity =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound) 0 1 (by decide)
  | atom a =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode, encodedAtom_calibration bound a] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound)
          (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode, hp] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound) p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode, Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound)
          (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [NormalForm.Formula.encode, WholeBoundInitialization.«initialize»,
        BlockFormulaSubstitutionCode.formulaCode, Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (encodedAtom bound)
          (Nat.pair p.encode q.encode) 5 (by decide)
#print axioms literalFormulaCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeProof
