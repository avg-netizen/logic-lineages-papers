module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeLiftCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode

theorem lowerSummand_calibration (table : List TiedLinear.Token) (x : Nat) (s : NormalForm.Summand) :
    lowerSummand (table.map tokenData) x s.data = tokenData (TiedLinear.lowerSummand table x s) := by
  cases s with
  | «variable» j => exact tokenOfName_calibration table x j
  | phi i e => rfl
  | hyperPhi i e h => rfl
#print axioms lowerSummand_calibration

theorem lowerStep_calibration (table : List TiedLinear.Token) (x : Nat)
    (a : Int × NormalForm.Summand) (r : BlockRows.Row) :
    lowerStep (table.map tokenData) x (a.1, a.2.data) (BlockRowSubstitutionCode.rowData r) =
      BlockRowSubstitutionCode.rowData
        (match TiedLinear.lowerSummand table x a.2 with
        | .parameter t => ((.add (.multiply a.1.toNat t) r.1.1,
            .add (.multiply (-a.1).toNat t) r.1.2), r.2)
        | .occurrence s => (r.1, (a.1, s) :: r.2)) := by
  unfold lowerStep
  rw [lowerSummand_calibration]
  cases h : TiedLinear.lowerSummand table x a.2 with
  | parameter t => rfl
  | occurrence s =>
      simp only [tokenData, Nat.one_ne_zero, reduceIte, decodeItem, Encodable.encodek,
        Option.getD_some, BlockRowSubstitutionCode.rowData, List.map_cons]
#print axioms lowerStep_calibration

theorem lowerEntries_calibration (table : List TiedLinear.Token) (x : Nat)
    (positive negative : Term) (es : List (Int × NormalForm.Summand)) :
    lowerEntries (table.map tokenData) x positive.encode negative.encode
      (es.map (fun a => (a.1, a.2.data))) =
      BlockRowSubstitutionCode.rowData (TiedLinear.lowerEntries table x positive negative es) := by
  induction es with
  | nil => rfl
  | cons a es ih =>
      change lowerStep (table.map tokenData) x (a.1, a.2.data)
        (lowerEntries (table.map tokenData) x positive.encode negative.encode
          (es.map (fun a => (a.1, a.2.data)))) = _
      rw [ih]
      exact lowerStep_calibration table x a (TiedLinear.lowerEntries table x positive negative es)
#print axioms lowerEntries_calibration

theorem lowerRow_calibration (table : List TiedLinear.Token) (x : Nat) (r : NormalForm.Row) :
    lowerRow (table.map tokenData) x (NormalForm.rowData r) =
      BlockRowSubstitutionCode.rowData (TiedLinear.lowerRow table x r) :=
  lowerEntries_calibration table x (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2
#print axioms lowerRow_calibration

theorem lowerAtom_calibration (table : List TiedLinear.Token) (x : Nat) (a : NormalForm.Atom) :
    lowerAtom (table.map tokenData) x a.data =
      BlockFormulaSubstitutionCode.atomData (TiedLinear.lowerAtom table x a) := by
  cases a with
  | nonnegative r =>
      exact congrArg (fun d : BlockRowSubstitutionCode.RowData => ((0, 0, d) : BlockFormulaSubstitutionCode.AtomData))
        (lowerRow_calibration table x r)
  | divisible m r =>
      exact congrArg (fun d : BlockRowSubstitutionCode.RowData => ((1, m, d) : BlockFormulaSubstitutionCode.AtomData))
        (lowerRow_calibration table x r)
#print axioms lowerAtom_calibration

theorem lowerEncodedAtom_calibration (table : List TiedLinear.Token) (x : Nat) (a : NormalForm.Atom) :
    lowerEncodedAtom (table.map tokenData) x (Encodable.encode a.data) =
      Encodable.encode (BlockFormulaSubstitutionCode.atomData (TiedLinear.lowerAtom table x a)) := by
  unfold lowerEncodedAtom
  simp only [LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some]
  rw [lowerAtom_calibration]
#print axioms lowerEncodedAtom_calibration

theorem literalLowerCalibration : TiedLinearCodeTargets.LiteralLowerCalibration := by
  intro table x p
  change LinearRows.Code.mapAtoms (lowerEncodedAtom (table.map tokenData) x) p.encode =
    BlockFormulaSubstitutionCode.formulaCode (TiedLinear.lowerFormula table x p)
  induction p with
  | truth =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x) 0 0 (by decide)
  | falsity =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x) 0 1 (by decide)
  | atom a =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode,
        lowerEncodedAtom_calibration table x a] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x)
          (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode, hp] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x) p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode,
        Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x)
          (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [NormalForm.Formula.encode, TiedLinear.lowerFormula, BlockFormulaSubstitutionCode.formulaCode,
        Nat.unpair_pair, hp, hq] using
        BlockFormulaSubstitutionCodeProof.map_step (lowerEncodedAtom (table.map tokenData) x)
          (Nat.pair p.encode q.encode) 5 (by decide)
#print axioms literalLowerCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
