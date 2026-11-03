module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableEffectivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableProof
open NumberedNumericDecoding NumberedCodeParserTable NumberedCodeParserTableSupportProof NumberedCodeParserTableEffectivityProof

theorem codeTableCalibration : NumberedCodeParserTableTargets.ActualCodeTableCalibration := calibration
theorem codeTablePrimitive : NumberedCodeParserTableTargets.ActualCodeTablePrimitive := tablePrimitive

theorem codeDecodeSuccessPrimitive : NumberedCodeParserTableTargets.ActualCodeDecodeSuccessPrimitive := by
  intro n
  have h : Primrec (fun value => lookup (codeTable n value (value+1)) value) :=
    lookupPrimitive.comp ((tablePrimitive n).comp Primrec.id Primrec.succ) Primrec.id
  exact h.of_eq (by intro value; rw [calibration n value (value+1) value (Nat.le_refl _),validatedSuccess])

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeParserTableProof
