module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
open NormalForm SourceRows ClosedLinear

theorem constantMatrix_calibration (p : Formula) :
    Code.constantMatrix p.encode = constantMatrix p := by
  simp only [Code.constantMatrix, LinearRowsCodeProof.atoms_calibration,
    List.all_map, Function.comp_def, constantMatrix]
  apply congrArg (fun f : Atom → Bool => (LinearRows.atoms p).all f)
  funext a
  cases a <;> simp [LinearRows.Code.decodeAtom, Atom.data, Atom.row, rowData]

theorem constantAtom_calibration (a : Atom) : Code.constantAtom a.data = constantAtom a := by
  cases a <;> rfl

private theorem evaluateConstants_step (n tag : Nat) (ht : tag < 6) :
    Code.evaluateConstants (6 * n + tag) =
      if tag = 0 then true
      else if tag = 1 then false
      else if tag = 2 then Code.constantAtom (LinearRows.Code.decodeAtom n)
      else if tag = 3 then !Code.evaluateConstants n
      else if tag = 4 then Code.evaluateConstants n.unpair.1 && Code.evaluateConstants n.unpair.2
      else Code.evaluateConstants n.unpair.1 || Code.evaluateConstants n.unpair.2 := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [Code.evaluateConstants, hm, hd]

theorem evaluateConstants_calibration (p : Formula) :
    Code.evaluateConstants p.encode = evaluateConstants p := by
  induction p with
  | truth => simpa [Formula.encode, evaluateConstants] using evaluateConstants_step 0 0 (by decide)
  | falsity => simpa [Formula.encode, evaluateConstants] using evaluateConstants_step 0 1 (by decide)
  | atom a =>
      have h := evaluateConstants_step (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))),
        if_neg (by decide : ¬(2 = (1 : Nat))), if_pos rfl,
        LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some,
        constantAtom_calibration] at h
      exact h
  | negative p ih =>
      simpa [Formula.encode, evaluateConstants, ih] using evaluateConstants_step p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
      simpa [Formula.encode, evaluateConstants, Nat.unpair_pair, ihp, ihq] using
        evaluateConstants_step (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
      simpa [Formula.encode, evaluateConstants, Nat.unpair_pair, ihp, ihq] using
        evaluateConstants_step (Nat.pair p.encode q.encode) 5 (by decide)

theorem decideClosed_calibration (p : QFormula) :
    Code.decideClosed p.encode = decideClosed p := by
  simp only [Code.decideClosed, decideClosed,
    QuantifiedLinearProof.admissible_calibration, QuantifiedLinearProof.eliminate_calibration,
    constantMatrix_calibration, evaluateConstants_calibration]

theorem literalCodeCalibration : ClosedLinearTargets.LiteralCodeCalibration :=
  ⟨constantMatrix_calibration, evaluateConstants_calibration, decideClosed_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
