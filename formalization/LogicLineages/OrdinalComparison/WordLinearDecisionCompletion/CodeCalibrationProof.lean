module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Targets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
open PolynomialGraphCompletion LayeredComparison.SnyatkovCompletion

private theorem decode_atom_data (a : Atom) :
    Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [Code.decodeAtom, Encodable.encodek, Option.getD_some]

private theorem decode_normal_atom_data (a : NormalForm.Atom) :
    LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some]

theorem code_lift_row (x : Nat) (r : Row) :
    Code.liftRow x r = NormalForm.rowData (liftRow x r) := by
  simp [Code.liftRow, liftRow, NormalForm.rowData, NormalForm.Summand.data,
    List.map_map, Function.comp_def]

theorem code_lift_atom (x : Nat) (a : Atom) :
    Code.liftAtom x a.data = (liftAtom x a).data := by
  cases a <;> simp only [Atom.data, Code.liftAtom, liftAtom, NormalForm.Atom.data, code_lift_row]

theorem code_lower_item (x : Nat) (s : NormalForm.Summand) :
    Code.lowerItem x s.data = lowerSummand x s := by
  cases s <;> simp [Code.lowerItem, NormalForm.Summand.data, lowerSummand]

theorem code_lower_row (x : Nat) (r : NormalForm.Row) :
    Code.lowerRow x (NormalForm.rowData r) = lowerRow x r := by
  simp [Code.lowerRow, NormalForm.rowData, lowerRow, List.map_map,
    Function.comp_def, code_lower_item]

theorem code_lower_atom (x : Nat) (a : NormalForm.Atom) :
    Code.lowerAtom x a.data = (lowerAtom x a).data := by
  cases a <;> simp only [NormalForm.Atom.data, Code.lowerAtom, lowerAtom, Atom.data,
    code_lower_row]

private theorem mapAtoms_step (op : Nat → Nat) (payload tag : Nat) (ht : tag < 6) :
    LinearRows.Code.mapAtoms op (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * op payload + 2
      else if tag = 3 then 6 * LinearRows.Code.mapAtoms op payload + 3
      else 6 * Nat.pair (LinearRows.Code.mapAtoms op payload.unpair.1)
        (LinearRows.Code.mapAtoms op payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [LinearRows.Code.mapAtoms, hm, hd]

theorem lift_formula_code (x : Nat) (p : Formula) :
    Code.liftFormula x (Formula.encode p) = (liftFormula x p).encode := by
  unfold Code.liftFormula
  induction p with
  | bot =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a))) 0 1 (by decide)
  | top =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a))) 0 0 (by decide)
  | atom a =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode,
        decode_atom_data, code_lift_atom] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a)))
          (Encodable.encode a.data) 2 (by decide)
  | neg p ih =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode, ih] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a))) (Formula.encode p) 3 (by decide)
  | conj p q ihp ihq =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode, Nat.unpair_pair, ihp, ihq] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a)))
          (Nat.pair (Formula.encode p) (Formula.encode q)) 4 (by decide)
  | disj p q ihp ihq =>
      simpa [Formula.encode, liftFormula, NormalForm.Formula.encode, Nat.unpair_pair, ihp, ihq] using
        mapAtoms_step (fun a => Encodable.encode (Code.liftAtom x (Code.decodeAtom a)))
          (Nat.pair (Formula.encode p) (Formula.encode q)) 5 (by decide)

theorem lower_formula_code (x : Nat) (p : NormalForm.Formula) :
    Code.lowerFormula x p.encode = Formula.encode (lowerFormula x p) := by
  unfold Code.lowerFormula
  induction p with
  | truth =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a))) 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a))) 0 1 (by decide)
  | atom a =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode,
        decode_normal_atom_data, code_lower_atom] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a)))
          (Encodable.encode a.data) 2 (by decide)
  | negative p ih =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode, ih] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a))) p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode, Nat.unpair_pair, ihp, ihq] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a)))
          (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
      simpa [Formula.encode, lowerFormula, NormalForm.Formula.encode, Nat.unpair_pair, ihp, ihq] using
        mapAtoms_step (fun a => Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a)))
          (Nat.pair p.encode q.encode) 5 (by decide)

theorem literalCodeCalibration : Targets.LiteralCodeCalibration := by
  intro x p
  unfold Code.eliminate eliminate
  rw [lift_formula_code, LinearRowsCodeProof.eliminate_calibration, lower_formula_code]

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
