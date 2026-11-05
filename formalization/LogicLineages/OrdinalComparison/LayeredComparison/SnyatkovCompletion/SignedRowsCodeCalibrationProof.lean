module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProof
open NormalForm (Summand Row rowData Atom Formula)
open SignedRows

theorem item_calibration (i j : Nat) (d : Int) (s : Summand) :
    Code.item i j d s.data = (translateSummand i j d s).data := by
  cases s with
  | «variable» k =>
      by_cases hk : k = i <;>
        simp [Code.item, Summand.data, translateSummand, Summand.name, hk]
  | phi k e =>
      by_cases hk : k = i <;>
        simp [Code.item, Summand.data, translateSummand, Summand.name, hk]
  | hyperPhi k e h =>
      by_cases hk : k = i <;>
        simp [Code.item, Summand.data, translateSummand, Summand.name, hk]

theorem offset_calibration (i : Nat) (d : Int) (s : Summand) :
    Code.offset i d s.data = offset i d s := by
  cases s <;> simp [Code.offset, Summand.data, offset]

theorem row_calibration (i j : Nat) (d : Int) (row : Row) :
    Code.row i j d (rowData row) = rowData (rowTranslate i j d row) := by
  simp only [Code.row, rowData, rowTranslate, List.map_map, Function.comp_def,
    item_calibration, offset_calibration]

theorem atom_calibration (i j : Nat) (d : Int) (a : Atom) :
    Code.atom i j d a.data = (atomTranslate i j d a).data := by
  cases a <;> simp only [Code.atom, Atom.data, atomTranslate, row_calibration]

private theorem core_step (i j : Nat) (d : Int) (payload tag : Nat) (ht : tag < 6) :
    Code.core i j d (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * Encodable.encode (Code.atom i j d
        ((Encodable.decode payload : Option Code.AtomData).getD (0, 0, (0 : Int), []))) + 2
      else if tag = 3 then 6 * Code.core i j d payload + 3
      else 6 * Nat.pair (Code.core i j d payload.unpair.1)
        (Code.core i j d payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.core, hm, hd]

theorem core_calibration (i j : Nat) (d : Int) (p : Formula) :
    Code.core i j d p.encode = (core i j d p).encode := by
  induction p with
  | truth =>
      simpa [Formula.encode, core] using core_step i j d 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, core] using core_step i j d 0 1 (by decide)
  | atom a =>
      change Code.core i j d (6 * Encodable.encode a.data + 2) =
        6 * Encodable.encode (atomTranslate i j d a).data + 2
      have h := core_step i j d (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))),
        if_neg (by decide : ¬(2 = (1 : Nat))), if_pos rfl, Encodable.encodek] at h
      simpa only [Option.getD_some, atom_calibration] using h
  | negative p hp =>
      simpa [Formula.encode, core, hp] using core_step i j d p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode, core, Nat.unpair_pair, hp, hq] using
        core_step i j d (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode, core, Nat.unpair_pair, hp, hq] using
        core_step i j d (Nat.pair p.encode q.encode) 5 (by decide)

theorem anchorDomain_calibration (j : Nat) (d : Int) :
    Code.anchorDomain j d = (anchorDomain j d).encode := rfl

theorem substitute_calibration (i j : Nat) (d : Int) (p : Formula) :
    Code.substitute i j d p.encode = (substitute i j d p).encode := by
  unfold Code.substitute
  rw [anchorDomain_calibration, core_calibration, BoundedRowsCodeProof.formula_calibration]
  rfl

theorem literalCodeCalibration : SignedRowsTargets.LiteralCodeCalibration :=
  ⟨fun i j d s => ⟨item_calibration i j d s, offset_calibration i d s⟩,
    row_calibration, core_calibration, substitute_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProof
