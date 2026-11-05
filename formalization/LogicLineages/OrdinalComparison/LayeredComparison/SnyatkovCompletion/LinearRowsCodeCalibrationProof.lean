module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
open NormalForm LinearRows

private theorem item_name (s : Summand) : s.data.2.1 = s.name := by
  cases s <;> rfl

private theorem item_linear (i : Nat) (s : Summand) :
    (s.data.1 == 0 || s.data.2.1 != i) = summandLinear i s := by
  cases s <;> rfl

private theorem atom_row (a : Atom) : a.data.2.2 = rowData a.row := by
  cases a <;> rfl

theorem rowConst_calibration (z : Int) : Code.rowConst z = rowData (rowConst z) := rfl

theorem rowAdd_calibration (r s : Row) :
    Code.rowAdd (rowData r) (rowData s) = rowData (rowAdd r s) := by
  simp only [Code.rowAdd, rowAdd, rowData, List.map_append]

theorem rowScale_calibration (z : Int) (r : Row) :
    Code.rowScale z (rowData r) = rowData (rowScale z r) := by
  simp only [Code.rowScale, rowScale, rowData, List.map_map, Function.comp_def]

theorem leading_calibration (i : Nat) (r : Row) :
    Code.leading i (rowData r) = leading i r := by
  simp only [Code.leading, leading, rowData, List.map_map, Function.comp_def, item_name]

theorem remainder_calibration (i : Nat) (r : Row) :
    Code.remainder i (rowData r) = rowData (remainder i r) := by
  simp only [Code.remainder, remainder, rowData, List.filter_map, Function.comp_def, item_name]

theorem rowLinear_calibration (i : Nat) (r : Row) :
    Code.rowLinear i (rowData r) = rowLinear i r := by
  simp only [Code.rowLinear, rowLinear, rowData, List.all_map, Function.comp_def, item_linear]

private theorem decodeAtom_data (a : Atom) :
    Code.decodeAtom (Encodable.encode a.data) = a.data := by
  simp only [Code.decodeAtom, Encodable.encodek, Option.getD_some]

private theorem decodeUnit_data (a : UnitAtom) :
    Code.decodeUnit (Encodable.encode a.data) = a.data := by
  simp only [Code.decodeUnit, Encodable.encodek, Option.getD_some]

private theorem mapAtoms_step (op : Nat → Nat) (payload tag : Nat) (ht : tag < 6) :
    Code.mapAtoms op (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * op payload + 2
      else if tag = 3 then 6 * Code.mapAtoms op payload + 3
      else 6 * Nat.pair (Code.mapAtoms op payload.unpair.1)
        (Code.mapAtoms op payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.mapAtoms, hm, hd]

private theorem atoms_step (payload tag : Nat) (ht : tag < 6) :
    Code.atoms (6 * payload + tag) =
      if tag = 0 then [] else if tag = 1 then []
      else if tag = 2 then [payload]
      else if tag = 3 then Code.atoms payload
      else Code.atoms payload.unpair.1 ++ Code.atoms payload.unpair.2 := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.atoms, hm, hd]

theorem atoms_calibration (p : Formula) :
    Code.atoms p.encode = (atoms p).map (fun a => Encodable.encode a.data) := by
  induction p with
  | truth =>
      simpa [Formula.encode, atoms] using atoms_step 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, atoms] using atoms_step 0 1 (by decide)
  | atom a =>
      simpa [Formula.encode, atoms] using atoms_step (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [Formula.encode, atoms, hp] using atoms_step p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode, atoms, Nat.unpair_pair, hp, hq, List.map_append] using
        atoms_step (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode, atoms, Nat.unpair_pair, hp, hq, List.map_append] using
        atoms_step (Nat.pair p.encode q.encode) 5 (by decide)

theorem unit_atoms_calibration (u : UnitFormula) :
    Code.atoms (unitEncode u) = u.atoms.map (fun a => Encodable.encode a.data) := by
  induction u with
  | bot =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
        using atoms_step 0 1 (by decide)
  | top =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
        using atoms_step 0 0 (by decide)
  | atom a =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
        using atoms_step (Encodable.encode a.data) 2 (by decide)
  | neg p hp =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms, hp]
        using atoms_step (unitEncode p) 3 (by decide)
  | conj p q hp hq =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        Nat.unpair_pair, hp, hq, List.map_append] using
        atoms_step (Nat.pair (unitEncode p) (unitEncode q)) 4 (by decide)
  | disj p q hp hq =>
      simpa [unitEncode, LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        Nat.unpair_pair, hp, hq, List.map_append] using
        atoms_step (Nat.pair (unitEncode p) (unitEncode q)) 5 (by decide)

theorem isLinear_calibration (i : Nat) (p : Formula) :
    Code.isLinear i p.encode = isLinear i p := by
  simp only [Code.isLinear, isLinear, atoms_calibration, List.all_map, Function.comp_def,
    decodeAtom_data, atom_row, rowLinear_calibration]

theorem weight_calibration (i : Nat) (a : Atom) : Code.weight i a.data = weight i a := by
  simp only [Code.weight, weight, atom_row, leading_calibration]

theorem coefficientModulus_calibration (i : Nat) (p : Formula) :
    Code.coefficientModulus i p.encode = coefficientModulus i p := by
  simp only [Code.coefficientModulus, coefficientModulus, atoms_calibration,
    List.map_map, Function.comp_def, decodeAtom_data, weight_calibration]

theorem nonzeroSign_calibration (z : Int) : Code.nonzeroSign z = (nonzeroSign z).value := by
  by_cases h : 0 < z <;>
    simp [Code.nonzeroSign, nonzeroSign, h,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value]

theorem adjustAtom_calibration (i M : Nat) (a : Atom) :
    Code.adjustAtom i M a.data = (adjustAtom i M a).data := by
  cases a with
  | nonnegative r =>
      simp only [Code.adjustAtom, Atom.data, adjustAtom, leading_calibration,
        remainder_calibration]
      by_cases h : leading i r = 0
      · simp only [h, ite_true, UnitAtom.data,
          LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value]
      · simp only [h, ↓reduceIte, UnitAtom.data,
          nonzeroSign_calibration, rowScale_calibration]
  | divisible m r =>
      simp only [Code.adjustAtom, Atom.data, adjustAtom, leading_calibration,
        remainder_calibration]
      by_cases h : leading i r = 0
      · simp only [h, ite_true, UnitAtom.data,
          LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value]
      · simp only [h, Nat.one_ne_zero, ↓reduceIte, UnitAtom.data,
          nonzeroSign_calibration, rowScale_calibration]

theorem adjust_calibration (i M : Nat) (p : Formula) :
    Code.adjust i M p.encode = unitEncode (adjust i M p) := by
  let op : Nat → Nat := fun a => Encodable.encode (Code.adjustAtom i M (Code.decodeAtom a))
  change Code.mapAtoms op p.encode = _
  induction p with
  | truth =>
      simpa [Formula.encode, adjust, unitEncode] using mapAtoms_step op 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, adjust, unitEncode] using mapAtoms_step op 0 1 (by decide)
  | atom a =>
      simpa [Formula.encode, adjust, unitEncode, op, decodeAtom_data,
        adjustAtom_calibration] using
        mapAtoms_step op (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [Formula.encode, adjust, unitEncode, hp] using
        mapAtoms_step op p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode, adjust, unitEncode, Nat.unpair_pair, hp, hq] using
        mapAtoms_step op (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode, adjust, unitEncode, Nat.unpair_pair, hp, hq] using
        mapAtoms_step op (Nat.pair p.encode q.encode) 5 (by decide)

theorem normalize_calibration (i : Nat) (p : Formula) :
    Code.normalize i p.encode = unitEncode (normalize i p) := by
  simp only [Code.normalize, normalize, coefficientModulus_calibration,
    Code.conjunction, Code.unitAtom, unitEncode, UnitAtom.data,
    LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value,
    rowConst_calibration, adjust_calibration]

theorem atomPeriod_calibration (a : UnitAtom) : Code.atomPeriod a.data = a.period := by
  cases a <;> rfl

theorem atomCutoffs_calibration (a : UnitAtom) :
    Code.atomCutoffs a.data = a.cutoffs.map rowData := by
  cases a with
  | nonnegative s r =>
      cases s <;> simp [Code.atomCutoffs, UnitAtom.data, UnitAtom.cutoffs,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value,
        rowScale_calibration, rowAdd_calibration, rowConst_calibration]
  | divisible m s r =>
      simp only [Code.atomCutoffs, UnitAtom.data, if_neg (by decide : ¬(1 = (0 : Nat))),
        UnitAtom.cutoffs, List.map_nil]

theorem period_calibration (u : UnitFormula) : Code.period (unitEncode u) = period u := by
  simp only [Code.period, period, unit_atoms_calibration, List.map_map, Function.comp_def,
    decodeUnit_data, atomPeriod_calibration]

theorem cutoffs_calibration (u : UnitFormula) :
    Code.cutoffs (unitEncode u) = (cutoffs u).map rowData := by
  simp only [Code.cutoffs, cutoffs, unit_atoms_calibration, List.flatMap_map,
    decodeUnit_data, atomCutoffs_calibration,
    List.map_cons, rowConst_calibration, List.map_flatMap]

theorem instantiateAtom_calibration (b : Row) (a : UnitAtom) :
    Code.instantiateAtom (rowData b) a.data = (a.instantiate b).data := by
  cases a <;> simp only [Code.instantiateAtom, UnitAtom.instantiate, UnitAtom.data,
    Atom.data, rowScale_calibration, rowAdd_calibration]

theorem instantiate_calibration (u : UnitFormula) (b : Row) :
    Code.instantiate (unitEncode u) (rowData b) = (instantiate u b).encode := by
  let op : Nat → Nat := fun a => Encodable.encode (Code.instantiateAtom (rowData b) (Code.decodeUnit a))
  change Code.mapAtoms op (unitEncode u) = _
  induction u with
  | bot =>
      simpa [Formula.encode, instantiate, unitEncode] using mapAtoms_step op 0 1 (by decide)
  | top =>
      simpa [Formula.encode, instantiate, unitEncode] using mapAtoms_step op 0 0 (by decide)
  | atom a =>
      simpa [Formula.encode, instantiate, unitEncode, op, decodeUnit_data,
        instantiateAtom_calibration] using
        mapAtoms_step op (Encodable.encode a.data) 2 (by decide)
  | neg p hp =>
      simpa [Formula.encode, instantiate, unitEncode, hp] using
        mapAtoms_step op (unitEncode p) 3 (by decide)
  | conj p q hp hq =>
      simpa [Formula.encode, instantiate, unitEncode, Nat.unpair_pair, hp, hq] using
        mapAtoms_step op (Nat.pair (unitEncode p) (unitEncode q)) 4 (by decide)
  | disj p q hp hq =>
      simpa [Formula.encode, instantiate, unitEncode, Nat.unpair_pair, hp, hq] using
        mapAtoms_step op (Nat.pair (unitEncode p) (unitEncode q)) 5 (by decide)

theorem guarded_calibration (u : UnitFormula) : Code.guarded (unitEncode u) = unitEncode (guarded u) := by
  simp only [Code.guarded, guarded, Code.conjunction, Code.unitAtom, unitEncode, UnitAtom.data,
    LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Sign.value, rowConst_calibration]

theorem unitEliminate_calibration (u : UnitFormula) :
    Code.unitEliminate (unitEncode u) = (unitEliminate u).encode := by
  unfold Code.unitEliminate unitEliminate
  rw [cutoffs_calibration, period_calibration, ← BoundedRowsCodeProof.any_calibration]
  apply congrArg BoundedRows.Code.any
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro b hb
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_def, guarded_calibration, rowConst_calibration,
    rowAdd_calibration, instantiate_calibration]

theorem eliminate_calibration (i : Nat) (p : Formula) :
    Code.eliminate i p.encode = (eliminate i p).encode := by
  simp only [Code.eliminate, eliminate, normalize_calibration, unitEliminate_calibration]

theorem literalCodeCalibration : LinearRowsTargets.LiteralCodeCalibration :=
  ⟨isLinear_calibration, normalize_calibration, unitEliminate_calibration, eliminate_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
