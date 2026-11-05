module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
open NormalForm (Row Atom Formula rowData)
open ZeroValuation

theorem projectRow_calibration (r : Row) : Code.projectRow (rowData r) = rowData (projectRow r) := by
  simp only [Code.projectRow, projectRow, rowData, List.map_map, Function.comp_def,
    BoundedRowsCodeProof.itemValue_calibration, List.map_nil]

theorem projectAtom_calibration (a : Atom) : Code.projectAtom a.data = (projectAtom a).data := by
  cases a <;> simp only [Code.projectAtom, projectAtom, Atom.data, projectRow_calibration]

private theorem project_step (payload tag : Nat) (ht : tag < 6) :
    Code.project (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * Encodable.encode (Code.projectAtom (LinearRows.Code.decodeAtom payload)) + 2
      else if tag = 3 then 6 * Code.project payload + 3
      else 6 * Nat.pair (Code.project payload.unpair.1) (Code.project payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  unfold Code.project
  rw [LinearRows.Code.mapAtoms, hm, hd]

theorem project_calibration (p : Formula) : Code.project p.encode = (project p).encode := by
  induction p with
  | truth => simpa [Formula.encode, project] using project_step 0 0 (by decide)
  | falsity => simpa [Formula.encode, project] using project_step 0 1 (by decide)
  | atom a =>
      have h := project_step (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))),
        if_neg (by decide : ¬(2 = (1 : Nat))), if_pos rfl,
        LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some,
        projectAtom_calibration] at h
      exact h
  | negative p ih => simpa [Formula.encode, project, ih] using project_step p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
      simpa [Formula.encode, project, Nat.unpair_pair, ihp, ihq] using
        project_step (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
      simpa [Formula.encode, project, Nat.unpair_pair, ihp, ihq] using
        project_step (Nat.pair p.encode q.encode) 5 (by decide)

theorem evaluate_calibration (p : Formula) : Code.evaluate p.encode = evaluate p := by
  unfold Code.evaluate evaluate
  rw [project_calibration, ClosedLinearProof.evaluateConstants_calibration]

theorem literalCodeCalibration : ZeroValuationTargets.LiteralCodeCalibration :=
  ⟨projectRow_calibration, projectAtom_calibration, project_calibration, evaluate_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
