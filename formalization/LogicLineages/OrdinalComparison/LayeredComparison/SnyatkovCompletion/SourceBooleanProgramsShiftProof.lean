module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
open NormalForm CommonLayerSyntax SourceBooleanPrograms

theorem shiftItem_calibration (d : Nat) (s : Summand) : Code.shiftItem d s.data = (shiftSummand d s).data := by
  cases s <;> rfl

theorem shiftRow_calibration (d : Nat) (r : Row) : Code.shiftRow d (rowData r) = rowData (shiftRow d r) := by
  simp only [Code.shiftRow, shiftRow, rowData, List.map_map, Function.comp_def, shiftItem_calibration]

theorem shiftAtom_calibration (d : Nat) (a : Atom) : Code.shiftAtom d a.data = (shiftAtom d a).data := by
  cases a <;> simp only [Code.shiftAtom, shiftAtom, Atom.data, shiftRow_calibration]

private theorem shift_step (d payload tag : Nat) (ht : tag < 6) :
    Code.shift d (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * Encodable.encode (Code.shiftAtom d (LinearRows.Code.decodeAtom payload)) + 2
      else if tag = 3 then 6 * Code.shift d payload + 3
      else 6 * Nat.pair (Code.shift d payload.unpair.1) (Code.shift d payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  unfold Code.shift
  rw [LinearRows.Code.mapAtoms, hm, hd]

theorem literalNameShift : SourceBooleanProgramsTargets.LiteralNameShift := by
  intro d p
  induction p with
  | truth => simpa [Formula.encode, shift] using shift_step d 0 0 (by decide)
  | falsity => simpa [Formula.encode, shift] using shift_step d 0 1 (by decide)
  | atom a =>
      have h := shift_step d (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))), if_neg (by decide : ¬(2 = (1 : Nat))),
        if_pos rfl, LinearRows.Code.decodeAtom, Encodable.encodek, Option.getD_some,
        shiftAtom_calibration] at h
      exact h
  | negative p ih => simpa [Formula.encode, shift, ih] using shift_step d p.encode 3 (by decide)
  | conjunction p q ihp ihq =>
      simpa [Formula.encode, shift, Nat.unpair_pair, ihp, ihq] using
        shift_step d (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q ihp ihq =>
      simpa [Formula.encode, shift, Nat.unpair_pair, ihp, ihq] using
        shift_step d (Nat.pair p.encode q.encode) 5 (by decide)

private theorem relation_shift (d : Nat) (strict : Bool) (x y : Nat) :
    shift d (SourceRows.relation strict x y) = SourceRows.relation strict (d + x) (d + y) := by
  cases strict <;> rfl

private theorem output_shift (d s : Nat) (t : BaseTerm) :
    d + SourceTermGraph.output s t = SourceTermGraph.output (d + s) t := by
  have h := SourceTermGraphSupportProof.nodeCount_pos t
  unfold SourceTermGraph.output
  omega

theorem actualPredicateShift : SourceBooleanProgramsTargets.ActualPredicateShift := by
  intro d s p
  induction p generalizing s with
  | equal a b =>
      simp only [SourceBooleanGraph.predicate, relation_shift, output_shift, Nat.add_assoc]
  | less a b =>
      simp only [SourceBooleanGraph.predicate, relation_shift, output_shift, Nat.add_assoc]
  | negative p ih => simp only [SourceBooleanGraph.predicate, shift, ih]
  | conjunction p q ihp ihq =>
      simp only [SourceBooleanGraph.predicate, shift, ihp, ihq, Nat.add_assoc]
  | existsNat i p ih => rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
