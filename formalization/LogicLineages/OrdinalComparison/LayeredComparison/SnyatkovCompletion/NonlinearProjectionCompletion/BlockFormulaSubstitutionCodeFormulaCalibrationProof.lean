module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeAtomCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
open BlockFormulaSubstitutionCode

theorem map_step (op : Nat → Nat) (n tag : Nat) (ht : tag < 6) :
    LinearRows.Code.mapAtoms op (6 * n + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * op n + 2
      else if tag = 3 then 6 * LinearRows.Code.mapAtoms op n + 3
      else 6 * Nat.pair (LinearRows.Code.mapAtoms op n.unpair.1)
        (LinearRows.Code.mapAtoms op n.unpair.2) + tag := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [LinearRows.Code.mapAtoms, hm, hd]
#print axioms map_step

theorem literalFormulaCalibration :
    BlockFormulaSubstitutionCodeTargets.LiteralFormulaCalibration := by
  intro i replacement p
  change LinearRows.Code.mapAtoms (encodedAtom i replacement.encode) (formulaCode p) =
    formulaCode (p.substitute i replacement)
  induction p with
  | truth =>
      simpa [formulaCode, BlockRows.Formula.substitute] using
        map_step (encodedAtom i replacement.encode) 0 0 (by decide)
  | falsity =>
      simpa [formulaCode, BlockRows.Formula.substitute] using
        map_step (encodedAtom i replacement.encode) 0 1 (by decide)
  | atom a =>
      simpa [formulaCode, BlockRows.Formula.substitute,
        literalEncodedAtomCalibration i replacement a] using
        map_step (encodedAtom i replacement.encode) (Encodable.encode (atomData a)) 2 (by decide)
  | negative p hp =>
      simpa [formulaCode, BlockRows.Formula.substitute, hp] using
        map_step (encodedAtom i replacement.encode) (formulaCode p) 3 (by decide)
  | conjunction p q hp hq =>
      simpa [formulaCode, BlockRows.Formula.substitute, Nat.unpair_pair, hp, hq] using
        map_step (encodedAtom i replacement.encode)
          (Nat.pair (formulaCode p) (formulaCode q)) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [formulaCode, BlockRows.Formula.substitute, Nat.unpair_pair, hp, hq] using
        map_step (encodedAtom i replacement.encode)
          (Nat.pair (formulaCode p) (formulaCode q)) 5 (by decide)
#print axioms literalFormulaCalibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProof
