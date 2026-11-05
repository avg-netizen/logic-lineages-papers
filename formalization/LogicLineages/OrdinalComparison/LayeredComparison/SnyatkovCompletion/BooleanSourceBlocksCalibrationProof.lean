module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
open BooleanSourceBlocks

theorem literalCodeDecision : BooleanSourceBlocksTargets.LiteralCodeDecision := by
  intro values p
  induction p with
  | equal a b =>
      rw [Code.decide, HomogeneousSourceProof.admissible_calibration]
      simp only [HomogeneousSource.admissible, HomogeneousSource.peelExists, HomogeneousSource.peelForall,
        SourceBooleanGraph.test, Bool.true_or, if_true, HomogeneousSourceProof.decide_calibration,
        decide_eq]
  | less a b =>
      rw [Code.decide, HomogeneousSourceProof.admissible_calibration]
      simp only [HomogeneousSource.admissible, HomogeneousSource.peelExists, HomogeneousSource.peelForall,
        SourceBooleanGraph.test, Bool.true_or, if_true, HomogeneousSourceProof.decide_calibration,
        decide_eq]
  | negative p ih =>
      rw [Code.decide, HomogeneousSourceProof.admissible_calibration, decide_eq]
      by_cases h : HomogeneousSource.admissible (.negative p) = true
      · simp only [if_pos h, HomogeneousSourceProof.decide_calibration]
      · have hm : (5 * p.encode + 2) % 5 = 2 := by omega
        have hd : (5 * p.encode + 2) / 5 = p.encode := by omega
        simp [h, SourceFormula.encode, hm, hd, ih]
  | conjunction p q ihp ihq =>
      rw [Code.decide, HomogeneousSourceProof.admissible_calibration, decide_eq]
      by_cases h : HomogeneousSource.admissible (.conjunction p q) = true
      · simp only [if_pos h, HomogeneousSourceProof.decide_calibration]
      · simp [h, SourceFormula.encode, Nat.add_div, Nat.add_mod, Nat.unpair_pair, ihp, ihq]
  | existsNat i p ih =>
      rw [Code.decide, HomogeneousSourceProof.admissible_calibration, decide_eq]
      by_cases h : HomogeneousSource.admissible (.existsNat i p) = true
      · simp only [if_pos h, HomogeneousSourceProof.decide_calibration]
      · simp [h, SourceFormula.encode, Nat.add_mod]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
