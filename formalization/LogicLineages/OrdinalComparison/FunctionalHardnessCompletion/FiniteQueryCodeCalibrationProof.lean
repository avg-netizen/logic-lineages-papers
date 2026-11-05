module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Proof

theorem exactQueryCalibration : Targets.ExactQueryCalibration := by
  intro strict n s
  have h := PlainSystemCode.Proof.exactQueryPairs n s
  simp only [groundQuery, FunctionalHardnessCompletion.queryCode]
  cases strict with
  | false =>
      simp only [sourcePair, queryCode, Bool.false_eq_true, ↓reduceIte]
      rw [h.2.1, h.2.2]
      rfl
  | true =>
      simp only [sourcePair, queryCode, ↓reduceIte]
      rw [h.1, h.2.2]
      rfl

theorem exactListCalibration : Targets.ExactListCalibration := by
  intro strict n s
  rw [queriesCode, (MaskRestrictionCode.Proof.exactMasks n).1]
  simp only [queries, List.map_map]
  apply List.map_congr_left
  intro z hz
  change FunctionalHardnessCompletion.queryCode (groundQuery strict (restrictSystem z s)) =
    queryCode strict n (MaskRestrictionCode.restrictRows (MaskRestrictionCode.maskCode z)
      (s.map SeededSourceCode.expressionCode))
  rw [MaskRestrictionCode.Proof.exactSystemRestriction]
  exact exactQueryCalibration strict n (restrictSystem z s)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Proof
