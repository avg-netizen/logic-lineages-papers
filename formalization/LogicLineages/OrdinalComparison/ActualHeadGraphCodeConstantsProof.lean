module
public import LogicLineages.OrdinalComparison.ActualHeadGraphCodeTargets
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitProof
public import LogicLineages.OrdinalComparison.HeadGraphShiftProof
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
open ForwardTranslation FormulaConstruction

theorem exactGenuineConstants : Targets.ExactGenuineConstants := by
  intro a c δ
  have hc := GeneralOmegaHeadLimit.Proof.actualClosedHeadCalibration a
  have hs := HeadGraphShift.actual_shift (fixedHead a) hc.2.2.2.2 hc.2.2.2.1 δ
  have hn : headNormCode (closedPositiveCode a) = actualOrdinalNorm (fixedHead a) := by
    unfold headNormCode
    rw [hc.2.1, rawNormCodeCorrect]
    rw [← actualOrdinalNorm_notationCorrespondence (scalarHeadNote a), hc.1]
  have hsn : shiftedNormCode (closedPositiveCode a) δ = actualOrdinalNorm (shiftedHead a δ) := by
    rw [shiftedNormCode, hn]
    exact hs.2.2.1.symm
  have hr : rayBaseCode (closedPositiveCode a) c = ActualUnaryRay.totalNorm a c 0 := by
    simp [rayBaseCode, hn, ActualUnaryRay.totalNorm]
  refine ⟨hn, hsn, hr, ?_, ?_⟩
  · simp only [thresholdCode, threshold, hsn, hr]
  · intro t ht
    have hv := (hs.2.2.2 t ht).2.2.2
    unfold prefixValueCode
    rw [hc.2.1, (encodedFiniteTailCorrect (scalarHeadNote a) _).1,
      encodedCollapseSourceCorrect, (finiteTailCorrect (scalarHeadNote a) _).1, hc.1, hn]
    exact hv.symm
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.GraphCode.Proof
