module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsFormulaCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
open FiniteSearchPrograms

theorem literalSyntaxCode : FiniteSearchProgramsTargets.LiteralSyntaxCode := by
  intro p
  induction p with
  | equal a b =>
      rw [Code.test, ScopedPhiProgramsProof.test_calibration, FiniteSearchSourceProof.test_eq]
      simp [SourceFormula.encode]
  | less a b =>
      rw [Code.test, ScopedPhiProgramsProof.test_calibration, FiniteSearchSourceProof.test_eq]
      simp [SourceFormula.encode, Nat.add_mod]
  | negative p ih =>
      rw [Code.test, ScopedPhiProgramsProof.test_calibration, FiniteSearchSourceProof.test_eq]
      simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq =>
      rw [Code.test, ScopedPhiProgramsProof.test_calibration, FiniteSearchSourceProof.test_eq]
      simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih =>
      rw [Code.test, ScopedPhiProgramsProof.test_calibration, FiniteSearchSourceProof.test_eq]
      simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, BoundedSourceProgramsProof.literalGuardCode i p, ih]

theorem literalAnswerCode : FiniteSearchProgramsTargets.LiteralAnswerCode := by
  intro values p
  induction p generalizing values with
  | equal a b =>
      rw [Code.answer, ScopedPhiProgramsProof.test_calibration, ScopedPhiProgramsProof.literalDecision,
        FiniteSearchSourceProof.answer_eq]
      simp [SourceFormula.encode]
  | less a b =>
      rw [Code.answer, ScopedPhiProgramsProof.test_calibration, ScopedPhiProgramsProof.literalDecision,
        FiniteSearchSourceProof.answer_eq]
      simp [SourceFormula.encode, Nat.add_mod]
  | negative p ih =>
      rw [Code.answer, ScopedPhiProgramsProof.test_calibration, ScopedPhiProgramsProof.literalDecision,
        FiniteSearchSourceProof.answer_eq]
      simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq =>
      rw [Code.answer, ScopedPhiProgramsProof.test_calibration, ScopedPhiProgramsProof.literalDecision,
        FiniteSearchSourceProof.answer_eq]
      simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih =>
      rw [Code.answer, ScopedPhiProgramsProof.test_calibration, ScopedPhiProgramsProof.literalDecision,
        FiniteSearchSourceProof.answer_eq]
      cases hg : BoundedSource.guard i p with
      | none => simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, BoundedSourceProgramsProof.literalGuardCode i p, hg]
      | some t => simp [SourceFormula.encode, Nat.add_mod, Nat.add_div, BoundedSourceProgramsProof.literalGuardCode i p,
          hg, ScopedPhiProgramsProof.actualZeroDefaultEvaluation values t, ih]

theorem literalDecisionCode : FiniteSearchProgramsTargets.LiteralDecisionCode := by
  intro values p
  unfold Code.decide FiniteSearchSource.decide
  rw [literalSyntaxCode p, literalAnswerCode values p]

theorem actualRawDecision : FiniteSearchProgramsTargets.ActualRawDecision := by
  intro values code
  have hc := literalDecisionCode values (SourceFormulaCodec.decode code)
  rw [SourceFormulaCodecProof.codeRoundtrip code] at hc
  rw [hc]
  exact FiniteSearchSourceProof.actualDecision values (SourceFormulaCodec.decode code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
