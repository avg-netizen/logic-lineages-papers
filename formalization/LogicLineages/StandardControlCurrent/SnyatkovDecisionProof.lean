module
public import LogicLineages.StandardControlCurrent.SnyatkovDecisionTargets
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.SnyatkovDecisionProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open SixSol20261112

theorem controlArithmetic : SnyatkovDecisionTargets.ControlArithmetic :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, Phi_computable,
    (LayeredComparison.SnyatkovInverse.Proof.actualPrimitiveRecursion.1).to_comp⟩

theorem currentBinderCompatibility : SnyatkovDecisionTargets.CurrentBinderCompatibility := by
  intro i p
  rw [HFreeGraphNormalizationProof.names_calibration,
    HFreeGraphNormalizationProof.graphFormula_calibration,
    WholeBoundProjectionCodeProof.literalInitializedProjection]
  exact SourceDecisionStatementChecks.literalBinderCompiler i p

theorem effectiveOriginalElimination : SnyatkovDecisionTargets.EffectiveOriginalElimination := by
  refine ⟨SourceDecisionStatementChecks.actualCompilerPrograms.2.2, ?_⟩
  intro p
  exact ⟨SourceDecisionStatementChecks.literalSourceCompiler p,
    OriginalSourceEliminationStatementChecks.actualSourceHFree p,
    OriginalSourceEliminationStatementChecks.actualSourceNames p,
    OriginalSourceEliminationStatementChecks.actualSource p⟩

theorem zeroEvaluator : SnyatkovDecisionTargets.ZeroEvaluator :=
  ⟨SourceDecisionStatementChecks.actualEvaluationPrograms.1,
    SourceDecisionStatementChecks.actualEvaluationPrograms.2.1,
    SourceDecisionStatementChecks.groundTermCalibration,
    SourceDecisionStatementChecks.groundMatrixCalibration⟩

theorem actualClosedAnswer : SnyatkovDecisionTargets.ActualClosedAnswer := by
  refine ⟨zeroEvaluator.2.1.comp effectiveOriginalElimination.1, ?_⟩
  intro p hp ν
  obtain ⟨hcode, _, hnames, hsemantic⟩ := effectiveOriginalElimination.2 p
  have hclosed : ∀ i ∈ (OriginalSourceElimination.eliminate p).variables, False := by
    intro i hi
    simpa only [hp, List.not_mem_nil] using hnames i hi
  have hvaluation := ExpandedBooleanGraphProof.matrix_eval_congr
    (OriginalSourceElimination.eliminate p) (fun _ => 0) ν
    (fun i hi => False.elim (hclosed i hi))
  change SourceDecision.groundMatrix (SourceDecision.eliminate p.encode) = true ↔ p.eval ν
  rw [hcode]
  exact (zeroEvaluator.2.2.2 _).trans (hvaluation.trans (hsemantic ν))

theorem fullSourceDecision : SnyatkovDecisionTargets.FullSourceDecision :=
  ⟨SourceDecision.answer, actualClosedAnswer⟩

end LogicLineages.StandardControlCurrent.SnyatkovDecisionProof
