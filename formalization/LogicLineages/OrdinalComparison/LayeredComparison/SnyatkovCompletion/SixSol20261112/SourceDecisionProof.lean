module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceCompilerCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.GroundEvaluatorCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.GroundEvaluatorProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
open SourceDecision NonlinearProjectionCompletion

theorem effectiveOriginalSourceElimination : SourceDecisionTargets.EffectiveOriginalSourceElimination :=
  ⟨eliminate, eliminate_computable, literalSourceCompiler,
    OriginalSourceEliminationProof.actualSourceElimination,
    OriginalSourceEliminationProof.originalSourceNameSupport⟩

theorem fullSourceDecision : SourceDecisionTargets.FullSourceDecision := by
  refine ⟨answer, answer_computable, ?_⟩
  intro p hp ν
  have hclosed : ∀ i ∈ (OriginalSourceElimination.eliminate p).variables, False := by
    intro i hi
    have h := OriginalSourceEliminationProof.originalSourceNameSupport p i hi
    simpa only [hp, List.not_mem_nil] using h
  have hvaluation := ExpandedBooleanGraphProof.matrix_eval_congr
    (OriginalSourceElimination.eliminate p) (fun _ => 0) ν
    (fun i hi => False.elim (hclosed i hi))
  change groundMatrix (eliminate p.encode) = true ↔ p.eval ν
  rw [literalSourceCompiler]
  exact (groundMatrixCalibration _).trans
    (hvaluation.trans (OriginalSourceEliminationProof.actualSourceElimination p ν))

#print axioms effectiveOriginalSourceElimination
#print axioms fullSourceDecision
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
