module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEvaluationProof
open Source InternalCanonicalQuotientEdgeApplicationLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The small composition calculation is proved before instantiating the large
canonical fold ASTs. No evaluator reduction enters C or N. -/
theorem argumentCompositionEvaluation (C : Program 4) (N : Program 1)
    (v : List.Vector Nat 4) :
    evaluate (.composition C ![.projection 0,.projection 1,.projection 2,
      .composition N (fun _ : Fin 1 => .projection 3)]) v =
    evaluate C (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,
      evaluate N (List.Vector.ofFn (fun _ : Fin 1 => v.get 3))]) := by
  change evaluate C _ = evaluate C _
  apply congrArg (evaluate C)
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun k => Fin.elim0 k)))) i

theorem actualOriginalCanonicalApplicationCalibration :
    InternalCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalCanonicalApplicationCalibration := by
  intro n arity symbols S Gamma table data hc h v
  have hn := InternalCanonicalResultFoldCalibrationProof.normalizerCalibration
    n arity symbols S Gamma table data hc h
    (List.Vector.ofFn (fun _ : Fin 1 => v.get 3))
  have hj := argumentCompositionEvaluation
    (InternalCanonicalResultFoldCalibration.combine data)
    (InternalCanonicalResultFoldCalibration.normalizer data) v
  change evaluate (actualJ data) v = _ at hj
  rw [hj, InternalCanonicalResultFoldCalibrationSupportProof.combineCalibration
    n arity symbols S Gamma table data hc h, hn]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEvaluationProof
