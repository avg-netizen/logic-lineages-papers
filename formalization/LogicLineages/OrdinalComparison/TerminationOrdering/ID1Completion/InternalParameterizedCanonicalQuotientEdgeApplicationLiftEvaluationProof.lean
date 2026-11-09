module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof
open Source InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalParameterizedCanonicalResultFold (actualJ combine foldN)
open InternalOriginalUniformParameterLeaves (parameterCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Compute only the small literal composition. The canonical fold and
combine programs remain opaque, and both calls retain the identical p. -/
theorem argumentCompositionEvaluation (C : Program 5) (N : Program 2)
    (v : List.Vector Nat 5) :
    evaluate (.composition C
      ![.projection 0,.projection 1,.projection 2,
        .composition N ![.projection 3,.projection 4],.projection 4]) v =
      evaluate C (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,
        evaluate N (List.Vector.ofFn ![v.get 3,v.get 4]),v.get 4]) := by
  change evaluate C _ = evaluate C _
  apply congrArg (evaluate C)
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i

/-- All natural inputs retain the original packed-target map. No validity,
decoded type, canonical function or fixed-argument hypothesis is introduced. -/
theorem actualOriginalParameterizedCanonicalApplicationCalibration :
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalParameterizedCanonicalApplicationCalibration := by
  intro n arity data hc symbols S Gamma table hS v
  have hn :=
    (InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
      n arity data hc symbols S Gamma table hS (v.get 3)).1
  have hj := argumentCompositionEvaluation (combine data) (foldN data)
    (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,parameterCode symbols S Gamma table])
  change evaluate (actualJ data)
    (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,parameterCode symbols S Gamma table]) = _ at hj
  rw [hj]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  rw [InternalOriginalUniformCanonicalResultFoldSupportProof.combineCalibration
    n arity data hc symbols S Gamma table hS,hn]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof
