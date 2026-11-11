module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumScanProof
open OriginalTransparentMinimum
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof InternalLessThanEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector


theorem stepEvaluation (Q : Program 3) (index previous seed parameter : Nat) :
    evaluate (scanStep Q) (ofFn ![index,previous,seed,parameter]) =
      if previous < index then previous
      else if evaluate Q (ofFn ![seed,index,parameter]) = 1 then index else index+1 := by
  have hl : evaluate (.composition InternalLessThan.ltTest ![.projection 1,.projection 0])
      (ofFn ![index,previous,seed,parameter]) = if previous < index then 1 else 0 := by
    change evaluate InternalLessThan.ltTest (ofFn ![previous,index]) = _
    rw [vectorTwo]
    exact exactLessThanEvaluation _ _
  have he : evaluate (.composition InternalEqualityTest.equalityTest
      ![.composition Q ![.projection 2,.projection 0,.projection 3],
        InternalLessThan.constantOne 4]) (ofFn ![index,previous,seed,parameter]) =
      if evaluate Q (ofFn ![seed,index,parameter]) = 1 then 1 else 0 := by
    change evaluate InternalEqualityTest.equalityTest
      (ofFn ![evaluate Q (ofFn ![seed,index,parameter]),1]) = _
    rw [vectorTwo]
    exact exactEqualityEvaluation _ _
  rw [scanStep,evalBranch,hl]
  by_cases hp : previous < index
  · simp [hp,evaluate]
  · simp only [hp,ite_false,ite_true]
    rw [evalBranch,he]
    by_cases hq : evaluate Q (ofFn ![seed,index,parameter]) = 1 <;>
      simp [hq,evaluate]


theorem scanEvaluation (Q : Program 3) (bound seed parameter : Nat) :
    evaluate (scan Q) (ofFn ![bound,seed,parameter]) =
      (List.range bound).findIdx
        (fun candidate => decide (evaluate Q (ofFn ![seed,candidate,parameter]) = 1)) := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
    change evaluate (scanStep Q) (ofFn ![bound,
      evaluate (scan Q) (ofFn ![bound,seed,parameter]),seed,parameter]) = _
    rw [stepEvaluation,ih,List.range_succ,List.findIdx_append,List.length_range]
    split_ifs with h hq <;> simp_all only [List.findIdx_cons,decide_true,decide_false,
      cond_true,cond_false,List.findIdx_nil,Nat.zero_add,Nat.zero_add] <;> omega

theorem actualOriginalTransparentMinimumScanEvaluation :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumScanEvaluation := by
  intro Q v
  have hv : v = ofFn ![v.get 0,v.get 1,v.get 2] := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i <;> rfl
  conv_lhs => rw [hv]
  exact scanEvaluation Q _ _ _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumScanProof
