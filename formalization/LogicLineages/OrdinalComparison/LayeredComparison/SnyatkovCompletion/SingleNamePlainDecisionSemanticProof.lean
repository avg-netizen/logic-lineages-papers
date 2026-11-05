module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionProof
open NormalForm SingleNamePlainDecision

theorem valuationIndependence : SingleNamePlainDecisionTargets.ValuationIndependence := by
  intro i p hp ν μ
  have hnames := ((SingleNamePlainProof.exactFragmentTest i p).mp hp).2
  have he : ∀ n : Nat, p.eval (Function.update ν i n) ↔ p.eval (Function.update μ i n) := by
    intro n
    apply SourceTermGraphSupportProof.formula_eval_congr
    intro j hj
    rw [hnames j hj, Function.update_self, Function.update_self]
  exact ⟨exists_congr he, forall_congr' he⟩

theorem exactDecisionDomain : SingleNamePlainDecisionTargets.ExactDecisionDomain := by
  intro i p
  cases h : SingleNamePlain.admissible i p <;> simp [existsDecision, forallDecision, h]

theorem actualExistentialDecision : SingleNamePlainDecisionTargets.ActualExistentialDecision := by
  intro i p hp ν answer
  have he : ZeroValuation.evaluate (SingleNamePlain.existsEliminate i p) = true ↔
      ∃ n : Nat, p.eval (Function.update ν i n) :=
    (ZeroValuationProof.actualZeroEvaluator _).trans
      ((SingleNamePlainProof.actualExistentialElimination i p hp (fun _ => 0)).trans
        (valuationIndependence i p hp (fun _ => 0) ν).1)
  simp only [existsDecision, hp, if_true, Option.some.injEq]
  rw [Bool.eq_iff_iff, he]

theorem actualUniversalDecision : SingleNamePlainDecisionTargets.ActualUniversalDecision := by
  intro i p hp ν answer
  have he : ZeroValuation.evaluate (SingleNamePlain.forallEliminate i p) = true ↔
      ∀ n : Nat, p.eval (Function.update ν i n) :=
    (ZeroValuationProof.actualZeroEvaluator _).trans
      ((SingleNamePlainProof.actualUniversalElimination i p hp (fun _ => 0)).trans
        (valuationIndependence i p hp (fun _ => 0) ν).2)
  simp only [forallDecision, hp, if_true, Option.some.injEq]
  rw [Bool.eq_iff_iff, he]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SingleNamePlainDecisionProof
