module
public import LogicLineages.PermittedControl.SelectedDecisionPullbackTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedDecisionPullback.Proof
open OrdinalComparison Source
open Source.FunctionalHardnessCompletion
open Source.FunctionalHardnessCompletion.HardnessDecision
open Source.FunctionalHardnessCompletion.HardnessDecision.Proof (conjunctionMeaning conjunctionComputable)

theorem finiteQueryPullback : SelectedDecisionPullbackTargets.FiniteQueryPullback := by
  intro ctrl policy strict hreduce hdecider
  obtain ⟨reduce,hcompute,hreduce⟩ := hreduce
  obtain ⟨answer,hanswer,hcorrect⟩ := hdecider
  have hbool : Computable (fun e => allAnswers answer (reduce e)) :=
    (conjunctionComputable answer hanswer).comp hcompute
  have hmeaning : ∀ e,
      ¬encodedPolynomialSolvable e ↔ allAnswers answer (reduce e)=true := by
    intro e
    obtain ⟨queries,hcodes,hbounds,hsem⟩ := hreduce e
    have hanswerCorrect : ∀ q∈queries,
        answer (queryCode q)=true ↔ SelectedFiniteQuery.queryUniversal ctrl policy strict q := by
      intro q hq
      rcases q with ⟨Γ,a,b⟩
      have hb := hbounds ⟨Γ,a,b⟩ hq
      exact hcorrect Γ a b hb.1 hb.2.1 hb.2.2
    rw [←hcodes,conjunctionMeaning answer (queries.map queryCode)]
    simp only [List.forall_mem_map]
    constructor
    · intro hs q hq
      exact (hanswerCorrect q hq).mpr (hsem.mp hs q hq)
    · intro hs
      apply hsem.mpr
      intro q hq
      exact (hanswerCorrect q hq).mp (hs q hq)
  have hcomplement : ComputablePred (fun e => ¬encodedPolynomialSolvable e) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨(fun e => allAnswers answer (reduce e)),hbool,?_⟩
    exact funext (fun e => propext (hmeaning e))
  exact hcomplement.not.of_eq (fun e => by simp)

end LogicLineages.PermittedControl.SelectedDecisionPullback.Proof
