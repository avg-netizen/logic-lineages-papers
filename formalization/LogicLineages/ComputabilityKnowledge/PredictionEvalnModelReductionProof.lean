module

public import LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetProof
public import LogicLineages.ComputabilityKnowledge.PredictionFlipLearningProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionProof
open PredictionGame PredictionLearning PredictionFiniteChange PredictionUniformHistory
open PredictionAvailabilityReduction PredictionEvalnModelReductionTargets

theorem actualEvalnModelReduction : ActualEvalnModelReduction := by
  classical
  intro R hR
  obtain ⟨v, _, hv⟩ := PredictionCodeEvaderProof.uniformCodeEvaderProgram
  choose he heid using hv
  obtain ⟨b, hb, hav⟩ := PredictionCommonBudgetProof.actualCommonAvailableBudget v he
  obtain ⟨u, hu, hup⟩ := PredictionFlipLearningProof.uniformFlipPolicyProgram R b hR hb
  choose hp hpid using hup
  refine ⟨b, u, hb, hu, hp, fun z => ?_⟩
  rw [hpid z]
  constructor
  · intro hlearn k
    by_contra hn
    have hinf : (changeSet R z k).Infinite := by
      intro hfin
      exact hn ((PredictionFiniteChangeProof.finiteChangesIffWitness R z k).mp hfin)
    exact PredictionFlipLearningProof.negativeFlipLearning R b z k hinf
      (compileSelfHistory v k) (he k) (heid k) (hav k)
      (hlearn (compileSelfHistory v k) (he k) (hav k))
  · intro hw e htotal heavailable
    exact PredictionFlipLearningProof.positiveFlipLearning R b z
      (fun k => (PredictionFiniteChangeProof.finiteChangesIffWitness R z k).mpr (hw k))
      e htotal heavailable

end LogicLineages.ComputabilityKnowledge.PredictionEvalnModelReductionProof
