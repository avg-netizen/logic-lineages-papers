module

public import LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFlipLearningProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionProof
open PredictionGame PredictionLearning PredictionFiniteChange PredictionCodeEvader PredictionFlipMask
open PredictionBaselineGame PredictionUniformHistory PredictionAvailabilityReduction
open PredictionAvailabilityReductionTargets

theorem conditionalOrdinaryAvailabilityReduction : ConditionalOrdinaryAvailabilityReduction := by
  classical
  intro R b hR hb
  obtain ⟨u, hu, hup⟩ := PredictionFlipLearningProof.uniformFlipPolicyProgram R b hR hb
  obtain ⟨v, hv, hve⟩ := PredictionCodeEvaderProof.uniformCodeEvaderProgram
  choose hp hpid using hup
  choose he heid using hve
  refine ⟨u, v, hu, hv, hp, he, hpid, heid, ?_⟩
  intro hav z
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
    apply PredictionFlipLearningProof.positiveFlipLearning R b z
      (fun k => (PredictionFiniteChangeProof.finiteChangesIffWitness R z k).mpr (hw k))
      e htotal heavailable

end LogicLineages.ComputabilityKnowledge.PredictionAvailabilityReductionProof
