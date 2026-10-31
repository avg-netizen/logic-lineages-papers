module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeClassProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeFlipProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessProof
open PredictionGame PredictionTapeObservation PredictionTapeRuntime PredictionTapeRuntimeClass
open PredictionFiniteChange PredictionTapeFlip PredictionTapeHardness PredictionTapeHardnessTargets

theorem fixedBudgetHardness : FixedBudgetHardness := by
  classical
  intro R b hR hb hdom
  obtain ⟨f, hf, hprog⟩ := PredictionTapeFlipProof.uniformTapeFlipProgram R b hR hb
  choose hp hpid using hprog
  refine ⟨f, hf, hp, ?_⟩
  intro z
  rw [hpid z]
  constructor
  · intro hlearn k
    by_contra hn
    have hinf : (changeSet R z k).Infinite := by
      intro hfin
      exact hn ((PredictionFiniteChangeProof.finiteChangesIffWitness R z k).1 hfin)
    obtain ⟨he, heq⟩ := PredictionTapeRuntimeClassProof.exactEvaderPolicy k
    have htime := (PredictionTapeRuntimeClassProof.exactEvaderMembership k b).2 (hdom k)
    have hav := (PredictionTapeRuntimeClassProof.exactAvailabilityCalibration (evaderCode k) he b).2 htime
    exact PredictionTapeFlipProof.negativeTapeFlipLearning R b z k hinf
      (evaderCode k) he heq hav (hlearn (evaderCode k) he htime)
  · intro hw e he htime
    exact PredictionTapeFlipProof.positiveTapeFlipLearning R b z
      (fun k => (PredictionFiniteChangeProof.finiteChangesIffWitness R z k).2 (hw k)) e he
      ((PredictionTapeRuntimeClassProof.exactAvailabilityCalibration e he b).2 htime)

end LogicLineages.ComputabilityKnowledge.PredictionTapeHardnessProof
