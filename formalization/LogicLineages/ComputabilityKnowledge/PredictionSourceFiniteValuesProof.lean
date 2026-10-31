module
public import LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeAntiProgramProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeComputableProof
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesProof
open PredictionSourceFiniteValues PredictionSourceFiniteValuesTargets PredictionTapeObservation
open PredictionTapeRuntimeClass PredictionOriginalHardness PredictionOriginalBounds

theorem wholeSourceFiniteValues : WholeSourceFiniteValues := by
  classical
  intro g hg p hp
  obtain ⟨forward,reverse,anti,_,_,hanti⟩ := PredictionTapeAntiProgramProof.uniformRawAntiProgram
  obtain ⟨he,_,_,hne⟩ := hanti p hp
  let e := PredictionTapeAntiProgram.compile forward reverse anti p
  obtain ⟨time,htime,hs⟩ := PredictionTapeRuntimeComputableProof.totalProgramComputableRuntime e he
  obtain ⟨i,hi⟩ := hg (fun n => time n+1) (Computable.succ.comp htime)
  have hdom : ∀ n, time n+1 ≤ levelBound g (i+1) n := by
    intro n
    rw [literalFiniteMaximum, ← hi n]
    exact le_trans
      (Finset.le_sup (s := Finset.range (n+1)) (f := g i) (by simp))
      (Finset.le_sup (s := Finset.range (i+1))
        (f := fun j => (Finset.range (n+1)).sup (g j)) (by simp))
  have htimebound : EventualRuntime e (levelBound g (i+1)) :=
    ⟨0,fun n _ => ⟨time n,hs n,lt_of_lt_of_le (Nat.lt_succ_self _) (hdom n)⟩⟩
  have hnot : ¬ Threshold (policy p hp) (levelBound g (i+1)) := by
    intro h
    exact hne (h e he htimebound)
  have hex : ∃ m, 1 ≤ m ∧ ¬ Threshold (policy p hp) (levelBound g m) :=
    ⟨i+1,by omega,hnot⟩
  refine ⟨Nat.find hex-1,?_⟩
  simp only [originalHeight, PredictionTapeMeasureContract.height, dif_pos hex]

end LogicLineages.ComputabilityKnowledge.PredictionSourceFiniteValuesProof
