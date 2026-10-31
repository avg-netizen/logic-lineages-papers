module
public import LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderProof
open PredictionMeasureOrder PredictionMeasureOrderTargets PredictionTapeMeasureContract PredictionTapeRuntimeClass

theorem positiveThresholdOrder : PositiveThresholdOrder := by
  classical
  intro levels hmono p m hm
  by_cases hex : ∃ j, 1 ≤ j ∧ ¬ Threshold p (levels j)
  · have hpos := (Nat.find_spec hex).1
    have hfail := (Nat.find_spec hex).2
    have hh : height levels p = ((Nat.find hex - 1 : Nat) : WithTop Nat) := by
      simp only [height, dif_pos hex]
    rw [hh]
    constructor
    · intro hge
      have hnat : m ≤ Nat.find hex - 1 := WithTop.coe_le_coe.mp hge
      by_contra hn
      have hle := Nat.find_min' hex ⟨hm,hn⟩
      omega
    · intro hthreshold
      have hnat : m ≤ Nat.find hex - 1 := by
        by_contra hn
        have hle : Nat.find hex ≤ m := by omega
        exact hfail (PredictionTapeMeasureContractProof.thresholdAntitone p _ _
          (fun n => hmono n hle) hthreshold)
      exact WithTop.coe_le_coe.mpr hnat
  · simp only [height, dif_neg hex, le_top, true_iff]
    by_contra hn
    exact hex ⟨m,hm,hn⟩

end LogicLineages.ComputabilityKnowledge.PredictionMeasureOrderProof
