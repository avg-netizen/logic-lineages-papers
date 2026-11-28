module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeHierarchyProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeReductionTargets

@[expose] public section

/-! The two facts about `L = (β ↦ D β 0)` consumed by the reduction T4 ⟹ T5
(`ActualCalibrationThreeReduction.LevelFacts`): `L` is strictly increasing, and `Γ_0 < L e` for
`e ≥ 1`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal ActualOmegaTower OrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets NativeTowerSequenceTargets

theorem exact_LevelFacts : ActualCalibrationThreeReduction.LevelFacts := by
  intro Z s add mul w one pow fix h1 h2
  exact ⟨fun α β h => levelZero_strict h1 h2 α β h, fun e he => base_lt_level h1 h2 e he⟩

#print axioms exact_LevelFacts

end LogicLineages.PersistentMarking.ActualCalibrationThree
