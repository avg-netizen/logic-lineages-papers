module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsLimitTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeLevelProof

public section

namespace LogicLineages.PersistentMarking.ActualCalibrationLevelsLimitProof
open Ordinal OrdinalRealizationTargets OrdinalNativeOrbitProof OrdinalNativeIterationTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCalibrationLevels

/-- A pointwise supremum at type `A_{m+1}` is a supremum after applying down the spine. -/
theorem semDown_sup {ι : Type 1} : ∀ (m : Nat) (F : ι → Value (tier (m + 1))) (v : Value (tier (m + 1)))
    (xs : Env), PointwiseSupremum (tier (m + 1)) F v →
      (semDown m v xs).val = ⨆ i, (semDown m (F i) xs).val := by
  intro m
  induction m with
  | zero =>
    intro F v xs h
    have h' : ∀ x : Value (tier 0), PointwiseSupremum (tier 0) (fun i => F i x) (v x) := h
    exact h' zeroValue
  | succ m ih =>
    intro F v xs h
    have h' : ∀ x : Value (tier (m + 1)), PointwiseSupremum (tier (m + 1)) (fun i => F i x) (v x) := h
    exact ih (fun i => F i (xs (m + 1))) (v (xs (m + 1))) xs (h' (xs (m + 1)))

theorem exact_LevelDiagonalLimit : LevelDiagonalLimit := by
  intro fix pow l lim hl
  cases l with
  | zero =>
    exact (orbitEquations (tier 0) (towerEnv fix pow 1) zeroValue).2.2 lim hl
  | succ m =>
    exact semDown_sup m _ _ (towerEnv fix pow)
      ((orbitEquations (tier (m + 1)) (towerEnv fix pow (m + 2)) (towerEnv fix pow (m + 1))).2.2 lim hl)

#print axioms exact_LevelDiagonalLimit

end LogicLineages.PersistentMarking.ActualCalibrationLevelsLimitProof
