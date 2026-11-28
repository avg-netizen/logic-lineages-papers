module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformLevelProof

@[expose] public section

/-! # The calibration `Δ_n' = ψ_B(a_n)` at every `n`, on the actual collapse of every solution

`Paper16RemainingOrdinalTargets.AllTowerCalibration`, from root's reduction
`ActualCalibrationLevelsProof.exact_AllFromLevels` and the per-level statements at every level
(`ActualCalibrationUniform.allLevels`). -/

namespace LogicLineages.PersistentMarking.ActualCalibrationAll
open Paper16RemainingOrdinalTargets ActualCalibrationLevels

theorem allTowerCalibration : AllTowerCalibration :=
  ActualCalibrationLevelsProof.exact_AllFromLevels
    (fun A l hl => ActualCalibrationUniform.allLevels A.zero A.successor A.add A.mul A.omega A.one
      A.pow A.fix A.arithmetic A.omegaEquations l hl)

/-- The first instance beyond the explicit levels: `Δ_5' = ψ(a_5)`. -/
theorem calibrationAt_five (A : OrdinalSemantics) : CalibrationAt A 5 :=
  allTowerCalibration A 5

#print axioms allTowerCalibration
#print axioms calibrationAt_five

end LogicLineages.PersistentMarking.ActualCalibrationAll
