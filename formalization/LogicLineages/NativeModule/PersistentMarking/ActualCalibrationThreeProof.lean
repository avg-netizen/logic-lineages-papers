module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePowerProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeLevelFactsProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeReductionProof

@[expose] public section

/-! T5 (`CalibrationThree`): `Δ_3' = ψ(a_3)`, from T4 (`psiPowerLevel`), the two facts about `L`
(`exact_LevelFacts`) and the reduction `ActualCalibrationThreeReductionProof.exact_ThreeFromPower`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree

theorem calibrationThree : CalibrationThree :=
  ActualCalibrationThreeReductionProof.exact_ThreeFromPower exact_LevelFacts psiPowerLevel

#print axioms calibrationThree

end LogicLineages.PersistentMarking.ActualCalibrationThree
