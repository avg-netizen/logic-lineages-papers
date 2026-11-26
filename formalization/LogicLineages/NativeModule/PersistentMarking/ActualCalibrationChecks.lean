module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTwoProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ActualCalibration

theorem exact_MonotoneLayer : MonotoneLayer := monotoneLayer
theorem exact_OrbitComparison : OrbitComparison := orbitComparison
theorem exact_CalibrationTwo : CalibrationTwo := calibrationTwo

#print axioms exact_MonotoneLayer
#print axioms exact_OrbitComparison
#print axioms exact_CalibrationTwo

end LogicLineages.PersistentMarking.ActualCalibration
