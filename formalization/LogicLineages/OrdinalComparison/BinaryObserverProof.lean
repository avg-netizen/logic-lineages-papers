module
public import LogicLineages.OrdinalComparison.BinaryObserverTargets
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesProof
public import LogicLineages.OrdinalComparison.BinaryMatrixProof

@[expose] public section

universe u

namespace LogicLineages.OrdinalComparison

theorem actualBinaryInitialVectorCalibration : Targets.ActualBinaryInitialVectorCalibration := by
  intro D
  funext i
  simp [actualBinaryCoefficientVector, actualBinaryInitialVector, Polynomial.coeff_one]

theorem actualBinaryMatrixWordProduct : Targets.ActualBinaryMatrixWordProduct.{u} := by
  intro K _ D A w v
  induction w generalizing v with
  | nil => simp [actualBinaryMatrixWord]
  | cons b w ih =>
    simp only [actualBinaryMatrixWord, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih, Matrix.mulVec_mulVec]

theorem actualSourceBinarySelectedCoefficient : Targets.ActualSourceBinarySelectedCoefficient := by
  intro d hd n w hw
  have hproper : (1 : Polynomial (ZMod 2)).degree < (actualBinarySourceDimension d : WithBot Nat) := by
    rw [Polynomial.degree_one]
    exact WithBot.coe_lt_coe.mpr (actualBinarySourceDimensionPositive d hd)
  rw [← actualBinaryMatrixWordProduct (ZMod 2), ← actualBinaryInitialVectorCalibration]
  rw [actualBinaryMatrixWordObservation _ (actualBinarySourceDimensionPositive d hd)
    (actualBinarySourceDenominator d) 1 (actualBinarySourceDenominatorConstant d)
    (le_of_eq (actualBinarySourceDenominatorDegree d)) hproper w]
  rw [← actualBinaryPartitionSeriesQuotient d, hw]
  simp only [actualBinaryPartitionSeries, PowerSeries.coeff_mk]

theorem actualSourceBinarySelectedParity : Targets.ActualSourceBinarySelectedParity := by
  intro d hd n w hw
  rw [actualSourceBinarySelectedCoefficient d hd n w hw]
  exact ZMod.val_natCast 2 _

end LogicLineages.OrdinalComparison
