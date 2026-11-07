module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationPreflight
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationStatementChecks

theorem gammaPrimitive_exact : GammaGuardCalibrationPreflight.gammaPrimitiveComparator :=
  GammaGuardCalibrationProof.actualGammaPrimitive

#print axioms gammaPrimitive_exact

theorem gammaProgram_exact : GammaGuardCalibrationPreflight.gammaProgramComparator :=
  GammaGuardCalibrationProof.actualGammaProgram

#print axioms gammaProgram_exact

theorem validityEvaluation_exact : GammaGuardCalibrationPreflight.validityEvaluationComparator :=
  GammaGuardCalibrationProof.actualValidityEvaluation

#print axioms validityEvaluation_exact

theorem validityCalibration_exact : GammaGuardCalibrationPreflight.validityCalibrationComparator :=
  GammaGuardCalibrationProof.actualValidityCalibration

#print axioms validityCalibration_exact

theorem guardRange_exact : GammaGuardCalibrationPreflight.guardRangeComparator :=
  GammaGuardCalibrationProof.actualGuardRange

#print axioms guardRange_exact

theorem guardCalibration_exact : GammaGuardCalibrationPreflight.guardCalibrationComparator :=
  GammaGuardCalibrationProof.actualGuardCalibration

#print axioms guardCalibration_exact

theorem typedValid_exact : GammaGuardCalibrationPreflight.typedValidComparator :=
  GammaGuardCalibrationProof.actualTypedValid

#print axioms typedValid_exact

theorem positiveGamma_exact : GammaGuardCalibrationPreflight.positiveGammaComparator :=
  GammaGuardCalibrationProof.actualPositiveGamma

#print axioms positiveGamma_exact

theorem objectValidity_exact : GammaGuardCalibrationPreflight.objectValidityComparator :=
  GammaGuardCalibrationProof.actualObjectValidity

#print axioms objectValidity_exact

theorem gammaDecoded_exact : GammaGuardCalibrationPreflight.gammaDecodedComparator :=
  GammaGuardCalibrationProof.actualGammaDecoded

#print axioms gammaDecoded_exact

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationStatementChecks
