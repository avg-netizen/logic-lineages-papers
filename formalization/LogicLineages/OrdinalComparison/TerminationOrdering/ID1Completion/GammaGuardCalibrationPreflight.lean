module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationPreflight

def gammaPrimitiveComparator : Prop := GammaGuardCalibrationTargets.ActualGammaPrimitive
def gammaProgramComparator : Prop := GammaGuardCalibrationTargets.ActualGammaProgram
def validityEvaluationComparator : Prop := GammaGuardCalibrationTargets.ActualValidityEvaluation
def validityCalibrationComparator : Prop := GammaGuardCalibrationTargets.ActualValidityCalibration
def guardRangeComparator : Prop := GammaGuardCalibrationTargets.ActualGuardRange
def guardCalibrationComparator : Prop := GammaGuardCalibrationTargets.ActualGuardCalibration
def typedValidComparator : Prop := GammaGuardCalibrationTargets.ActualTypedValid
def positiveGammaComparator : Prop := GammaGuardCalibrationTargets.ActualPositiveGamma
def objectValidityComparator : Prop := GammaGuardCalibrationTargets.ActualObjectValidity
def gammaDecodedComparator : Prop := GammaGuardCalibrationTargets.ActualGammaDecoded

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationPreflight
