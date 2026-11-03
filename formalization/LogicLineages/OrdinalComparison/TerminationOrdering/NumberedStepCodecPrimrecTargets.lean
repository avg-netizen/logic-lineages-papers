module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecTargets
open NumberedNumericStep NumberedStepCodecPrimrec

def ActualPositionEncoderPrimitive : Prop := Primrec positionNumber

def ActualPositionDecoderPrimitive : Prop := Primrec decodePosition

def ActualPathEncoderPrimitive : Prop := Primrec pathNumber

def ActualPathDecoderPrimitive : Prop := Primrec decodePath

def ActualStepEncoderPrimitive : Prop := Primrec stepCertificateNumber

def ActualStepDecoderPrimitive : Prop := Primrec decodeStepCertificate

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecTargets
