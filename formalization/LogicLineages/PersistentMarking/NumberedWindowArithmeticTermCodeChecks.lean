import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeSound
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeComplete

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeTargets
open NumberedWindowArithmeticCodecLaws

theorem exact_FieldsFuelCalibration : FieldsFuelCalibration :=
  NumberedWindowArithmeticFieldsProof.calibration

theorem exact_FieldsCodec : ExactFieldsCodec :=
  NumberedWindowArithmeticFieldsProof.exactCodec

theorem exact_LiteralFieldBounds : LiteralFieldBounds :=
  NumberedWindowArithmeticNodeProof.bounds

theorem exact_TaggedNodeCodec : ExactTaggedNodeCodec :=
  NumberedWindowArithmeticNodeProof.exactCodec

theorem exact_TermFuelCalibration : TermFuelCalibration :=
  ⟨fun f => (NumberedWindowArithmeticTermCodeSound.atFuel f).1,
    fun f => (NumberedWindowArithmeticTermCodeComplete.atFuel f).1⟩

theorem exact_ArgsFuelCalibration : ArgsFuelCalibration :=
  ⟨fun f => (NumberedWindowArithmeticTermCodeSound.atFuel f).2,
    fun f => (NumberedWindowArithmeticTermCodeComplete.atFuel f).2⟩

theorem exact_TermCodec : ExactTermCodec :=
  codec encodeTerm decodeTerm (fun c => (NumberedWindowArithmeticTermCodeSound.atFuel c).1 c)
    NumberedWindowArithmeticTermCodeComplete.termRound

theorem exact_ArgsCodec : ExactArgsCodec :=
  codec encodeArgs decodeArgs (fun c => (NumberedWindowArithmeticTermCodeSound.atFuel c).2 c)
    NumberedWindowArithmeticTermCodeComplete.argsRound

#print axioms exact_FieldsFuelCalibration
#print axioms exact_FieldsCodec
#print axioms exact_LiteralFieldBounds
#print axioms exact_TaggedNodeCodec
#print axioms exact_TermFuelCalibration
#print axioms exact_ArgsFuelCalibration
#print axioms exact_TermCodec
#print axioms exact_ArgsCodec

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
