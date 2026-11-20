import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramCalibration
import LogicLineages.PersistentMarking.NumberedWindowRegistryPairPrograms

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramProof
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowArithmeticPair
open NumberedWindowArithmeticPairProgramTargets

theorem calibration : PairAndDecodeCalibration := NumberedWindowArithmeticPairProgramCalibration.calibration

theorem actualPair : ActualPairProgram := by
  obtain ⟨p,hp⟩ := NumberedWindowRegistryPairPrograms.encoding
  exact ⟨p, fun a b => (hp a b).trans (calibration.1 a b).symm⟩

theorem actualDecoder : ActualPairDecoderProgram := by
  obtain ⟨p,hp⟩ := NumberedWindowRegistryPairPrograms.decoding
  exact ⟨p, fun n => (hp n).trans (congrArg Encodable.encode (calibration.2 n).symm)⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramProof
