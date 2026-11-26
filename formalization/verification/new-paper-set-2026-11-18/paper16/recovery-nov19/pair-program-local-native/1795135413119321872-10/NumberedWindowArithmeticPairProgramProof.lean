import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramProof
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowArithmeticPair
open NumberedWindowArithmeticPairProgramTargets

theorem calibration : PairAndDecodeCalibration := ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem actualPair : ActualPairProgram := by
  let f := fun v : List.Vector Nat 2 => pair v.head v.tail.head
  have primitive : Primrec f :=
    GorbowRegistryTupleProof.uniformPrograms.1.comp (Primrec.vector_head.pair (Primrec.vector_head.comp Primrec.vector_tail))
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 f primitive
  exact ⟨p,fun a b => hp (a ::ᵥ b ::ᵥ List.Vector.nil)⟩

theorem actualDecoder : ActualPairDecoderProgram := by
  have primitive : Primrec (fun n => Encodable.encode (decode n)) :=
    Primrec.encode.comp GorbowRegistryDecoderProof.uniformPrograms.2.1
  exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp primitive

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramProof
