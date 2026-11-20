module

public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
public import LogicLineages.PersistentMarking.NumberedWindowRegistryPairCalibration
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRegistryPairPrograms
open LogicLineages.ComputabilityKnowledge List.Vector

theorem encoding : ∃ p : GorbowPRProgram.Program 2,
    ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = GorbowRegistryTuple.pair a b := by
  let f : List.Vector Nat 2 → Nat := fun v => GorbowRegistryTuple.pair v.head v.tail.head
  have left : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
  have right : Primrec (fun v : List.Vector Nat 2 => v.tail.head) := Primrec.vector_head.comp Primrec.vector_tail
  have primitive : Primrec f := GorbowRegistryTupleProof.uniformPrograms.1.comp (left.pair right)
  obtain ⟨p,hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 f primitive
  exact ⟨p,fun a b => hp (a ::ᵥ b ::ᵥ List.Vector.nil)⟩

theorem decoding : ∃ p : GorbowPRProgram.Program 1,
    ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (GorbowRegistryDecoder.decodePair n) := by
  have primitive : Primrec (fun n => Encodable.encode (GorbowRegistryDecoder.decodePair n)) :=
    Primrec.encode.comp GorbowRegistryDecoderProof.uniformPrograms.2.1
  exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp primitive
theorem calibratedEncoding (f : Nat → Nat → Nat) (h : ∀ a b, f a b = GorbowRegistryTuple.pair a b) :
    ∃ p : GorbowPRProgram.Program 2, ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = f a b := by
  obtain ⟨p,hp⟩ := encoding
  exact ⟨p, fun a b => (hp a b).trans (h a b).symm⟩

theorem calibratedDecoding (f : Nat → Option (Nat × Nat)) (h : ∀ n, f n = GorbowRegistryDecoder.decodePair n) :
    ∃ p : GorbowPRProgram.Program 1, ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (f n) := by
  obtain ⟨p,hp⟩ := decoding
  exact ⟨p, fun n => (hp n).trans (congrArg Encodable.encode (h n).symm)⟩

theorem literalEncoding : ∃ p : GorbowPRProgram.Program 2, ∀ a b,
    GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = NumberedWindowPairAlgorithm.pair a b :=
  calibratedEncoding _ (fun a b => congrFun (congrFun NumberedWindowRegistryPairCalibration.pair a) b)

theorem literalDecoding : ∃ p : GorbowPRProgram.Program 1, ∀ n,
    GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (NumberedWindowPairAlgorithm.decode n) :=
  calibratedDecoding _ (congrFun NumberedWindowRegistryPairCalibration.decode)

end LogicLineages.PersistentMarking.NumberedWindowRegistryPairPrograms
