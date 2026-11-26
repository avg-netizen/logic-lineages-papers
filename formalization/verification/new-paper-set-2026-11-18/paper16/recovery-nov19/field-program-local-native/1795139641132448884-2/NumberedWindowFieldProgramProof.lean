module

public import LogicLineages.PersistentMarking.NumberedWindowFieldProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowRegistryPairCalibration
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFieldProgramProof
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowFieldAlgorithm
open NumberedWindowFieldProgramTargets

private theorem registryPack (xs : List Nat) : pack xs = GorbowRegistryTuple.tuple xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pack, GorbowRegistryTuple.tuple, NumberedWindowRegistryPairCalibration.pair, ih]

private theorem registryStep : step = GorbowRegistryDecoder.tupleStep := by
  funext s
  cases s with
  | none => rfl
  | some p =>
    obtain ⟨n, acc⟩ := p
    cases n with
    | zero => rfl
    | succ n => simp [step, GorbowRegistryDecoder.tupleStep, NumberedWindowRegistryPairCalibration.decode]

private theorem registrySteps (n : Nat) (s : State) :
    steps n s = GorbowRegistryDecoder.tupleStep^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [steps, Function.iterate_succ_apply, registryStep, ih]

private theorem registryUnpack (n : Nat) : unpack n = GorbowRegistryDecoder.decodeTuple n := by
  simp only [unpack, registrySteps, finish, GorbowRegistryDecoder.decodeTuple]

private theorem primitivePack : Primrec pack :=
  GorbowRegistryTupleProof.uniformPrograms.2.1.of_eq (fun xs => (registryPack xs).symm)

private theorem primitiveUnpack : Primrec unpack :=
  GorbowRegistryDecoderProof.uniformPrograms.2.2.2.1.of_eq (fun n => (registryUnpack n).symm)

private def readList (n : Nat) : List Nat := (Encodable.decode (List Nat) n).getD []

private theorem primitiveReadList : Primrec readList :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem fields : OrderedFieldPrograms := by
  constructor
  · obtain ⟨p, hp⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp
      (primitivePack.comp primitiveReadList)
    exact ⟨p, fun xs => by simpa [readList] using hp (Encodable.encode xs)⟩
  · exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp primitiveUnpack)

private theorem primitiveUnpackSuccessor : Primrec (fun n => unpackNode (n+1)) := by
  have withFields : Primrec (fun p : Nat × (Nat × Nat) => (unpack p.2.2).map (fun xs => (p.2.1, xs))) :=
    Primrec.option_map (primitiveUnpack.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd).to₂
  have pairPrim : Primrec NumberedWindowPairAlgorithm.decode :=
    GorbowRegistryDecoderProof.uniformPrograms.2.1.of_eq (fun n => (congrFun NumberedWindowRegistryPairCalibration.decode n).symm)
  exact (Primrec.option_bind pairPrim withFields.to₂).of_eq (fun n => by
    cases hp : NumberedWindowPairAlgorithm.decode n with
    | none => simp [unpackNode, hp]
    | some p => cases hf : unpack p.2 <;> simp [unpackNode, hp, hf])

theorem nodes : TaggedNodePrograms := by
  constructor
  · let f (v : List.Vector Nat 2) := packNode v.head (readList v.tail.head)
    have tag : Primrec (fun v : List.Vector Nat 2 => v.head) := Primrec.vector_head
    have payload : Primrec (fun v : List.Vector Nat 2 => pack (readList v.tail.head)) :=
      primitivePack.comp (primitiveReadList.comp (Primrec.vector_head.comp Primrec.vector_tail))
    have prim : Primrec f := Primrec.succ.comp (GorbowRegistryTupleProof.uniformPrograms.1.comp (tag.pair payload))
    obtain ⟨p, hp⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 f prim
    exact ⟨p, fun tag xs => by simpa [f, readList] using hp (tag ::ᵥ Encodable.encode xs ::ᵥ List.Vector.nil)⟩
  · have prim : Primrec unpackNode := (Primrec.nat_casesOn₁ none primitiveUnpackSuccessor).of_eq
      (fun n => by cases n <;> rfl)
    exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp (Primrec.encode.comp prim)

end LogicLineages.PersistentMarking.NumberedWindowFieldProgramProof
