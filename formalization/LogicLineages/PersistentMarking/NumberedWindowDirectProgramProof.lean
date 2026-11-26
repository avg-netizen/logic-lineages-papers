module

public import LogicLineages.PersistentMarking.NumberedWindowDirectParsingProof
public import LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectProgramProof
open LogicLineages.ComputabilityKnowledge NumberedWindowDirectAlgorithm NumberedWindowDirectProgramTargets
open NumberedWindowDirectParsingProof NumberedWindowDirectListsPrimrec NumberedWindowFieldAlgorithm List.Vector

private theorem asNat : Primrec Bool.toNat :=
  (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq (fun b => by cases b <;> rfl)

theorem domain : MultisetDomainProgram := by
  intro scalar hs
  have member := (Primrec.option_map₁ (allScalar hs)).comp fieldsPrim
  have bit : Primrec (typedList scalar) :=
    (Primrec.option_getD.comp member (Primrec.const false)).of_eq (fun n => by
      cases hx : unpack n <;> simp [typedList, hx])
  exact (GorbowPRProgram.Proof.unaryCorrespondence _).mp (asNat.comp bit)

theorem checker : DirectCertificateProgram := by
  intro scalar positive hs hp
  let V := List.Vector Nat 3
  have source : Primrec (fun v : V => unpack v.head) := fieldsPrim.comp Primrec.vector_head
  have cert : Primrec (fun v : V => readWitness v.tail.head) :=
    parsing.2.comp (Primrec.vector_head.comp Primrec.vector_tail)
  have target : Primrec (fun v : V => unpack v.tail.tail.head) :=
    fieldsPrim.comp (Primrec.vector_head.comp (Primrec.vector_tail.comp Primrec.vector_tail))
  have complete := Primrec.and.comp (Primrec.and.comp (Primrec.option_isSome.comp source)
    (Primrec.option_isSome.comp cert)) (Primrec.option_isSome.comp target)
  have result := (directListsPrimitive scalar positive hs hp).comp
    ((Primrec.option_getD_default.comp source).pair
      ((Primrec.option_getD_default.comp target).pair (Primrec.option_getD_default.comp cert)))
  have bit : Primrec (fun v : V => direct scalar positive v.head v.tail.head v.tail.tail.head) :=
    (Primrec.cond complete result (Primrec.const false)).of_eq (fun v => by
      cases hx : unpack v.head <;> cases hw : readWitness v.tail.head <;> cases hy : unpack v.tail.tail.head <;>
        simp [direct, hx, hw, hy])
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _ (asNat.comp bit)
  exact ⟨p,fun s c d => eval (s ::ᵥ c ::ᵥ d ::ᵥ List.Vector.nil)⟩

end LogicLineages.PersistentMarking.NumberedWindowDirectProgramProof
